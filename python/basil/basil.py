import gc
import sys
sys.path.append('..')       # path to lazer module
import time
import hashlib              # for SHAKE128
import secrets              # for internal coins
from lazer import *         # import lazer python module
from merkletree import *    # import tree node module
from math import log, ceil
from typing import List

from _basil_params_cffi import lib
from basil_p1_params import deg, mod, tau, B, m, n, alpha
from basil_p1_params import p as p_COM
from basil_p2_params import p as p_SIG

# constants
d, q = deg, mod
Rq = polyring_t(d, q)
lgB = ceil(log(B, alpha))

# the binary recomposition gadget matrix
G = makeGmat(Rq, m, n)

zero = polyvec_t(Rq, m)
one = poly_t(Rq, {0: 1})

# ==============================================================================
# CRS generation
# ==============================================================================

def pke_keygen(ENCPP: bytes, E1: polymat_t = None) -> Tuple[polymat_t, polymat_t]:
    """
    Generate the public and secret keys for the encryption scheme.
    """

    phase = 0

    if E1 == None:
        E1 = polymat_t(Rq, 8, 8)
        E1.urandom(q, ENCPP, 3 * phase + 0)
        nrows = 3 * n
    else: 
        phase = 1
        nrows = 2 * n + 3

    S1 = polymat_t(Rq, nrows, 8)
    S1.urandom(tau, ENCPP, 3 * phase + 1)

    S2 = polymat_t(Rq, nrows, 8)
    S2.urandom(tau, ENCPP, 3 * phase + 2)
    E2 = S1 * E1 + 1 * S2

    # del S1, S2

    return (E1, E2)

# ==============================================================================
# The client class
# ==============================================================================

class Client:
    """
    Class representing the client in the Basil protocol.
    """

    def __init__(
            self, µ: List[polyvec_t], COMPP: bytes, PF1PP: bytes, ENCPP: bytes, 
            PF2PP: bytes, E1: polymat_t, E2_COM: polymat_t, 
            E2_SIG: polymat_t, L: polymat_t, R: polymat_t
        ):
        """
        Initialize the client with a batch of messages.
        
        Args:
            µ (List[polyvec_t]): Batch of messages to commit to.
            L (polymat_t): The left matrix of the Merkle tree.
            R (polymat_t): The right matrix of the Merkle tree.
        """
        
        self.COMPP = COMPP
        self.PF1PP = PF1PP
        self.ENCPP = ENCPP
        self.PF2PP = PF2PP

        self.µ = µ
        self.T = MerkleTree(self.COMPP, L, R)
        self.E1 = E1
        self.E2_COM = E2_COM
        self.E2_SIG = E2_SIG

        self.p2_prover = lin_prover_state_t(self.PF2PP, lib.get_params("p2_param"))
        self.p2_verifier = lin_verifier_state_t(self.PF2PP, lib.get_params("p2_param"))

    def blind(self, precompute: bool = False) -> bytes:
        """
        Commit to a batch of messages using the Ajtai-Merkle tree.

        Args:
            precompute (bool): Whether to precompute the opening proofs.
        Returns:
            bytes: The commitment to the batch as raw bytes.
        """
        # create the Merkle tree commitment
        print(f"Building the commitment tree for {B} leaves ...")
        start_time = time.time()
        self.__h = self.T.commit(self.µ)
        tree_time = time.time() - start_time
        print(f"[OK] completed in: {tree_time:.3f} s")

        # Ajtai commitment to the Merkle tree root
        self.__x = polyvec_t(Rq, n)
        self.__x.urandom_bnd(0, 1, self.COMPP, 2 + B)
        self.c = self.T.L * self.__h + self.T.R * self.__x
        com_time = time.time() - start_time
        print(f"[OK] completed in: +{com_time - tree_time:.3f} s")

        # encode the commitment
        print("Encoding commitment to raw bytestream ...")
        coder = coder_t()
        print(f"selfc_dimension:", self.c.dim)
        coder.enc_begin(22000)
        coder.enc_urandom(mod, self.c)
        c_bytes = coder.enc_end()
        print(f"[OK] Commitment size: {len(c_bytes) / 1024: .3f} KB")

        # precompute the opening proof (for the first message)
        # NOTE: in general, all proofs can be precomputed, but we only show the first one
        if precompute: self._precomute_opening_proofs(0)

        return c_bytes

    def _precomute_opening_proofs(self, idx: int = None):
        """
        Precompute the opening proofs for the batch of messages.

        Args:
            idx (int, optional): The index of the message to prove opening of.
                If None, proofs for all messages are precomputed.
        """
        self.π_COM = [[] for _ in range(B)]
        self.ct_COM = [[] for _ in range(B)]
        
        print('\n-------------[ Unblind (offline) ]-------------')

        if idx is not None:
            if idx < 0 or idx >= B:
                raise ValueError("Index out of bounds.")
            self.__precompute_opening_proof_idx(idx)
        else:
            raise NotImplementedError("Precomputation for all messages not implemented.")

    def __encrypt(
                    self, _E2: polymat_t, µ_ENC: polyvec_t
            ) -> Tuple[polyvec_t, polyvec_t, polyvec_t, polyvec_t, polyvec_t]:
        """
        Encrypt a message vector using a variant of Regev's encryption scheme.

        Args:
            _E2 (polymat_t): Derived public key matrix.
            µ_ENC (polyvec_t): The message vector to encrypt

        Returns:
            Tuple containing:
                s (polyvec_t): Random vector sampled from [-tau, tau]
                e1 (polyvec_t): Error vector for first ciphertext component
                e2 (polyvec_t): Error vector for second ciphertext component  
                c1 (polyvec_t): First ciphertext component
                c2 (polyvec_t): Second ciphertext component

        Raises:
            ValueError: If phase is not 0 or 1
        """
        nrows = _E2.rows
        phase = 0 if nrows == 3 * n else 1
        p = p_COM if nrows == 3 * n else p_SIG

        s = polyvec_t(Rq, 8)
        s.urandom_bnd(0, tau, self.ENCPP, 3 * phase + 5)
        
        e1 = polyvec_t(Rq, 8)
        e1.urandom_bnd(0, tau, self.ENCPP, 3 * phase + 6)
        
        e2 = polyvec_t(Rq, nrows)
        e2.urandom_bnd(0, tau, self.ENCPP, 3 * phase + 7)
        
        c1 = self.E1 * s + e1 * 1
        c2 = _E2 * s + e2 + p * µ_ENC

        return (s, e1, e2, c1, c2)

    def __precompute_opening_proof_idx(self, idx: int) -> None:
        """
        Precompute the opening proof for the i-th message.

        Args:
            idx (int): The index of the message to prove opening of.
        """
        # get the opening proof
        print(f"Precomputing opening proof for leaf {idx} ...")
        start_time = time.time()
        op = self.T.lin_open(idx)
        proof_time = time.time() - start_time
        print(f"[OK] completed in: {proof_time:.3f} s")

        # compute the public instance matrix
        A_COM = [polymat_t(Rq, m + 3 * n + 8, 16 + 6 * n) for _ in range(2)]

        # | A1    In    ---- 0 ---- | | s  |
        # | A2    0    Im    p * Im | | e1 |    | c1 |
        # | ----- 0 -----    L R -G | | e2 | +  | c2 | = 0
        #                             | h1 |    | 0  |
        #                             | h2 |
        #                             | h3 |

        # the identity matrices
        Im_COM = polymat_t.identity(Rq, 3 * n)     # m_COM = 3 * n
        In_COM = polymat_t.identity(Rq, 8)         # n_COM = 8
        pIm_COM = p_COM * Im_COM

        # configure both commitment matrices as slices of A[pos]
        for pos in range(2):
            A_COM[pos].set_submatrix(0, 0, self.E1)
            A_COM[pos].set_submatrix(0, 8, In_COM)
            A_COM[pos].set_submatrix(8, 0, self.E2_COM)
            A_COM[pos].set_submatrix(8, 16, Im_COM)
            A_COM[pos].set_submatrix(8, 3 * n + 16, pIm_COM)
            A_COM[pos].set_submatrix(3 * n + 8, 3 * n + 16, self.T.L if pos == 0 else self.T.R)
            A_COM[pos].set_submatrix(3 * n + 8, 4 * n + 16, self.T.R if pos == 0 else self.T.L)
            A_COM[pos].set_submatrix(3 * n + 8, 5 * n + 16, -G)
        

        print(f"Generating ZK proof of opening for leaf {idx}...")

        proof_time = 0.
        for i in range(len(op) - 1):
            h1, h2, pos = op[i]
            h3 = op[i + 1][0]
            
            # create witness vector
            partial_w = polyvec_t(Rq, 3 * n, [h1, h2, h3])
            s, e1, e2, c1, c2 = self.__encrypt(self.E2_COM, partial_w)

            w = polyvec_t(Rq, 16 + 6 * n, [s, e1, e2, h1, h2, h3])

            zero = polyvec_t(Rq, m)
            t_COM = polyvec_t(Rq, m + 3 * n + 8, [-c1, -c2, zero])

            # test = A_COM[pos] * w + t_COM
            # print(test.print())

            # create new prover instance
            p1_prover = lin_prover_state_t(self.PF1PP, lib.get_params("p1_param"))

            try:
                # set statement and witness
                
                p1_prover.set_statement(A_COM[pos], t_COM)
                p1_prover.set_witness(w)

                # generate proof
                
                start_time = time.time()
                _π = p1_prover.prove()
                proof_time += time.time() - start_time
                self.π_COM[idx].append(_π)
                print(f"[OK] completed proof {i + 1} of {len(op) - 1} | time elapsed : {proof_time:.3f} s | size: {len(_π) / 1024:.3f} KB")

                # verify proof
                p1_verifier = lin_verifier_state_t(self.PF1PP, lib.get_params("p1_param"))
                p1_verifier.set_statement(A_COM[pos], t_COM)
                start_time = time.time()
                p1_verifier.verify(_π)
                verify_time = time.time() - start_time
                print(f"[OK] completed verification {i + 1} of {len(op) - 1} | time elapsed: {verify_time:.3f} s")
                del p1_verifier  # explicitly free verifier
                
                # encode ciphertexts to raw bytes
                print("Encoding ciphertexts to raw bytestream ...")
                

                print(f"c2dimension:", c2.dim)
                print(f"c1dimension:", c1.dim)
                
                coder = coder_t()
                coder.enc_begin(22000)
                coder.enc_urandom(mod, c1)
                #coder.enc_urandom(mod, c2)
                ct_bytes = coder.enc_end()
                self.ct_COM[idx].append(ct_bytes)
                print(f"[OK] Ciphertext size: {(len(ct_bytes) / 1024):.3f} KB")
                print(f"[OK] Ciphertext size estimate: {((len(ct_bytes) / 1024)/8 * 50):.3f} KB")
                
            finally:
                del p1_prover  # explicitly free prover
                gc.collect()
    
    def unblind(self, vk: Tuple[poly_t, falcon_pkenc], z_bytes: bytes, idx: int) -> List[bytes]:
        """
        Obtain the blind signature on the i-th message.

        Args:
            vk (Tuple[poly_t, falcon_pkenc]): The public verification key of the issuer.
            z_bytes (bytes): The signature on the batch commitment.
            idx (int): The index of the message to obtain the signature on.

        Returns:
            List[bytes]: The ciphertexts and proofs for commitment and signature.
        """
        rho, s1, s2 = bytes(64), poly_t(Rq), poly_t(Rq)
        
        # decode the signature
        print("Decoding signature from raw bytestream ...")
        try:
            coder = coder_t()
            coder.dec_begin(z_bytes)
            coder.dec_bytes(rho)
            coder.dec_grandom(165, s1)
            coder.dec_grandom(165, s2)
            coder.dec_end()
        except DecodingError:
            raise ValueError("[ERR] decoder failed")

        print("[OK] decoded successfully")

        r = poly_t(Rq, rho)

        # # extract the issuer's verification key
        b, a = vk[0], falcon_decode_pk(vk[1])

        # | A1    In    ------- 0 ------- | | s  |
        # | A2      0      Im      p * Im | | e1 |    | c1 |
        # | ----- 0 -----    L R -1 -A -B | | e2 | +  | c2 | = 0
        #                                   | h  |    | 0  |
        #                                   | x  |
        #                                   | s1 |
        #                                   | s2 |
        #                                   | r  |

        # create the public instance matrix
        # this can be pre-computed once and for all, so not counted in runtime
        # the signature proof matrix (initialised partially)
        A_SIG = polymat_t(Rq, m + 2 * n + 11, 22 + 4 * n)
        
        # the identity matrices
        Im_SIG = polymat_t.identity(Rq, 2 * n + 3)      # m_SIG = 2 * n + 3
        In_SIG = polymat_t.identity(Rq, 8)              # n_SIG = 8
        pIm_SIG = p_SIG * Im_SIG

        # define the submatrices as slices of A
        A_SIG.set_submatrix(0, 0, self.E1)
        A_SIG.set_submatrix(0, 8, In_SIG)
        A_SIG.set_submatrix(8, 0, self.E2_SIG)
        A_SIG.set_submatrix(8, 16, Im_SIG)
        A_SIG.set_submatrix(8, 2 * n + 19, pIm_SIG)
        A_SIG.set_submatrix(2 * n + 11, 2 * n + 19, self.T.L)
        A_SIG.set_submatrix(2 * n + 11, 3 * n + 19, self.T.R)
        A_SIG.set_elem(-one, 2 * n + 11, 4 * n + 19)
        
        print(f"Generating ZK proof of valid signature on commitment ...")

        start_time = time.time()

        # set the rest of the A matrix
        # A_SIG.set_submatrix(0, 2 * n, -a)

        A_SIG.set_elem(-a, 2 * n + 11, 4 * n + 20)
        A_SIG.set_elem(-b, 2 * n + 11, 4 * n + 21)

        # create witness vector
        partial_w = polyvec_t(Rq, 2 * n + 3, [self.__h, self.__x, s1, s2, r])
        s, e1, e2, c1, c2 = self.__encrypt(self.E2_SIG, partial_w)
        self.c1_SIG, self.c2_SIG = c1, c2

        w = polyvec_t(Rq, 4 * n + 22, [s, e1, e2, self.__h, self.__x, s1, s2, r])
        
        # create the target vector
        zero = polyvec_t(Rq, m)
        t_SIG = polyvec_t(Rq, m + 2 * n + 11, [-c1, -c2, zero])

        print(f"t_SIG dimension: {t_SIG.dim}")
        print(f"A_SIG dimension: {A_SIG.rows}, {A_SIG.cols}")
        print(f"w dimension: {w.dim}")



        test = A_SIG * w + t_SIG
        #print(test.print()) # this should output a vector of zero polynomials

        self.p2_prover.set_statement(A_SIG, t_SIG)
        self.p2_prover.set_witness(w)

        self.π_SIG = self.p2_prover.prove()
        proof_time = time.time() - start_time
        print(f"[OK] completed in: {proof_time:.3f} s | size: {len(self.π_SIG) / 1024:.3f} KB")

        self.p2_verifier.set_statement(A_SIG, t_SIG)
        self.p2_verifier.verify(self.π_SIG)


        # encode ciphertexts to raw bytes
        
        print("Encoding ciphertexts to raw bytestream ...")
        '''
        coder = coder_t()
        coder.enc_begin(22000)
        coder.enc_urandom(mod, c1)
        coder.enc_urandom(mod, c2)
        ct_bytes = coder.enc_end()
        self.ct_SIG = ct_bytes
        print(f"[OK] Ciphertext size: {len(ct_bytes) / 1024} KB")
        '''
        

        return (self.ct_COM[idx], self.π_COM[idx], self.ct_SIG, self.π_SIG)

# ==============================================================================
# The issuer class
# ==============================================================================

class Issuer:
    """
    Class representing the issuer in the Basil protocol.
    """

    def __init__(self, SIGPP: bytes):
        """
        """
        self.SIGPP = SIGPP

        # instantiate the FALCON key pair
        self.sk, vk, _ = falcon_keygen()

        # the rOM-ISIS polynomial
        b = poly_t(Rq)
        b.urandom_bnd(-int((q-1)/2), int((q-1)/2), self.SIGPP, 0)

        self.vk = (b, vk)

    
    def get_falcon_vk(self) -> Tuple[poly_t, falcon_pkenc]:
        """
        Returns:
            falcon_pkenc: The public verification key of the issuer.
        """
        return self.vk
    
    def issue(self, c_bytes: bytes) -> bytes:
        """
        Issue a signature for the given commitment.

        Args:
            c (bytes): The commitment to sign with FALCON.

        Returns:
            bytes: The FALCON signature on the client's commitment.
        """
        
        c = polyvec_t(Rq, m)

        # decode the commitment
        print("Decoding commitment from raw bytestream ...")
        try:
            coder = coder_t()
            coder.dec_begin(c_bytes)
            coder.dec_urandom(mod, c)
            coder.dec_end()
        except DecodingError:
            raise ValueError("[ERR] decoder failed")
        
        print("[OK] decoded successfully")

        # internal coins
        rho = secrets.token_bytes(64)

        # sign the commitment
        print("Signing the commitment ...")
        start_time = time.time()
        r = poly_t(Rq, rho) # the rOM-ISIS randomness
        s1, s2 = falcon_preimage_sample(self.sk, c - self.vk[0] * r)
        sign_time = time.time() - start_time
        print(f"[OK] completed in: {sign_time * 1000:.3f} ms")

        # encode rho, s1, s2
        print("Encoding signature to raw bytestream ...")
        coder = coder_t()
        coder.enc_begin(2000)
        coder.enc_bytes(rho)
        coder.enc_grandom(165, s1)
        coder.enc_grandom(165, s2)
        self.z_bytes = coder.enc_end()
        print(f"[OK] Pre-signature size: {len(self.z_bytes) / 1024: .3f} KB")
        
        return self.z_bytes

# ==============================================================================
# The verifier class
# ==============================================================================

class Verifier:
    """
    Class representing the verifier in the Basil protocol.
    """
    
    def __init__(self, COMPP: bytes, PF2PP: bytes, vk: Tuple[poly_t, falcon_pkenc], 
                 L: polymat_t, R: polymat_t, E1: polymat_t, E2_COM: polymat_t, 
                 E2_SIG: polymat_t
            ):
        """
        Initialize the verifier with the proof parameters and public keys.
        
        Args:
            COMPP (bytes): Commitment parameters
            PF2PP (bytes): Second proof system parameters
            vk (Tuple[poly_t, falcon_pkenc]): Issuer's verification key
            L (polymat_t): Left matrix for Merkle tree
            R (polymat_t): Right matrix for Merkle tree
            E1 (polymat_t): First encryption matrix
            E2_COM (polymat_t): Second encryption matrix for commitment
            E2_SIG (polymat_t): Second encryption matrix for signature
        """
        self.p2_verifier = lin_verifier_state_t(PF2PP, lib.get_params("p2_param"))
        
        self.vk = vk
        self.L = L
        self.R = R
        self.E1 = E1
        self.E2_COM = E2_COM
        self.E2_SIG = E2_SIG
        
    def verify(self, µ: polyvec_t, ct_COM: List[bytes], π_COM: List[bytes], 
               ct_SIG: bytes, π_SIG: bytes) -> bool:
        """
        Verify the commitment proof and signature proof.

        Args:
            µ (polyvec_t): The message to verify 
            ct_COM (List[bytes]): The ciphertexts for commitment proofs
            π_COM (List[bytes]): The commitment opening proofs
            ct_SIG (bytes): The ciphertext for signature proof
            π_SIG (bytes): The signature proof

        Returns:
            bool: True if both proofs verify, False otherwise
        """
        # verify commitment proofs
        print("Verifying commitment proofs ...")
        verify_time = 0.0
        
        # setup commitment verification matrices
        A_COM = [polymat_t(Rq, m + 3 * n + 8, 16 + 6 * n) for _ in range(2)]
        Im_COM = polymat_t.identity(Rq, 3 * n)
        In_COM = polymat_t.identity(Rq, 8)
        pIm_COM = p_COM * Im_COM
        
        # configure both commitment matrices
        for pos in range(2):
            A_COM[pos].set_submatrix(0, 0, self.E1)
            A_COM[pos].set_submatrix(0, 8, In_COM)
            A_COM[pos].set_submatrix(8, 0, self.E2_COM)
            A_COM[pos].set_submatrix(8, 16, Im_COM)
            A_COM[pos].set_submatrix(8, 3 * n + 16, pIm_COM)
            A_COM[pos].set_submatrix(3 * n + 8, 3 * n + 16, self.L if pos == 0 else self.R)
            A_COM[pos].set_submatrix(3 * n + 8, 4 * n + 16, self.R if pos == 0 else self.L)
            A_COM[pos].set_submatrix(3 * n + 8, 5 * n + 16, -G)
        
        # verify each commitment proof
        for i, (ct, proof) in enumerate(zip(ct_COM, π_COM)):
            self.p1_verifier = lin_verifier_state_t(self.PF1PP, lib.get_params("p1_param"))
            # decode ciphertext
            c1, c2 = polyvec_t(Rq, 8), polyvec_t(Rq, 3 * n)
            try:
                coder = coder_t()
                coder.dec_begin(ct)
                coder.dec_urandom(mod, c1)
                coder.dec_urandom(mod, c2)
                coder.dec_end()
            except DecodingError:
                print(f"[ERR] commitment ciphertext {i + 1} decoding failed")
                return False
            start_time = time.time()
            try:
                # construct target vector using decoded ciphertext
                t_COM = polyvec_t(Rq, m + 3 * n + 8, [-c1, -c2, zero])

                self.p1_verifier.set_statement(A_COM[i % 2], t_COM)
                self.p1_verifier.verify(proof)
            except VerificationError:
                print(f"[ERR] commitment proof {i + 1} verification failed")
                return False
            verify_time += time.time() - start_time
            print(f"[OK] completed verification {i + 1} of {len(π_COM)} | time elapsed: {verify_time:.3f} s")
            
        # setup signature verification matrix
        A_SIG = polymat_t(Rq, m + 2 * n + 11, 22 + 4 * n)
        Im_SIG = polymat_t.identity(Rq, 2 * n + 3)
        In_SIG = polymat_t.identity(Rq, 8)
        pIm_SIG = p_SIG * Im_SIG
        
        # configure signature matrix
        A_SIG.set_submatrix(0, 0, self.E1)
        A_SIG.set_submatrix(0, 8, In_SIG)
        A_SIG.set_submatrix(8, 0, self.E2_SIG)
        A_SIG.set_submatrix(8, 16, Im_SIG)
        A_SIG.set_submatrix(8, 2 * n + 19, pIm_SIG)
        A_SIG.set_submatrix(2 * n + 11, 2 * n + 19, self.L)
        A_SIG.set_submatrix(2 * n + 11, 3 * n + 19, self.R)
        A_SIG.set_elem(-one, 2 * n + 11, 3 * n + 20)
        
        # Set FALCON verification key elements
        b, a = self.vk[0], falcon_decode_pk(self.vk[1])
        A_SIG.set_elem(-a, 2 * n + 11, 3 * n + 21)
        A_SIG.set_elem(-b, 2 * n + 11, 3 * n + 22)
        
        # decode signature ciphertext
        c1_SIG, c2_SIG = polyvec_t(Rq, 8), polyvec_t(Rq, 2 * n + 3)
        try:
            coder = coder_t()
            coder.dec_begin(ct_SIG)
            coder.dec_urandom(mod, c1_SIG)
            coder.dec_urandom(mod, c2_SIG)
            coder.dec_end()
        except DecodingError:
            print("[ERR] signature ciphertext decoding failed")
            return False

        # Verify signature proof with decoded ciphertext
        print("Verifying signature proof ...")
        start_time = time.time()
        try:
            zero = polyvec_t(Rq, m)
            t_SIG = polyvec_t(Rq, m + 2 * n + 11, [-c1_SIG, -c2_SIG, zero])
            self.p2_verifier.set_statement(A_SIG, t_SIG)
            self.p2_verifier.verify(π_SIG)
        except VerificationError:
            print("[ERR] signature proof verification failed")
            return False
        verify_time = time.time() - start_time
        print(f"[OK] completed in: {verify_time:.3f} s")
        
        return True

# ==============================================================================
# Driver code
# ==============================================================================

def main():

    # public randomness
    shake128 = hashlib.shake_128(bytes.fromhex("00"))
    COMPP = shake128.digest(32)
    shake128 = hashlib.shake_128(bytes.fromhex("01"))
    PF1PP = shake128.digest(32)
    shake128 = hashlib.shake_128(bytes.fromhex("02"))
    SIGPP = shake128.digest(32)
    shake128 = hashlib.shake_128(bytes.fromhex("03"))
    ENCPP = shake128.digest(32)
    shake128 = hashlib.shake_128(bytes.fromhex("04"))
    PF2PP = shake128.digest(32)

    E1, E2_COM = pke_keygen(ENCPP)
    _, E2_SIG = pke_keygen(ENCPP, E1)

    # the commitment matrices
    L = polymat_t(Rq, m, n)
    L.urandom(q, COMPP, 0)

    R = polymat_t(Rq, m, n)
    R.urandom(q, COMPP, 1)

    # create the batch of messages
    µ = [ polyvec_t(Rq, n) for _ in range(B) ]
    for i in range(B):
        µ[i].urandom_bnd(0, 1, COMPP, 2 + i) # <-- may need to use bytes here
    
    # create the client
    cli = Client(µ, COMPP, PF1PP, ENCPP, PF2PP, E1, E2_COM, E2_SIG, L, R)

    # create the issuer and get the FALCON verification key
    iss = Issuer(SIGPP)
    iss_vk = iss.get_falcon_vk()
    
    print('\n-------------------[ Blind ]-------------------')

    # create the client query
    cli_COM = cli.blind(precompute=True)

    print('\n-------------------[ BSign ]-------------------')

    # issue the signature
    iss_sig = iss.issue(cli_COM)

    print('\n--------------[ Unblind (online) ]--------------')

    # obtain the final message and signature pair for the first message
    ct_COM, π_COM, ct_SIG, π_SIG = cli.unblind(iss_vk, iss_sig, 0)

    # create verifier
    ver = Verifier(COMPP, PF2PP, iss_vk, L, R, E1, E2_COM, E2_SIG)
    
    print('\n--------------[ Verify ]--------------')

    # verify proofs including ciphertexts
    if ver.verify(µ[0], PF1PP, ct_COM, π_COM, ct_SIG, π_SIG):
        print("[OK] Verification successful!")
    else:
        print("[ERR] Verification failed")

if __name__ == "__main__":
    main()
