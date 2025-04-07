import sys
sys.path.append('..')
import hashlib
import secrets
from lazer import *

from typing import Tuple

# Public randomness setup
shake128 = hashlib.shake_128(bytes.fromhex("00"))
COMPP = shake128.digest(32)
shake128 = hashlib.shake_128(bytes.fromhex("01"))
SIGPP = shake128.digest(32)
shake128 = hashlib.shake_128(bytes.fromhex("02"))
PFPP = shake128.digest(32)

from _pesto_params_cffi import lib
from pesto_params import deg, mod, m, n

# Constants
d, q = deg, mod
Rq = polyring_t(d, q)

# Commitment matrices
L = polymat_t(Rq, m, n)
L.urandom(q, COMPP, 0)
R = polymat_t(Rq, m, n)
R.urandom(q, COMPP, 1)

# The signature proof matrix (initialised partially)
A = polymat_t(Rq, m, 2 * n + 3)
A.set_submatrix(0, 0, L)
A.set_submatrix(0, n, R)
one = poly_t(Rq, {0 : 1})
A.set_elem(-one, 0, 2 * n + 1)

# The public vector t_COM such that A_SIG * w_SIG + t_SIG = 0
t = polyvec_t(Rq, m)

class User:
    def __init__(self):
        self.h = polyvec_t(Rq, n)
        self.x = polyvec_t(Rq, n)
        # Initialize h and x with binary coefficients
        self.h.urandom_bnd(0, 1, COMPP, 0)
        self.x.urandom_bnd(0, 1, COMPP, 1)
    
    def commit(self) -> bytes:
        # Compute commitment c = L*h + R*x
        self.c = L * self.h + R * self.x
        
        # Encode commitment
        coder = coder_t()
        coder.enc_begin(22000)
        coder.enc_urandom(mod, self.c)
        return coder.enc_end()
    
    def unblind(self, vk: Tuple[poly_t, falcon_pkenc], sig_bytes: bytes) -> bytes:
        rho, s1, s2 = bytes(64), poly_t(Rq), poly_t(Rq)
        
        # Decode signature
        coder = coder_t()
        coder.dec_begin(sig_bytes)
        coder.dec_bytes(rho)
        coder.dec_grandom(165, s1)
        coder.dec_grandom(165, s2)
        coder.dec_end()
        
        r = poly_t(Rq, rho)
        b, a = vk[0], falcon_decode_pk(vk[1])

        prover = lin_prover_state_t(PFPP, lib.get_params("param"))
        A.set_elem(-b, 0, 2 * n)
        A.set_elem(-a, 0, 2 * n + 2)
        w = polyvec_t(Rq, 2 * n + 3, [self.h, self.x, r, s1, s2])

        print(f"{"Passed" if A * w + t == polyvec_t(Rq, m) else "Failed"} sanity check")

        prover.set_statement(A, t)
        prover.set_witness(w)
        π = prover.prove()

        return π

class Issuer:
    def __init__(self):
        # Generate FALCON keypair
        self.sk, vk, _ = falcon_keygen()
        
        # ROM-ISIS polynomial
        b = poly_t(Rq)
        b.urandom_bnd(-int((q-1)/2), int((q-1)/2), SIGPP, 0)
        self.vk = (b, vk)
    
    def get_vk(self) -> Tuple[poly_t, falcon_pkenc]:
        return self.vk
    
    def sign(self, c_bytes: bytes) -> bytes:
        # Decode commitment
        c = polyvec_t(Rq, m)
        coder = coder_t()
        coder.dec_begin(c_bytes)
        coder.dec_urandom(mod, c)
        coder.dec_end()
        
        # Generate signature
        rho = secrets.token_bytes(64)
        r = poly_t(Rq, rho)
        s1, s2 = falcon_preimage_sample(self.sk, c - self.vk[0] * r)
        
        # Encode signature
        coder = coder_t()
        coder.enc_begin(2000)
        coder.enc_bytes(rho)
        coder.enc_grandom(165, s1)
        coder.enc_grandom(165, s2)
        return coder.enc_end()

class Verifier:
    def verify(self, π: bytes, vk: Tuple[poly_t, falcon_pkenc]) -> bool:
        # Extract verification key components
        b, a = vk[0], falcon_decode_pk(vk[1])
        
        # Set up the proof matrix with verification key
        A.set_elem(-b, 0, 2 * n)
        A.set_elem(-a, 0, 2 * n + 2)
        
        # Create verifier instance
        verifier = lin_verifier_state_t(PFPP, lib.get_params("param"))
        verifier.set_statement(A, t)
        
        # Verify the proof
        try:
            verifier.verify(π)
        except VerificationError:
            return False
        return True

def main():
    # Setup
    user = User()
    issuer = Issuer()
    verifier = Verifier()
    
    # Create a hiding commitment
    print("Creating commitment ...")
    com = user.commit()
    
    # Sign the commitment
    print("Signing commitment ...")
    sig = issuer.sign(com)
    
    # Generate the proof
    print("Generating proof ...")
    π = user.unblind(issuer.get_vk(), sig)

    print(f"Size: {len(π) / 1024} KB")

    # Verify the proof
    print("Verifying proof ...")
    if verifier.verify(π, issuer.get_vk()):
        print("Verification successful!")
    else:
        print("Verification failed!")

if __name__ == "__main__":
    main()
