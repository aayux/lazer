from math import log, ceil, sqrt

# Create a header file with proof system parameters for
# proving knowledge of a witness s in Rp^n (Rp = Zp[X]/(X^d + 1))
# such that
#
#   1. s satisfies a linear relation over Rp: As + t = 0
#   2. each element in a partition of s either ..
#      2.1 has binary coefficients only
#      2.2 satisfies an l2-norm bound

vname = "p2_param"                                      # variable name

deg   = 512                                             # ring Rq degree d
mod   = 12289                                           # ring Rq modulus q
tau   = 3                                               # l-inf norm for encryption secrets
m     = 1                                               # dimension of the commited vectors
n     = ceil(m * log(mod, 2))                           # column dimension of L, R
dim   = (m + 2 * n + 11, 4 * n + 22)                    # dimension of A
p = ceil(sqrt(2 * dim[1]) * tau ** 2 * sqrt(2 * dim[1] + 2 * dim[0]) + tau * sqrt(2 * dim[1] + 2 * dim[0]))

wpart = [
            list(range(0, 16)),                             # [ s e1 ]
            list(range(16, 2 * n + 19)),                    # e2
            list(range(2 * n + 19, 4 * n + 19)),            # [ h x ]
            [4 * n + 19, 4 * n + 20], [4 * n + 21]          # [ s1 s2 ], [ r ]
    ]

wl2   = [ tau * sqrt(8 * deg), tau * sqrt((2 * n + 3) * deg), 0, sqrt(34034726), 0]    # l2-norm bounds
#wl2   = [ 0, 0, 0, 0, 0]    # l2-norm bounds
wbin  = [ 0, 0, 1, 0, 1 ]                                  # binary coeffs
#wrej  = [0, 0, 0, 1]                                   # rejection sampling: on r only

# Optional: some linf-norm bound on w.
# Tighter bounds result in smaller proofs.
# If not specified, the default is the naive bound max(1,floor(max(wl2))).
# wlinf = 5833  # optional linf: some linf-norm bound on w.
