import sys

####################################################
d = 64  # degree of proof system ring in {64,128}
PSI = 3358  # range proof slack XXX depends on alpha4, Bprime ...
# XXX tighter bounds for q, Bprime...
####################################################

assert len(sys.argv) == 2
params_file = sys.argv[1]

load(params_file)

assert vname != ""
name = f"_{vname}"  # name passed to lnp-tbox-codegen.sage

assert 2 ** int(log(deg, 2)) == deg  # ring degree must be a power of 2
assert deg >= d                 # ring degree must be bigger than d

assert len(dim) == 2
nrows = dim[0]
assert nrows > 0
ncols = dim[1]
assert ncols > 0

wdim = max(max(wpart)) + 1  # dimension of witness vector
assert wdim == ncols

wnsub = len(wpart)      # number of elements in the partition of w
assert wnsub > 0

assert len(wl2) == wnsub
assert len(wbin) == wnsub
# assert len(wrej) == wnsub # XXX

# check l2 norms are positive
for i in wl2:
    assert i >= 0

# check wbin and wrej are lists of booleans
for i in wbin:
    assert i == 0 or i == 1
# for i in wrej:
#    assert i == 0 or i == 1

# check that w is a partition of a wdim-dimensional vector
w_ = [0 for i in range(wdim)]
for i in wpart:
    for j in i:
        w_[j] += 1
for i in w_:
    assert w_[i] == 1

# check that each subvector is either bounded in l2 or binary
for i in range(wnsub):
    assert (wl2[i] > 0 and wbin[i] == 0) or (wl2[i] == 0 and wbin[i] == 1)

if 'wlinf' in globals():
    assert wlinf >= 1
else:
    wlinf = max(1, max(wl2))

k = deg/d
P = (mod-1)/2
# t = As+e
S = wlinf  # bound on linf(s)
E = 0   # bound on linf(e), n/a here

# not affected by k since dimension m is multiplied by k
# but degree d is divided by k
# set ring modulus q's bit-size
log2q = ceil(log((2 * (1+PSI)*(P + ncols*P*deg*S + E) + 1), 2))
# log2q1 = 0            # if q = q1*q2, also set q1's bit-size

# find dimension of binary vector
nbin_ = 0
for i in range(wnsub):
    if wbin[i] == 1:
        nbin_ += len(wpart[i])
nbin = k * nbin_       # set length of vector with binary coefficients

# find dimensions of vectors bounded in l2 norm
n_ = []
B_ = []
for i in range(wnsub):
    if wl2[i] > 0:
        n_ += [len(wpart[i])]
        B_ += [wl2[i]]
n = [i * k for i in n_]
B = B_.copy()

# find dimension of vector bounded in linf norm
nprime = k * nrows
Bprime = (P+ncols*P*deg*S+E)/mod     # set linf norm bound


# copy l2 bound list and insert naive l2 norm bounds for binary vectors
wl2_ = wl2.copy()
for i in range(wnsub):
    if wl2_[i] == 0:
        wl2_[i] = sqrt((1 ** 2) * deg * len(wpart[i]))


# Search for smallest proof size:
# Modified to keep l2-norm bounded elements in Ajtai part
ajtai = [i for i in range(wnsub)]  # list of subvectors in Ajtai part
bdlop = []  # list of subvectors in BDLOP part
m1 = k*wdim     # set length of vector s1 (committed in Ajtai part)
l = k*0         # set length of vector m (committed in BDLOP part)
# set l2-norm bound on vector s1
alpha = ceil(sqrt(sum(wl2_[i] ** 2 for i in ajtai)))

verbose = 1
code = 1
loaded = 1
codegen_err = 0
load("lnp-tbox-codegen.sage")
assert codegen_err == 0

# indices of elements of w that go to s1
s1_indices = []
Ps_indices = []
Es_indices = []
for i in ajtai:
    if wbin[i] == 1:
        Ps_indices += list(range(len(s1_indices),
                               len(s1_indices)+len(wpart[i])))
    if wl2[i] > 0:  # Keep l2-norm bounded elements in Ajtai part
        Es_indices += [list(range(len(s1_indices),
                              len(s1_indices)+len(wpart[i])))]
    s1_indices += wpart[i]

# indices of elements of w that go to m
m_indices = []
Em_indices = []  # This will remain empty since all l2-norm bounds are in Ajtai
for i in bdlop:
    assert wbin[i] == 0  # can't put binary subvecs in BDLOP
    m_indices += wpart[i]

# to lower ring deg
tmp = []
for i in Ps_indices:
    tmp += list(range(i*k, i*k+k))
Ps_indices = tmp
Ps_indices.sort()

tmp2 = []
for j in Es_indices:
    tmp3 = []
    for i in j:
        tmp3 += list(range(i*k, i*k+k))
    tmp2 += [tmp3]
Es_indices = tmp2
Es_indices.sort()

out = ""

if Ps_indices == []:
    matPs_nrows = 0
    vname_Ps = f"NULL"
else:
    out += f"static const unsigned int {vname}_Ps[{len(Ps_indices)}] = {intlist2intarray(Ps_indices)};\n"
    matPs_nrows = len(Ps_indices)
    vname_Ps = f"{vname}_Ps"

vname_Es = []
for i in range(len(Es_indices)):
    _Es_indices = Es_indices[i]
    if _Es_indices == []:
        vname_Es += [f"NULL"]
    else:
        out += f"static const unsigned int {vname}_Es{i}[{len(_Es_indices)}] = {intlist2intarray(_Es_indices)};\n"
        vname_Es += [f"{vname}_Es{i}"]
if Es_indices == []:
    strEs = "NULL"
    strEs_nrows = "NULL"
else:
    strEs = f"{vname}_Es"
    strEs_nrows = f"{vname}_Es_nrows"
    out += f"static const unsigned int *{vname}_Es[{len(Es_indices)}] = {{ "
    for i in range(len(Es_indices)):
        out += f"{vname_Es[i]}, "
    out += f"}};\n"
    out += f"static const unsigned int {vname}_Es_nrows[{len(Es_indices)}] = {intlist2intarray([len(i) for i in Es_indices])};\n"

if l > 0:
    out += f"static const unsigned int {vname}_m_indices[{len(m_indices)}] = {intlist2intarray(m_indices)};\n"
    vname_m_indices = f"{vname}_m_indices"
else:
    vname_m_indices = f"NULL"

out += f"""
{int_t(f"{vname}_p", mod)}
{int_t(f"{vname}_pinv", redc(1/mod % q, q))}
static const unsigned int {vname}_s1_indices[{len(s1_indices)}] = {intlist2intarray(s1_indices)};
static const lin_params_t {vname} = {{{{ {name}, {deg}, {vname}_p, {vname}_pinv, {k}, {vname}_s1_indices, {len(s1_indices)}, {vname_m_indices}, {len(m_indices)}, {vname_Ps}, {matPs_nrows}, {strEs}, {strEs_nrows}, NULL, NULL }}}};
"""
printc(out)
