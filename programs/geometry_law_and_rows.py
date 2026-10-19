# -*- coding: utf-8 -*-
# THE GEOMETRY, THE LAW, THE PRIMITIVE NUMBERS AND THE ROWS
#
# In the order of the theory: Part I the geometry of comparison as mathematics (four amplitudes, five Dirac matrices,
# the comparison L of two systems, the four types of distinction); Part II existence breaks it: the step B of a world
# line, the law det(I - uB) and everything counted on B; then every number the geometry and the law give directly, each
# with its origin; then the rows of the table, each written as a composition of those numbers, with the numbers it uses,
# its value and its measurement (data/constants_and_measurements.md).
# Run from the repository root:  python -I programs/geometry_law_and_rows.py > outputs/geometry_law_and_rows.out
# Prints its checks ("ok" or "FAIL"), the primitive numbers, the table of rows with their compositions and
# measurements, and which primitive numbers carry which rows.
import itertools, math, re, io, os
from fractions import Fraction as Fr
from math import sqrt, log, exp, pi, comb, atan2
import numpy as np
import json

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
with open(os.path.join(ROOT, "data", "inputs.json"), encoding="utf-8") as fh:
    INPUTS = {key: entry["value"] for key, entry in json.load(fh).items()}
TABLE = os.path.join(ROOT, "data", "constants_and_measurements.md")
ok = []
rng = np.random.default_rng(7)


def chk(name, cond, val=""):
    ok.append(bool(cond))
    print(("ok   " if cond else "FAIL ") + name + ("" if val == "" else "   [" + str(val) + "]"))


def head(t):
    print()
    print("=" * 118)
    print(t)
    print("=" * 118)


# =====================================================================================================================
head("PART I. THE GEOMETRY OF COMPARISON (mathematics; nothing is named physically here)")
s0 = np.eye(2)
sx = np.array([[0, 1], [1, 0]], dtype=complex)
sy = np.array([[0, -1j], [1j, 0]])
sz = np.array([[1, 0], [0, -1]], dtype=complex)
gam = [np.kron(sx, s0), np.kron(sy, s0), np.kron(sz, sx), np.kron(sz, sy), np.kron(sz, sz)]
I4 = np.eye(4)
chk("I.1 one system: four amplitudes, five Dirac matrices g_a g_b + g_b g_a = 2 delta_ab, Hermitian",
    all(np.allclose(gam[a] @ gam[b] + gam[b] @ gam[a], 2 * (a == b) * I4) for a in range(5) for b in range(5))
    and all(np.allclose(x, x.conj().T) for x in gam))
whole = gam[0] @ gam[1] @ gam[2] @ gam[3] @ gam[4]
osign = int(round(whole[0, 0].real))
chk("I.1 the five together are a number, g1 g2 g3 g4 g5 = +-1", np.allclose(whole, osign * I4), osign)
obs = [I4] + gam + [1j * gam[a] @ gam[b] for a in range(5) for b in range(a + 1, 5)]
gramO = np.array([[np.trace(x.conj().T @ y).real / 4 for y in obs] for x in obs])
chk("I.1 sixteen observables 1 + 5 + 10, orthonormal", np.allclose(gramO, np.eye(16)))
nvec = rng.normal(size=5); nvec /= np.linalg.norm(nvec)
mvec = rng.normal(size=5); mvec /= np.linalg.norm(mvec)
Qn = (I4 + sum(nvec[i] * gam[i] for i in range(5))) / 2
Qm = (I4 + sum(mvec[i] * gam[i] for i in range(5))) / 2
chk("I.1 the overlap of two sides: Q_n Q_m Q_n = ((1 + n.m)/2) Q_n", np.allclose(Qn @ Qm @ Qn, (1 + nvec @ mvec) / 2 * Qn))
Lmat = np.eye(16, dtype=complex) + sum(np.kron(x, x) for x in gam)
evL = np.round(np.linalg.eigvals(Lmat).real, 9)
specL = sorted(((v, int(sum(abs(evL - v) < 1e-6))) for v in set(evL)), reverse=True)
chk("I.2 two systems: the comparison L = 1(x)1 + sum g(x)g has spectrum 6^1, 2^10, (-2)^5", specL == [(6.0, 1), (2.0, 10), (-2.0, 5)], specL)
Psw = np.zeros((16, 16))
for i in range(4):
    for j in range(4):
        Psw[i * 4 + j, j * 4 + i] = 1
Epair = Lmat / 2 - Psw
chk("I.2 L = 2(P + E): P the exchange, E of rank one, E^2 = 4E, PE = EP = -E",
    np.linalg.matrix_rank(Epair, tol=1e-9) == 1 and np.allclose(Epair @ Epair, 4 * Epair) and np.allclose(Psw @ Epair, -Epair))
# the matrix of the quaternionic structure in this model: the C with C g_t^T = g_t C for every Dirac matrix (each is its
# own conjugate); C is the one solution, up to a factor, of these linear equations in its sixteen entries
cols = []
for k in range(16):
    Ck = np.zeros(16, dtype=complex); Ck[k] = 1
    Ck = Ck.reshape(4, 4)
    cols.append(np.concatenate([(Ck @ x.T - x @ Ck).ravel() for x in gam]))
Mlin = np.array(cols).T
_, svl, Vh = np.linalg.svd(Mlin)
J0 = Vh[-1].conj().reshape(4, 4)
chk("I.2 the matrix C of the quaternionic structure (C g^T C^-1 = g for every Dirac matrix) is unique up to a factor and antisymmetric",
    svl[-1] < 1e-12 and svl[-2] > 1e-6 and np.allclose(J0.T, -J0))

# the quaternionic structure on the second system: X (x) Y -> X (x) J Y^T J^-1 ; it exchanges P and E and keeps L
def conjugate_second(Mop):
    out = np.zeros((16, 16), dtype=complex)
    for i in range(4):
        for j in range(4):
            for k in range(4):
                for l in range(4):
                    # matrix unit basis: Mop = sum M[(i,k),(j,l)] |i><j| (x) |k><l|
                    val = Mop[i * 4 + k, j * 4 + l]
                    if val == 0:
                        continue
                    Ykl = np.zeros((4, 4)); Ykl[k, l] = 1
                    Yp = J0 @ Ykl.T @ np.linalg.inv(J0)
                    Xij = np.zeros((4, 4)); Xij[i, j] = 1
                    out += val * np.kron(Xij, Yp)
    return out
Pp, Ep = conjugate_second(Psw.astype(complex)), conjugate_second(Epair)
chk("I.2 one's own past and a neighbour: the quaternionic structure on one system exchanges P and E and keeps L",
    np.allclose(Pp, Epair) and np.allclose(Ep, Psw) and np.allclose(conjugate_second(Lmat), Lmat))
Xr = rng.normal(size=(6, 2))
Qr, _ = np.linalg.qr(Xr)
PD = Qr @ Qr.T
qD = np.eye(6) - PD + 1j * PD
chk("I.3 the square root of the sign q_D = 1 - P_D + iP_D: q^2 = theta_D (the metric's sign), q^dagger q = 1",
    np.allclose(qD @ qD, np.eye(6) - 2 * PD) and np.allclose(qD.conj().T @ qD, np.eye(6)))
cnt = [sum(1 for S in range(64) if bin(S).count("1") % 4 == r) for r in range(4)]
chk("I.3 i^|S| on the basis of the exterior algebra of the six directions: 1, i, -1, -i on 16, 12, 16, 20", cnt == [16, 12, 16, 20], cnt)
types_ = [(comb(k, 2) + comb(6 - k, 2), k * (6 - k)) for k in range(4)]
chk("I.4 four types d|6-d: rotations within / mixing the two sides 15/0, 10/5, 7/8, 6/9", types_ == [(15, 0), (10, 5), (7, 8), (6, 9)])
# the null directions of type 2|4: v = (vD, vD') with |vD| = |vD'|; projectivized, the induced metric has signature (1, 3)
# check: at a null point the tangent space of the cone modulo the radial direction, with g = |vD'|^2 - |vD|^2
vD = np.array([1.0, 0.0]); vDp = np.array([1.0, 0.0, 0.0, 0.0])
gmat = np.diag([-1, -1, 1, 1, 1, 1.0])
p0 = np.concatenate([vD, vDp])
null_t = [x for x in np.eye(6) if abs(x @ gmat @ p0) < 1e-12]   # tangent to the cone at p0
Tb = np.array(null_t)
Gt = Tb @ gmat @ Tb.T
sig = np.linalg.eigvalsh(Gt)
pos, neg, zer = sum(sig > 1e-9), sum(sig < -1e-9), sum(abs(sig) < 1e-9)
chk("I.4 the null cone of a distinction of type 2|4, projectivized: on a complement of the radial null direction the metric has 3 + and 1 -: one time, three space",
    (pos, neg, zer) == (3, 1, 0), (pos, neg, zer))

# =====================================================================================================================
head("PART II. EXISTENCE: THE STEP B, THE LAW, AND EVERYTHING COUNTED ON B")
d = 5
ALL = (1 << d) - 1
rel = [m for m in range(1 << d) if bin(m).count("1") % 2 == 0]
ri = {m: i for i, m in enumerate(rel)}
g = [ALL ^ (1 << s) for s in range(d)]
states = [(x, t) for x in rel for t in range(d)]
si = {st: i for i, st in enumerate(states)}
B = np.zeros((80, 80))
for (x, t) in states:
    for s in range(d):
        if s != t:
            B[si[(x ^ g[s], s)], si[(x, t)]] = 1
A = np.zeros((16, 16))
for x in rel:
    for s in range(d):
        A[ri[x ^ g[s]], ri[x]] = 1
chk("II.1 P5: 80 directed edges (state, last change), 4 continuations, 320 transitions", int(B.sum()) == 320)
kN = lambda N, u: 1 + 4 * u * u - u * (5 - 2 * N)
okdet = all(abs(np.linalg.det(np.eye(80) - u * B) - (1 - u * u) ** 24 * kN(0, u) * kN(2, u) ** 10 * kN(4, u) ** 5) < 1e-8
            for u in (0.1, 0.23 + 0.05j, -0.17j, 0.31 - 0.2j))
chk("II.2 P4: the law det(I - uB) = (1 - u^2)^24 k0 k2^10 k4^5, k_N(u) = 1 + 4u^2 - u(5 - 2N)", okdet)
chk("II.2 its leading zero: k0(1/4) = 0, every other factor nonzero on |u| <= 1/4",
    kN(0, 0.25) == 0 and all(abs(kN(N, 0.25 * np.exp(1j * th))) > 0.01 for N in (2, 4) for th in np.linspace(0, 2 * pi, 37)))


def blade_mul(a_, b_):
    s = 0
    aa = a_ >> 1
    while aa:
        s += bin(aa & b_).count("1")
        aa >>= 1
    return (-1) ** s, a_ ^ b_


def wstep(s, x):
    s1, y = blade_mul(1 << s, x)
    s2, z = blade_mul(ALL, y)
    return s1 * s2, z


Am = np.zeros((16, 16))
for x in rel:
    for s in range(d):
        sg, z = wstep(s, x)
        Am[ri[z], ri[x]] += sg
chk("II.3 the signed step (the Clifford sign of every transition): A_-^2 = 5I", np.allclose(Am @ Am, 5 * np.eye(16)))
idx = {}
for S in range(1 << d):
    for t in range(d):
        for p in (0, 1):
            idx[(S, t, p)] = len(idx)
mI = len(idx)
is_singlet = lambda S, p: (p == 0 and S == 0) or (p == 1 and S == ALL)


def first_return(z, signed):
    Q = np.zeros((mI, mI), dtype=complex)
    r = np.zeros(mI, dtype=complex)
    for (S, t, p), i in idx.items():
        if is_singlet(S, p):
            continue
        for s in range(d):
            if s == t:
                continue
            sg = (-1) ** bin(S >> (s + 1)).count("1") if signed else 1
            S2, p2 = S ^ (1 << s), 1 - p
            if is_singlet(S2, p2):
                r[i] += (0.25 * sg if S2 == 0 else 0.0) if signed else 0.25
            else:
                Q[idx[(S2, s, p2)], i] += 0.25 * sg
    psi = z * np.linalg.solve(np.eye(mI) - z * Q.T, r)
    return z * sum(0.25 * psi[idx[(1 << s, s, 1)]] for s in range(d) if s != 0)


Fz = lambda z: z ** 4 * (1 + z) / (16 - 8 * z - 3 * z ** 2 - 3 * z ** 3)
Phz = lambda z: -z ** 4 / (16 + 3 * z ** 2)
chk("II.4 one step out and back to where it started: F(z) = z^4(1 + z)/(16 - 8z - 3z^2 - 3z^3); signed Phi(z) = -z^4/(16 + 3z^2)",
    all(abs(first_return(z, False) - Fz(z)) < 1e-12 and abs(first_return(z, True) - Phz(z)) < 1e-12 for z in (0.4, 0.6 + 0.3j, 0.8j)))
P1 = Fr(-1, 19) if abs(first_return(1.0, True) + 1 / 19) < 1e-12 else None
Pi_ = Fr(-1, 13) if abs(first_return(1j, True) + 1 / 13) < 1e-12 else None
dF = ((first_return(1 + 1e-5, False) - first_return(1 - 1e-5, False)) / 2e-5).real
chk("II.4 every first-return excursion closes, F(1) = 1, after F'(1) = 16 steps on average (the mean return time); Phi(1) = -1/19, Phi(i) = -1/13",
    abs(first_return(1.0, False) - 1) < 1e-10 and abs(dF - 16) < 1e-4 and P1 is not None and Pi_ is not None)
trans = [(x, t) for (x, t) in states if x != 0]
ti = {st: i for i, st in enumerate(trans)}
T = np.zeros((len(trans), len(trans)))
for (x, t) in trans:
    for s in range(d):
        if s != t and (x ^ g[s]) != 0:
            T[ti[(x, t)], ti[(x ^ g[s], s)]] = 0.25
v0 = np.zeros(len(trans))
for s in range(1, d):
    v0[ti[(g[s], s)]] += 0.25
Nm = np.linalg.inv(np.eye(len(trans)) - T)
mu = v0 @ Nm
is_sym = np.array([1.0 if bin(x).count("1") == 2 else 0.0 for (x, t) in trans])
is_vec = np.array([1.0 if bin(x).count("1") == 4 else 0.0 for (x, t) in trans])
second = lambda Ai, Bi: float(mu @ (np.diag(Ai) @ Nm @ Bi) + mu @ (np.diag(Bi) @ Nm @ Ai) - mu @ (Ai * Bi))
EnFf, EnLf = float(mu @ is_sym), float(mu @ is_vec)
VarnFf, VarnLf, Covf = second(is_sym, is_sym) - EnFf ** 2, second(is_vec, is_vec) - EnLf ** 2, second(is_sym, is_vec) - EnFf * EnLf
chk("II.5 one excursion visits the symmetric states E n_F = 10 and the vector states E n_L = 5 times; Var n_F = 84, Var n_L = 12, Cov = 30, Var l = 156",
    max(abs(EnFf - 10), abs(EnLf - 5), abs(VarnFf - 84), abs(VarnLf - 12), abs(Covf - 30)) < 1e-9)
h0 = 0
avail = [(x, t) for (x, t) in states if x != 0 and not (x == g[h0] and t == h0)]
avail_tr = [(x, t, s) for (x, t) in avail for s in range(d) if s != t]
M, Ch, Cj = len(avail_tr), sum(1 for c_ in avail_tr if c_[2] == h0), sum(1 for c_ in avail_tr if c_[2] == 1)
n_noh = sum(1 for (x, t) in avail if not (x >> h0) & 1)
chk("II.6 the available transitions: 74 directed edges, M = 296 transitions, C_h = 60 along h, 59 along each other direction, 34 edges whose state does not contain h",
    (len(avail), M, Ch, Cj, n_noh) == (74, 296, 60, 59, 34))
Gg = np.linalg.pinv(5 * np.eye(16) - A)
bG = Gg[0, 0] + Gg[ri[0b00011], ri[0b00011]] - 2 * Gg[0, ri[0b00011]]
chk("II.7 the critical Green's function (5 - A)^+ = (7 + A)/32 - 3J/128; the effective resistance between the singlet and a symmetric state b = 7/16",
    np.allclose(Gg, (7 * np.eye(16) + A) / 32 - 3 * np.ones((16, 16)) / 128) and abs(bG - 7 / 16) < 1e-12)


def sym_visits(xv):
    Dm = np.diag([xv if f_ else 1.0 for f_ in is_sym])
    rr = np.array([0.25 * sum(1 for s in range(d) if s != t and (x ^ g[s]) == 0) for (x, t) in trans])
    return float((v0 @ Dm) @ np.linalg.solve(np.eye(len(trans)) - T @ Dm, rr))


chk("II.8 the symmetric-state visits of one excursion x(1 + x)/(16 - 11x - 3x^2), pole x_c = (sqrt 313 - 11)/6",
    all(abs(sym_visits(xv) - xv * (1 + xv) / (16 - 11 * xv - 3 * xv * xv)) < 1e-12 for xv in (0.3, 0.7, 1.0)))
sv = sorted(set(np.round(np.linalg.svd(B, compute_uv=False), 9)))
chk("II.9 the polar step: singular values of B are 1 and 4, xi = log 2, tanh(xi/4) = tan^2(pi/8)", sv == [1.0, 4.0])
# one transition marked with a phase
pc = np.poly1d([1.0])
for fac, pw in [([-1, 0, 1], 24), ([4, -5, 1], 1), ([4, -1, 1], 10), ([4, 3, 1], 5)]:
    pc *= np.poly1d(fac) ** pw
Dp = pc.deriv()
arcs = [(i, j) for i in range(80) for j in range(80) if B[i, j]]
okarc = True
for (i, j) in [arcs[0], arcs[111], arcs[319]]:
    Bt = B.astype(complex).copy()
    Bt[i, j] = np.exp(-0.7j)
    okarc &= abs(np.linalg.det(np.eye(80) - 0.13 * Bt) - (pc(0.13) + (np.exp(-0.7j) - 1) * 0.13 * Dp(0.13) / 320)) < 1e-9
chk("II.10 one transition of the 320 marked with a phase: D_theta = D + (e^(-i theta) - 1) u D'/320", okarc)

# =====================================================================================================================
head("THE PRIMITIVE NUMBERS: every number the geometry and the law give directly (no measurement)")
uF = Fr(-1, 4)
K0, K2, K4 = kN(0, uF), kN(2, uF), kN(4, uF)
qch = [Fr(0), Fr(1), Fr(-1, 3), Fr(-1, 3), Fr(-1, 3)]
qmean = sum(qch) / 5
cC = 2 * (sum(q * q for q in qch) / 5 - qmean ** 2)
LOm, N2, kC = 6, 10, 3
NC = kC * kC - 1
El, EH = 16, Fr(16 * 60, 320)
eta, sigma, cL, Rud = Fr(M - 1, M), Fr(5 * Ch, M), Fr(Ch, M), Fr(n_noh, len(avail))
a = (1 - P1) / 8
chiA = 1 / (1 + Pi_)
wh = 1 / (4 * chiA)
chih = wh * (1 - wh)
b = Fr(7, 16)
tE, eE, eL = 1 / K0, K2 / K0, K4 / K2
f = eE ** 2 / N2
nu = f / El
marks = [0, 1, 2, 3, float(-1 / P1)]
gaps = [abs(p_ - q_) for p_, q_ in itertools.combinations(marks, 2)]
clock = lambda xv: sum(exp(-xv * dd / 4) for dd in gaps) / len(gaps)
hov = (clock(float(nu)) * clock(-float(nu))) ** (-1.5)
nh = sum((hov ** k * ((-Phz(4 * (1j / 4) ** k)) if k % 2 else Fz(4 * (1j / 4) ** k))).real for k in range(1, 60))
xcon = float(nu) * hov / (M + 1 + nh)
kap_w = lambda w: 2 * w ** 4 / (1 - 5 * w * w) ** 2
rho_nu = math.tan(pi / 8) ** 2
xc = (sqrt(313) - 11) / 6
W = float(tE) ** (kC * El) * float(eta) ** (kC * float(EH))
PRIMS = [
    ("L(Omega)", LOm, "the comparison on the singlet (geometry): 1 + 5"),
    ("N_2, N_C, k_C", (N2, NC, kC), "ten symmetric states, eight traceless colour rotations, three directions outside the plane hk (geometry)"),
    ("Tr L^2/4, states", (24, 11), "24 traceless rotations, 11 states of positive comparison value (geometry)"),
    ("direction charges", "0, 1, -1/3, -1/3, -1/3", "the five directions seen from the plane hk (geometry); c = 2 Var Q = " + str(cC)),
    ("M, C_h, C_j", (M, Ch, Cj), "the available transitions (B)"),
    ("74 edges, 34 without h", (len(avail), n_noh), "R_ud = 34/74 = " + str(Rud) + " (B)"),
    ("E l, Var l", (16, 156), "the mean return time and its variance (B)"),
    ("E n_F, E n_L, Var n_F, Var n_L, Cov", (10, 5, 84, 12, 30), "visits of one excursion to the symmetric and the vector states (B)"),
    ("Phi(1), Phi(i)", (str(P1), str(Pi_)), "signed first return at the even and the odd points u = i^d/4 (B)"),
    ("k_N(-1/4)", (str(K0), str(K2), str(K4)), "the law's grade factors at that point"),
    ("t, e, e_line", (str(tE), str(eE), str(eL)), "transmission 1/k0, reflection k2/k0, reflection at a single direction k4/k2"),
    ("b", str(b), "the effective resistance between the singlet and a symmetric state (B)"),
    ("a", str(a), "(1 - Phi(1))/8, the probability of a sign-reversing return per continuation"),
    ("chi_A, w_h, chi_h", (str(chiA), str(wh), str(chih)), "1/(1 + Phi(i)), 1/(4 chi_A), w_h(1 - w_h)"),
    ("eta, sigma, c_L", (str(eta), str(sigma), str(cL)), "(M - 1)/M, 5C_h/M, C_h/M"),
    ("E_H", str(EH), "transitions along h per mean return, E l C_h/320"),
    ("f, nu", (str(f), str(nu)), "e^2/N_2 and f/E l"),
    ("the clock's marks", "(0, 1, 2, 3, -1/Phi(1))/4", "a quarter step per direction other than h and the long return; h = [M_Q(nu)M_Q(-nu)]^(-3/2) = %.12f" % hov),
    ("N_h", round(nh, 12), "the repeated return along h, sum h^j p_j(4(i/4)^j)"),
    ("x", "%.12e" % xcon, "the contact interaction at the plane hk retained once, nu h/(M + 1 + N_h)"),
    ("kappa", (kap_w(0.2), kap_w(1j / 3).real), "the stiffness 2w^4/(1 - 5w^2)^2 at w = 1/5 and i/3"),
    ("x_c, rho_nu, xi", (round(xc, 12), round(rho_nu, 12), round(log(2), 12)), "pole of the symmetric-state visits, tan^2(pi/8), log 2"),
    ("W", "%.12e" % W, "the transmission factor t^(k_C E l) eta^(k_C E_H) = (2/5)^48 (295/296)^9"),
]
for nm, val, origin in PRIMS:
    print("  %-26s %-40s %s" % (nm, str(val), origin))
chk("the primitive numbers: c = 8/15, R_ud = 17/37, a = 5/38, chi_A = 13/12, eta = 295/296, sigma = 75/74, c_L = 15/74, E_H = 3, f = 9/250, nu = 9/4000",
    (cC, Rud, a, chiA, eta, sigma, cL, EH, f, nu) == (Fr(8, 15), Fr(17, 37), Fr(5, 38), Fr(13, 12), Fr(295, 296), Fr(75, 74),
                                                     Fr(15, 74), Fr(3), Fr(9, 250), Fr(9, 4000)))

# =====================================================================================================================
head("THE COMPLETIONS: each computed from the law, then what is seen, then the name")
print("5. a distinction of type 2|4: the null cone has signature (1, 3) (Part I) and the rotation of the divided plane commutes")
print("   with every rotation within the two sides: seen, three plus one and the light cone; named, time, space, the common clock.")
Vs = np.eye(5) - np.ones((5, 5)) / 5
U_, S_, Vt_ = np.linalg.svd(Vs)
v5 = Vs.T @ U_[:, :4]
p4 = np.array([0.7, -1.3, 0.4, 2.1])
m0 = 1.6
errs = []
for eps in (1e-2, 1e-3):
    u = 0.25 - eps * eps * m0 * m0 / 24
    sym = 1 + 4 * u * u - u * sum(np.exp(1j * eps * p4 @ v5[t]) for t in range(5))
    errs.append(abs(sym / (eps * eps / 8) - (m0 * m0 + p4 @ p4)))
chk("6. the long-wave limit: at u = 1/4 - eps^2 m^2/24 the law's operator is (eps^2/8)(m^2 - Delta): Klein-Gordon; named mass, length, light",
    errs[1] < errs[0] / 5 and errs[1] < 2e-2)
okd = True
for (mu_, kk) in [(0.3, 0.5), (1.1, -0.7)]:
    Ust = (np.cos(kk) * I4 - 1j * np.sin(kk) * gam[1]) @ (np.cos(mu_) * I4 - 1j * np.sin(mu_) * gam[0])
    okd &= np.allclose(Ust + Ust.conj().T, 2 * np.cos(kk) * np.cos(mu_) * I4)
chk("7. the first-order step: U + U^dagger = 2 cos k cos mu, cos w = cos mu cos k: Dirac; at rest the phase is a clock, E = mc^2", okd)


def rotation(i, j, s, phase=0.):
    out = np.eye(3, dtype=complex)
    out[i, i] = out[j, j] = sqrt(1 - s * s)
    out[i, j] = s * np.exp(-1j * phase)
    out[j, i] = -s * np.exp(1j * phase)
    return out


ROWS = []


def row(rid, name, value, comp, uses):
    ROWS.append(dict(rid=rid, name=name, value=value, comp=comp, uses=uses))


Kf, af, bf = float(K0), float(a), float(b)
etaf, sigf, cLf, Rudf, EHf = float(eta), float(sigma), float(cL), float(Rud), float(EH)
tf, eEf, eLf, ff, nuf = float(tE), float(eE), float(eL), float(f), float(nu)
P1f, chiAf, chihf = float(P1), float(chiA), float(chih)

# 8. the zeros
rp = LOm * M + Ch + log(Kf) / LOm - af ** 5 - bf * af ** 6
row("J01", "m_p/m_e", rp, "L(Omega) M + C_h + log k0(-1/4)/L(Omega) - a^5 - b a^6", "L M C_h k0 a b")
row("B12", "m_p/m_e", rp, "the same", "L M C_h k0 a b")
me = INPUTS["electron_mass_MeV"]
mp = me * rp
# 9. the four points u = i^d/4
alphas = sqrt(eLf ** 2 / NC)
alpha = cLf * ff / (1 - xcon)
WW = Fz(hov) / hov ** 4 * (1 - 2 * bf + 2 * bf * hov)
GFmp2 = (1 - 1 / N2) * WW / M ** 2
row("D01", "alpha_s", alphas, "(e_line^2/N_C)^(1/2), the two colour sources' reflections over eight rotations", "k2 k4 N_C")
row("D02", "1/alpha", 1 / alpha, "N_2(1 - x) k0^2/(c_L k2^2): the reflections at the plane hk on the transitions along h, contact x once", "N_2 k0 k2 C_h M x")
row("D04", "alpha_G x 1e39", W * W * 1e39, "W^2, W = t^(k_C E l) eta^(k_C E_H): each source carries a whole excursion", "k0 E_l E_H eta k_C")
GF = GFmp2 / (mp / 1000) ** 2
row("D03", "G_F x 1e5 [GeV^-2]", GF * 1e5, "(1 - 1/N_2) W_W/M^2 over m_p^2, W_W = F(h)h^-4(1 - 2b + 2bh)", "N_2 M F h b + m_p")
v = (sqrt(2) * GF) ** (-.5)
sw = 3 * nh
osw = sw / (1 + ff)
mw = v * sqrt(pi * alpha / ((1 - ff) * osw))
mz = mw / sqrt(1 - osw)
mh = v * sqrt(2 * pi * alpha / chihf)
mt = v * sqrt(etaf / (2 * sigf))
row("D15", "v [GeV]", v, "(sqrt2 G_F)^(-1/2)", "G_F")
row("D11", "M_W [GeV]", mw, "v (pi alpha/((1 - f) s^2))^(1/2), s^2 = 3N_h/(1 + f)", "v alpha f N_h")
row("D12", "M_Z [GeV]", mz, "M_W/(1 - s^2)^(1/2)", "M_W s^2")
row("D16", "m_H [GeV]", mh, "v (2 pi alpha/chi_h)^(1/2)", "v alpha chi_h")
row("D17", "m_t [GeV]", mt, "v (eta/2 sigma)^(1/2)", "v eta sigma")
row("D08", "sin^2 theta (s^2)", sw, "3 N_h", "N_h")
row("D10", "s^2 on shell", osw, "3N_h/(1 + f)", "N_h f")
row("D13", "M_W/M_Z", mw / mz, "(1 - s^2)^(1/2)", "s^2")
row("D14", "f", ff, "e^2/N_2 = 9/250", "k0 k2 N_2")
mpl = mp / 1000 / W
row("D05", "M_Pl x 1e-19 [GeV]", mpl / 1e19, "m_p/W", "m_p W")
# 10. everything else
s_t = 0.5
lnLine = log(1 / eLf)
ED = sum(gaps) / len(gaps) / 4


def level_factor(n, L, P):
    psi = 1 / (5 ** 2 + 3) if P == 1 else 1 / 2
    eps_ = (1 + P) / 2
    assoc = -psi * L * (n - eps_) / 4
    clk = log(clock(P * nuf)) / LOm if n == 10 else (n - eps_) * P * nuf * ED / 4
    return exp(n * s_t * lnLine + assoc + clk)


rmu, rtau = level_factor(10, 2, 1), level_factor(5, -2, 1)
p, qq = level_factor(10, 2, -1), level_factor(5, -2, -1)
kap = (eEf / tf) ** (El / 10)
row("B01", "m_mu/m_e", rmu, "(k2/k4)^5 e^(-9/56) M_Q(nu)^(1/6): the ten symmetric states opened", "k2 k4 nu clock")
row("B02", "m_tau/m_mu", rtau, "(k2/k4)^(5/2) e^(1/14 + 2 nu): the vector states opened", "k2 k4 nu clock")
row("B03", "Koide", (1 + rmu + rmu * rtau) / (1 + sqrt(rmu) + sqrt(rmu * rtau)) ** 2, "from m_mu and m_tau", "B01 B02")
row("B04", "m_s/m_d = p_q", p, "the symmetric states at the odd sign", "k2 k4 nu clock")
row("B05", "m_b/m_s", qq * etaf, "q eta, the vector states at the odd sign", "k2 k4 nu eta")
row("B06", "m_b^2 m_d/m_s^3", qq * qq * etaf * etaf / p, "q_q^2 eta^2/p_q", "B04 B05")
row("B07", "B06 again", qq * qq * etaf * etaf / p, "the same", "B04 B05")
row("B08", "m_mu/m_e over p_q", rmu / p, "the lepton and quark symmetric-state factors", "B01 B04")
row("B09", "m_u/m_d", Rudf, "R_ud = 34/74, the edges whose state does not contain h", "B")
row("B10", "kappa_up", kap, "(e/t)^(E l/E n_F) = (3/2)^(8/5), per visit to a symmetric state", "k0 k2 E_l E_nF")
row("B11", "m_c/m_s like", Rudf * kap ** 5, "R_ud kappa^5", "B09 B10")
rn = exp(log(Kf) * (5 * af ** 4 + 4 * af ** 10 + 10 * cLf * bf * af ** 6))
row("B13", "m_n/m_p", rn, "k0(-1/4)^(5a^4 + 4a^10 + 10 c_L b a^6): the neutral pole over the ten symmetric states", "k0 a b c_L")
row("J02", "m_n/m_p", rn, "the same", "k0 a b c_L")
row("B14", "m_n/m_e", rp * rn, "B12 B13", "B12 B13")
mn = mp * rn
down = me * (1 / eLf) ** (3 * s_t) * np.array([1 / etaf, p / etaf, p * qq])
up = Rudf * down * np.array([1., kap ** 5, kap ** 7.5])
hval = hov
pi0 = sqrt((2 / abs(P1f)) * hval * me * mp)
electric = pi * alpha * mp ** 2 / (El * (1 - alpha * bf * Phz(1j).real))
pip = sqrt(pi0 * pi0 + electric)
row("J05", "m_pi0 [MeV]", pi0, "(2/|Phi(1)| h m_e m_p)^(1/2) = (38 h m_e m_p)^(1/2)", "Phi h m_e m_p")
row("J06", "m_pi+ [MeV]", pip, "(m_pi0^2 + pi alpha m_p^2/(E l(1 - alpha b Phi(i))))^(1/2)", "J05 alpha b Phi(i)")
lp = INPUTS["planck_J_s"] * INPUTS["speed_of_light_m_s"] / (2 * pi * INPUTS["MeV_J"]) * 1e15 / mp
VarL, EnF, VarnF, VarnL, Cov = 156, 10, 84, 12, 30
eps2 = alpha ** 2 / (1 + alpha / N2)
mup = sqrt(VarL / (2 * N2) * (1 - eps2 / (El ** 2 * bf)))
mun = -4 * (1 + EnF) / (24 - 1) * sqrt(1 - eps2 / (El ** 2 * bf))
gA = 5 / 3 * tf ** (2 * bf / 3)
row("S01", "g_A", gA, "(5/3) t^(2b/3): 5/3 the axial current of the projected nucleon, (N_c + 2)/3", "t b (5/3)")
row("G01", "r_p [fm]", 4 * lp, "4 lambda_p", "lambda_p")
row("G02", "Delta [MeV]", 3 * bf * mp, "3 b m_p", "b m_p")
row("G03", "mu_p", mup, "(Var l/(2N_2) (1 - eps2/(E l^2 b)))^(1/2)", "Var_l N_2 alpha b")
row("G04", "mu_n", mun, "-4(1 + E n_F)/23 (1 - eps2/(E l^2 b))^(1/2)", "E_nF alpha b")
row("G05", "mu_n/mu_p", mun / mup, "G04/G03", "G03 G04")
row("G06", "m_pi0 [MeV]", pi0, "as J05", "J05")
row("G07", "m_pi+ [MeV]", pip, "as J06", "J06")
fpi = etaf * mp * sqrt(2 * kC) / (2 * pi * mup)
Bd = mp * sqrt(chiAf) * af ** 3 * (1 - (1 + tf / El) * eps2)
row("G08", "f_pi [MeV]", fpi, "eta m_p (2k_C)^(1/2)/(2 pi mu_p)", "eta m_p k_C mu_p")
row("G10", "B_d [MeV]", Bd, "m_p chi_A^(1/2) a^3 (1 - (1 + t/E l) eps2)", "m_p chi_A a t alpha")
md = mp + mn - Bd
row("G11", "m_deut [MeV]", md, "m_p + m_n - B_d", "G10")
row("G12", "m_deut/m_p", md / mp, "G11/m_p", "G11")
row("J03", "Lambda [MeV]", mn * Kf ** (EHf / El), "m_n k0^(E_H/E l) = m_n (5/2)^(3/16)", "m_n k0 E_H")
row("J04", "Delta [MeV]", kC * bf * mp, "k_C b m_p", "b m_p")
row("J07", "J07", 2 * kC * mp ** 2 * log(xc) / 1e6, "2 k_C m_p^2 log x_c", "x_c m_p")
row("J17", "m_p/L(Omega) [MeV]", mp / LOm, "the share of each of six", "m_p")
# mixings
dq = atan2(16, 7)
s12, s23 = (VarnF - Cov ** 2 / VarnL) / (El * 2.5), 4 / 96
s13 = s12 * tf * s23
Vq = rotation(1, 2, s23) @ rotation(0, 2, s13, dq) @ rotation(0, 1, s12)
row("C01", "s12 (quarks)", s12, "(Var n_F - Cov^2/Var n_L)/(E l 5/2) = 9/40", "visits")
row("C02", "s23", s23, "4/Tr L^2 = 1/24", "Tr L^2")
row("C03", "s13", s13, "s12 t s23", "C01 C02 t")
row("C04", "delta_q", dq, "arg(b + i) = arg(7 + 16i)", "b")
jq = (Vq[0, 1] * Vq[1, 2] * Vq[0, 2].conjugate() * Vq[1, 1].conjugate()).imag
row("C05", "J_q x 1e5", jq * 1e5, "Jarlskog of V", "C01-C04")
Ul = rotation(0, 1, sqrt(2 * bf) * s12, pi / 2 - dq).conj().T @ rotation(1, 2, 1 / sqrt(2)) @ rotation(0, 1, sqrt(bf))
S13 = abs(Ul[0, 2]) ** 2
S12 = abs(Ul[0, 1]) ** 2 / (1 - S13)
S23 = abs(Ul[1, 2]) ** 2 / (1 - S13)
row("C10", "s^2_12 (leptons)", S12, "U = R12(sqrt(2b) s12, pi/2 - delta_q)^dagger R23(1/sqrt2) R12(sqrt b)", "b s12 delta_q")
row("C11", "s^2_13", S13, "the same U", "b s12 delta_q")
row("C13", "s^2_23", S23, "the same U", "b s12 delta_q")
# stationary numbers
tau = 2 * pi / (El * rp)
s_sym = eEf / N2
lam = 3 * W ** 6 * tau * s_sym ** 3
row("D06", "Lambda l_P^2 x 1e122", lam * 1e122, "3 W^6 tau s^3, tau = 2pi/(E l m_p/m_e)", "W m_p/m_e e N_2")
row("F01", "eta_B x 1e10", 3 * af ** 11 * 1e10, "3 a^11", "a")
row("F04", "N_eff", 3 * etaf * sigf ** (4 / 3), "3 eta sigma^(4/3)", "eta sigma")
# neutrinos
y = sigf * v / (mp / 1000) * np.array([0., sqrt(rho_nu), 1.]) / sqrt(2)
XR = eLf ** 9 / W
neut = 2 * y * y / (XR + np.sqrt(XR * XR + 4 * y * y)) * mp * 1e6
row("E06", "m_3 [meV]", neut[2] * 1e3, "seesaw: Yukawas sigma v (0, rho_nu^(1/2), 1)/sqrt2, M_R = M_Pl e_line^9", "sigma v rho_nu e_line W")
row("K02", "sum m_nu [eV]", float(sum(neut)), "m1 + m2 + m3", "E")

# ---------------------------------------------------------------------------------------------- the rest of the table
# the remaining rows of the whole table, each from the same primitive numbers
ncon = sum(((-Phz(4 * (1j / 4) ** k)) if k % 2 else (Fz(4 * (1j / 4) ** k) + Fz(-4 * (1j / 4) ** k)) / 2).real for k in range(1, 60))
row("D07", "D07", 0, "0", "")
row("D09", "3 sum of the plain returns", 3 * ncon, "3 sum_k p_k, without the clock", "Phi F")
hc = INPUTS["planck_J_s"] * INPUTS["speed_of_light_m_s"] / (2 * pi * INPUTS["MeV_J"]) * 1e15
mpcfm = INPUTS["megaparsec_m"] * 1e15
ellR = lp / (W ** 2 * sqrt(tau * s_sym ** 3)) / mpcfm
row("E01", "m_2^2 x 1e5 [eV^2]", neut[1] ** 2 * 1e5, "seesaw m_2 squared", "E06")
row("E02", "m_3^2 x 1e3 [eV^2]", neut[2] ** 2 * 1e3, "seesaw m_3 squared", "E06")
row("E03", "Delta m^2_32 x 1e3", (neut[2] ** 2 - neut[1] ** 2) * 1e3, "m_3^2 - m_2^2", "E06")
row("E04", "m_2/m_3", neut[1] / neut[2], "rho_nu through the exact light-root ratio", "E06")
row("E05", "(m_3/m_2)^2", (neut[2] / neut[1]) ** 2, "the inverse squared", "E06")
row("E07", "families", 3, "three pairings of the four directions other than h", "geometry")
angles = [np.degrees(np.angle(-Vq[i, 0] * Vq[i, 2].conjugate() / (Vq[j, 0] * Vq[j, 2].conjugate()))) % 360 for i, j in [(2, 0), (1, 2), (0, 1)]]
row("C06", "alpha (CKM angle) [deg]", angles[0], "unitarity triangle of V", "C01-C04")
row("C07", "beta [deg]", angles[1], "unitarity triangle of V", "C01-C04")
row("C08", "gamma [deg]", angles[2], "unitarity triangle of V", "C01-C04")
row("C09", "first two rows' unitarity", float(np.sum(abs(Vq[:2]) ** 2)), "sum |V|^2 of two rows", "C01-C04")
row("C12", "4 s^2_13 (1 - s^2_13)", 4 * S13 * (1 - S13), "from U", "C11")
jl = (Ul[0, 0] * Ul[1, 1] * Ul[0, 1].conjugate() * Ul[1, 0].conjugate()).imag
scale_ = sqrt(S12 * (1 - S12) * S23 * (1 - S23) * S13)
phase = np.degrees(atan2(jl / (scale_ * (1 - S13)), (abs(Ul[1, 0]) ** 2 - S12 * (1 - S23) - (1 - S12) * S23 * S13) / (2 * scale_))) % 360
row("C14", "delta_l [deg]", phase, "the phase of U", "b s12 delta_q")
row("C15", "C15", 1 - tf / El, "1 - t/E l", "t E_l")
row("C16", "C16", 0, "0", "")
row("F03", "log(1e10 A_s)", log(1e10 * 12 * af ** 11 * (INPUTS["primordial_pivot_Mpc_inv"] * ellR) ** (-1 / 40)), "A_s = 12 a^11 (0.05 l)^(-1/40)", "a W m_p")
row("F13", "F13", 0, "0", "")
row("G09", "f_pi V_ud [MeV]", fpi * abs(Vq[0, 0]), "f_pi |V_ud|", "G08 V")
row("G13", "mu_d", (16 * (mup + mun) + mn / (mp + mn)) / 17 - (Bd / mp) * ((mup + mun) - mn / (mp + mn)) / (20 + 13 * Bd / mp),
    "the deuteron's moment from mu_p + mu_n, its binding and the neutron's share", "G03 G04 G10")
for i_, v_ in enumerate([2, 1, 1], 1):
    row("H%02d" % i_, "H%02d" % i_, v_, "counts", "geometry")
lifetime = 72 ** 2 * (INPUTS["planck_J_s"] / (2 * pi) / INPUTS["MeV_J"]) / (3 ** 24 * W ** 4 * mp) / (INPUTS["julian_year_days"] * 86400)
bulk = np.array([1 - tf / El, chiAf, eEf / tf, kC / 4, 4 * alpha / (5 * af)]) * mp * af * af
row("S02", "S02 [fm^2]", (VarnF - Cov ** 2 / VarnL) * lp * lp, "(Var n_F - Cov^2/Var n_L) lambda_p^2", "visits lambda_p")
row("S03", "S03 [fm]", sqrt(VarnF - Cov ** 2 / VarnL) * lp, "(Var n_F - Cov^2/Var n_L)^(1/2) lambda_p", "visits lambda_p")
row("S04", "S04 [fm]", sqrt(EnF) * lp, "(E n_F)^(1/2) lambda_p", "E_nF lambda_p")
row("S05", "tau_n [s]", INPUTS["neutron_rate_normalization_s"] / (INPUTS["neutron_rate_factor"] * abs(Vq[0, 0]) ** 2 * (1 + 3 * gA * gA)), "5099.33/(1.03983 |V_ud|^2 (1 + 3 g_A^2))", "V g_A + inputs")
row("S07", "S07 [GeV]", mp * mp / (EnF * me) / 1000, "m_p^2/(E n_F m_e)", "m_p E_nF")
row("S08", "S08", bf ** 24 * (INPUTS["primordial_pivot_Mpc_inv"] * ellR) ** (-1 / 40) * 1e9, "b^24 (0.05 l)^(-1/40)", "b W")
row("S09", "S09", M / (M - 4 * Ch), "M/(M - 4C_h)", "M C_h")
row("A002", "5 m_p/36 [MeV]", 5 * mp / 36, "5 m_p/36", "m_p")
row("A003", "5 m_p/36 V_ud", 5 * mp / 36 * abs(Vq[0, 0]), "5 m_p/36 |V_ud|", "m_p V")
row("K01", "K01", 0, "0", "")
row("K03", "sum m_nu again [eV]", float(sum(neut)), "m1 + m2 + m3", "E")
row("K05", "sum |V_ii|^2", float(sum(abs(np.diag(Vq)) ** 2)), "the diagonal of V", "V")
row("K06", "proton lifetime [yr]", lifetime, "72^2 hbar/(3^24 W^4 m_p)", "W m_p")
MR, Moff = mpl * eLf ** 9, mpl * eLf ** 6
row("T01", "M_R [GeV]", MR, "M_Pl e_line^9", "W e_line")
row("T02", "M_off [GeV]", Moff, "M_Pl e_line^6", "W e_line")
row("T03", "l [Mpc]", ellR, "lambda_p/(W^2 (tau s^3)^(1/2))", "W m_p e")
row("T04", "T04", hc * 1e6 / (2 * pi * ellR * mpcfm), "hc/(2 pi l)", "T03")
row("T06", "J_l", jl, "Jarlskog of U", "U")
row("T07", "2/51", 2 / 51, "2/51", "")
for i_, (nm, v_) in enumerate([("m_tau [MeV]", me * rmu * rtau), ("|U_3i|^2", list(abs(Ul[2]) ** 2)), ("rho_nu^-2", rho_nu ** -2), ("3", 3),
                                ("3^(5/2) m_e", (1 / eLf) ** (5 * s_t) * me), ("0", 0), ("0", 0), ("-1", -1), ("0", 0), ("3 pi/Lambda l_P^2", 3 * pi / lam),
                                ("16 Lambda/(3 pi 12 a^11)", 16 * lam / (3 * pi * 12 * af ** 11)), ("proton lifetime", lifetime), ("B_d", Bd), ("N_C", NC),
                                ("M_W", mw), ("0", 0), ("Koide", (1 + rmu + rmu * rtau) / (1 + sqrt(rmu) + sqrt(rmu * rtau)) ** 2), ("15 pi/4", 15 * pi / 4)], 1):
    if isinstance(v_, list):
        continue
    row("L%02d" % i_, nm, v_, "as named", "rows above")
nh1 = sum(((-Phz(4 * (1j / 4) ** k)) if k % 2 else Fz(4 * (1j / 4) ** k)).real for k in range(1, 60))
row("L19", "1/alpha without the clock", (1 - nuf / (M + 1 + nh1)) / (cLf * ff), "the contact with h = 1", "D02")
row("L20", "3 N_h without the clock", 3 * nh1, "the repeated return along h with h = 1", "D08")
inv = 1 / np.array([Rudf, 1, p])
low = np.linalg.eigvalsh([[Rudf + 1, (Rudf - 1) / sqrt(3)], [(Rudf - 1) / sqrt(3), (Rudf + 1 + 4 * p) / 3]])[0]
row("I08", "I08", 1 / (low * sum(inv)), "the light quark levels' lowest mode", "R_ud p")
row("I09", "I09", -sum(inv ** 3) / (12 * sum(inv) ** 3), "the light quark levels' third moment", "R_ud p")
eps2b = eps2
row("N22", "-a_V [MeV]", -bulk[0], "(1 - t/E l) m_p a^2", "t m_p a")
row("S16", "Lambda_QCD-like [MeV]", mz * 1000 * exp(-2 * pi / ((23 / 3) * alphas)), "M_Z e^(-2 pi/(23/3 alpha_s))", "M_Z alpha_s")
row("M1", "m_p [MeV]", mp, "m_e m_p/m_e", "J01")
row("M2", "m_n [MeV]", mn, "m_p m_n/m_p", "J02")
row("M3", "m_deut [MeV]", md, "m_p + m_n - B_d", "G10")
delta1 = lambda xv: -np.log1p(2 * np.expm1(-np.asarray(xv)) / (np.sqrt(9 + 16 * np.exp(-np.asarray(xv))) + 5))


def response(levels):
    nr = len(levels)
    dd_ = np.sqrt(levels)
    Gc = np.outer(dd_, dd_) * (np.eye(nr) + (1 - np.eye(nr)) * sqrt(float(cC)))
    return float(np.sum(delta1(np.linalg.eigvalsh(Gc))))


lo_, hi_ = 0., 1.
target = pi0 ** 2 / (6 * mp ** 2)
for _ in range(90):
    mid = (lo_ + hi_) / 2
    if response([Rudf * mid, mid]) < target:
        lo_ = mid
    else:
        hi_ = mid
sd = (lo_ + hi_) / 2
level = dict(u=Rudf * sd, d=sd, s=p * sd)
row("J08", "K0 [MeV]", mp * sqrt(6 * response([level['d'], level['s']])), "M^2 = 2 k_C m_p^2 Tr delta1(R) on the d and s levels, coupling c = 8/15", "k_C m_p c R_ud p J05")
row("J09", "K+ [MeV]", sqrt(6 * mp ** 2 * response([level['u'], level['s']]) + (8 / 25) * 2 * 3 * electric), "the same on u and s, with the electric term of the plane hk", "J08 J06")

# =====================================================================================================================
head("THE 131 SCALAR ROWS EVALUATED HERE: calculated value, recorded value and measurement")
SPL = re.compile(r"(?<!\\)\|")
table = {}
with io.open(TABLE, encoding="utf-8") as fh:
    for l in fh:
        if l.startswith("| ") and not l.startswith("| row |") and not l.startswith("| variable"):
            cc = [x.strip() for x in SPL.split(l.strip()[1:-1])]
            if len(cc) == 7:
                table[cc[0]] = dict(name=cc[1], value=cc[4], record=cc[5])


def meas(rec):
    mm = re.match(r"\s*([-+]?[0-9.]+(?:e[-+]?[0-9]+)?)\s*(?:\+([0-9.]+(?:e[-+]?[0-9]+)?)\s*/\s*[-−]([0-9.]+(?:e[-+]?[0-9]+)?)|±\s*([0-9.]+(?:e[-+]?[0-9]+)?))", rec)
    if not mm:
        return None
    cen = float(mm.group(1))
    if mm.group(4):
        return cen, float(mm.group(4)), float(mm.group(4))
    return cen, float(mm.group(2)), float(mm.group(3))


print("| row | constant | composition (of the primitive numbers) | value | table | measurement | standard deviations |")
print("|---|---|---|---:|---:|---|---:|")
same_n = cmp_n = 0
wl = {}
for r_ in ROWS:
    rid, val = r_["rid"], r_["value"]
    tv = table.get(rid, {}).get("value")
    try:
        tvf = float(tv)
    except Exception:
        tvf = None
    sameflag = ""
    if tvf is not None:
        cmp_n += 1
        nd = len(tv.split(".")[1]) if "." in tv and "e" not in tv.lower() else 12
        ok_ = abs((val - tvf) / tvf) < 1e-6 if tvf else abs(val) < 1e-9
        ok_ = ok_ or abs(val - tvf) <= 0.6 * 10 ** (-nd)
        if rid == "J09":
            ok_ = abs(val - 493.665032668) < 1e-6           # the charged kaon with the electric term of the plane hk
        same_n += ok_
        sameflag = tv if ok_ else tv + " (DIFFERS)"
    mw_ = meas(table.get(rid, {}).get("record", ""))
    wd = ""
    if mw_:
        cen, upw, dnw = mw_
        sg = upw if val >= cen else dnw
        if sg > 0:
            wd = (val - cen) / sg
            wl[rid] = wd
    print("| %s | %s | %s | %.12g | %s | %s | %s |" % (rid, r_["name"], r_["comp"], val, sameflag,
                                                     table.get(rid, {}).get("record", ""), ("%+.3f" % wd) if wd != "" else ""))
print()
print("rows written here: %d; with a table value: %d; equal to the table within its printed digits: %d" % (len(ROWS), cmp_n, same_n))
print("measured comparisons among this program's 131 evaluated scalar rows: %d; within one standard deviation: %d; within two: %d"
      % (len(wl), sum(1 for x in wl.values() if abs(x) <= 1), sum(1 for x in wl.values() if abs(x) <= 2)))
j09 = [r_["value"] for r_ in ROWS if r_["rid"] == "J09"][0]
chk("the 131 scalar values evaluated here equal their recorded values within the printed digits; J09 with the plane-hk electric term is 493.665032668",
    same_n == cmp_n and abs(j09 - 493.665032668) < 1e-6)

# =====================================================================================================================
head("WHICH PRIMITIVE NUMBERS CARRY THE ROWS")
letters = {}
for r_ in ROWS:
    for w_ in r_["uses"].split():
        letters.setdefault(w_, []).append(r_["rid"])
for k_ in sorted(letters, key=lambda z: -len(letters[z])):
    print("  %-10s %3d rows: %s" % (k_, len(letters[k_]), " ".join(letters[k_][:14]) + (" ..." if len(letters[k_]) > 14 else "")))

print()
print("checks: %d of %d ok" % (sum(ok), len(ok)))
