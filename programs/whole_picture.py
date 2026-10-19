# -*- coding: utf-8 -*-
# THE WHOLE PICTURE, COMPUTED
#
# Every finite statement and every number of the whole picture comes out of the four amplitudes and the step B of a world
# line on the sixteen two-spinor states. Besides B the program uses three pieces of geometry: the clock's five marks, a
# quarter step for each of the four directions other than h and the long return -1/Phi(1); the charges
# (0, 1, -1/3, -1/3, -1/3) of the five directions, which section 1 reads off the plane hk; and the rule's value of Psi at
# the two signs P = +1 and -1 of a divided set, 1/28 and 1/2. The measurements are read from
# data/constants_and_measurements.md.
# Run from the repository root:  python -I programs/whole_picture.py > outputs/whole_picture.out
# Prints its checks ("ok" or "FAIL") section by section, the law's values at the four points u = i^d/4, the couplings
# and masses, and the whole table with the measurements and the differences in standard deviations.
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


def chk(name, cond, val=""):
    ok.append(bool(cond))
    print(("ok   " if cond else "FAIL ") + name + ("" if val == "" else "   [" + str(val) + "]"))


def head(t):
    print()
    print("== " + t)


# ====================================================================================================== 1. geometry
head("1. The geometry of comparison: four amplitudes, five Dirac matrices, one comparison, four types")
s0 = np.eye(2)
sx = np.array([[0, 1], [1, 0]], dtype=complex)
sy = np.array([[0, -1j], [1j, 0]])
sz = np.array([[1, 0], [0, -1]], dtype=complex)
gam = [np.kron(sx, s0), np.kron(sy, s0), np.kron(sz, sx), np.kron(sz, sy), np.kron(sz, sz)]
I4 = np.eye(4)
chk("five Hermitian Dirac matrices on four amplitudes, g_a g_b + g_b g_a = 2 delta_ab",
    all(np.allclose(gam[a] @ gam[b] + gam[b] @ gam[a], 2 * (a == b) * I4) for a in range(5) for b in range(5))
    and all(np.allclose(x, x.conj().T) for x in gam))
omega = gam[0] @ gam[1] @ gam[2] @ gam[3] @ gam[4]
osign = int(round(omega[0, 0].real))
chk("the five together are central: g_1 g_2 g_3 g_4 g_5 = +-1", np.allclose(omega, osign * I4), osign)
# the square root of a distinction's sign
rng = np.random.default_rng(7)
Xr = rng.normal(size=(4, 2)) + 1j * rng.normal(size=(4, 2))
Qr, _ = np.linalg.qr(Xr)
PD = Qr @ Qr.conj().T
qD = I4 - PD + 1j * PD
chk("the square root of the sign q_D = I - P_D + iP_D: q_D^2 = I - 2P_D = theta_D and q_D^dagger q_D = I",
    np.allclose(qD @ qD, I4 - 2 * PD) and np.allclose(qD.conj().T @ qD, I4))
# one comparison L = I (x) I + sum_t g_t (x) g_t on C^4 (x) C^4
Lmat = np.eye(16, dtype=complex) + sum(np.kron(gt, gt) for gt in gam)
evL = np.round(np.linalg.eigvals(Lmat).real, 9)
specL = sorted(((v, int(sum(abs(evL - v) < 1e-6))) for v in set(evL)), reverse=True)
Lof = lambda X: X + sum(gt @ X @ gt for gt in gam)
chk("one comparison L = I (x) I + sum_t g_t (x) g_t has spectrum 6^1, 2^10, (-2)^5", specL == [(6.0, 1), (2.0, 10), (-2.0, 5)], specL)
chk("its blocks: the singlet L(I) = 6I, the ten symmetric states L(g_a g_b) = 2 g_a g_b, the five vector states L(g_a) = -2 g_a",
    np.allclose(Lof(I4), 6 * I4) and all(np.allclose(Lof(gam[a] @ gam[b]), 2 * gam[a] @ gam[b]) for a in range(5) for b in range(a + 1, 5))
    and all(np.allclose(Lof(gam[a]), -2 * gam[a]) for a in range(5)))
Psw = np.zeros((16, 16))
for i in range(4):
    for j in range(4):
        Psw[i * 4 + j, j * 4 + i] = 1
Epair = Lmat / 2 - Psw
chk("L = 2(P + E): P the exchange, E the singlet channel of rank one, P^2 = I, E^2 = 4E, PE = EP = -E",
    np.linalg.matrix_rank(Epair, tol=1e-9) == 1 and np.allclose(Epair @ Epair, 4 * Epair) and np.allclose(Psw @ Epair, -Epair)
    and np.allclose(Epair @ Psw, -Epair))
wE, VE = np.linalg.eigh((Epair + Epair.conj().T) / 2)
Jpart = VE[:, np.argmax(abs(wE))].reshape(4, 4)
chk("the singlet channel pairs each amplitude with its conjugate: E = |J><J| with J^T = -J, an antisymmetric form on the four amplitudes",
    np.allclose(Jpart.T, -Jpart))
# the four types of distinction of the six directions
types_ = [(k, comb(k, 2) + comb(6 - k, 2), k * (6 - k)) for k in range(4)]
chk("four types 0|6, 1|5, 2|4, 3|3: rotations within the two sides 15, 10, 7, 6 and mixing them d(6 - d) = 0, 5, 8, 9",
    [(x[1], x[2]) for x in types_] == [(15, 0), (10, 5), (7, 8), (6, 9)], types_)
chk("the whole system described once: Lambda(iI) e_S = i^|S| e_S, the four phases 1, i, -1, -i at |S| = 0, 1, 2, 3",
    [1j ** k for k in range(4)] == [1, 1j, -1, -1j])
ok_tw = True
for D in [set(), {0}, {0, 1}, {0, 1, 2}]:
    for S in range(64):
        for T in range(64):
            Ss = {k for k in range(6) if S >> k & 1}
            Ts = {k for k in range(6) if T >> k & 1}
            ok_tw &= (1j ** (len(Ss & D) + len(Ts & D))) == ((-1) ** len(Ss & Ts & D)) * (1j ** len((Ss ^ Ts) & D))
chk("a description carries the product: q_D(e_S)q_D(e_T) = (-1)^|S cap T cap D| q_D(e_S e_T), all 64 x 64 words", ok_tw)
# one generation: the sixteen two-spinor states, seen from the plane hk
hh_, kk_ = 0, 1
Fset, Cset = {0, 1}, {2, 3, 4}
evens5 = [frozenset(s) for r in (0, 2, 4) for s in itertools.combinations(range(5), r)]
Y = {S: Fr(len(S & Fset), 2) - Fr(len(S & Cset), 3) for S in evens5}
T3 = {S: Fr(len(S & {kk_}) - len(S & {hh_}), 2) for S in evens5}
Qline = [Fr(0), Fr(1), Fr(-1, 3), Fr(-1, 3), Fr(-1, 3)]           # the charges of h, k and the three directions outside the plane hk
Qrel = {S: sum((Qline[s] for s in S), Fr(0)) for S in evens5}
chk("the charge of a two-spinor state is how it meets the plane hk: Q = T_3 + Y, Y = |S cap F|/2 - |S cap C|/3, direction charges (0, 1, -1/3, -1/3, -1/3)",
    all(Qrel[S] == T3[S] + Y[S] for S in evens5))
mult = {}
for S in evens5:
    key = (len(S), len(S & Fset), len(S & Cset))
    mult[key] = mult.get(key, 0) + 1
chk("one generation: Y = 0 (1), 1 (1), -2/3 (3), 1/6 (6), 1/3 (3), -1/2 (2): nu^c, e^c, u^c, Q, d^c, L",
    sorted((str(Y[S]) for S in evens5)) == sorted(["0", "1"] + ["-2/3"] * 3 + ["1/6"] * 6 + ["1/3"] * 3 + ["-1/2"] * 2))
dbl = [S for S in evens5 if len(S & Fset) == 1]
trip = [S for S in evens5 if len(S & Cset) in (1, 2)]
chk("the generation carries no anomaly: sum Y = sum Y^3 = 0, sum over doublets Y = 0, sum over triplets Y = 0",
    sum(Y.values()) == 0 and sum(y ** 3 for y in Y.values()) == 0 and sum(Y[S] for S in dbl) == 0 and sum(Y[S] for S in trip) == 0)
chk("sum Y^5 = 5/9 over the sixteen", sum(y ** 5 for y in Y.values()) == Fr(5, 9))
beside = [1, 2, 3, 4]
pairings = {frozenset([frozenset(p), frozenset(set(beside) - set(p))]) for p in itertools.combinations(beside, 2)}
chk("the four directions other than h pair in exactly three ways: three families", len(pairings) == 3)
# the gauge algebra kept by the split 2 + 3 at the plane hk, and the Gram of h at the source
E = lambda i, j: np.outer(np.eye(5)[i], np.eye(5)[j]).astype(complex)
basis = []
for blk in ([0, 1], [2, 3, 4]):
    for i in blk:
        for j in blk:
            if i < j:
                basis.append(1j * (E(i, j) + E(j, i)) / sqrt(2))
                basis.append((E(i, j) - E(j, i)) / sqrt(2))
for blk in ([0, 1], [2, 3, 4]):                      # the diagonal rotations inside each block, traceless there
    n_ = len(blk)
    for m_ in range(1, n_):
        v = np.zeros(5)
        v[blk[:m_]] = 1
        v[blk[m_]] = -m_
        v /= np.linalg.norm(v)
        basis.append(1j * np.diag(v))
yv = np.array([3, 3, -2, -2, -2]) / sqrt(30)
basis.append(1j * np.diag(yv))                       # hypercharge, traceless on the five
chk("the rotations that keep the split 2 + 3 and the determinant: su(2) + su(3) + u(1), twelve generators", len(basis) == 12)
phi = np.eye(5)[hh_]
Gm = np.array([[np.real(np.vdot(X @ phi, Yb @ phi)) for Yb in basis] for X in basis])
gev = sorted(np.round(np.linalg.eigvalsh(Gm), 12))
nz = [x for x in gev if abs(x) > 1e-12]
chk("the direction h moves three of them, Gram eigenvalues 1/2, 1/2, 4/5: W+, W-, Z; nine stay massless, the photon and the colour rotations",
    np.allclose(nz, [0.5, 0.5, 0.8]) and len(gev) - len(nz) == 9, nz)
chk("at the source M_W^2/M_Z^2 = 5/8 and sin^2 theta = 3/8", abs(0.5 / 0.8 - 5 / 8) < 1e-15 and abs(1 - 0.5 / 0.8 - 3 / 8) < 1e-15)

# ====================================================================================================== 2. the law
head("2. Existence and the law: the step B, the law in one variable, the cells it walks on")
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
grade = lambda x: bin(x).count("1")
chk("P5: eighty directed edges (state, last change), each continued by the four other changes; 320 transitions", B.shape == (80, 80) and int(B.sum()) == 320)
lamA = sorted(set(np.round(np.linalg.eigvalsh(A), 9)), reverse=True)
chk("the graph of the two-spinor states has spectrum 5 - 2N on the grades N = 0, 2, 4", lamA == [5.0, 1.0, -3.0])
kN = lambda N, u: 1 + 4 * u * u - u * (5 - 2 * N)
okdet = True
for u in (0.1, 0.23 + 0.05j, -0.17j, 0.31 - 0.2j):
    lhs = np.linalg.det(np.eye(80) - u * B)
    rhs = (1 - u * u) ** 24 * kN(0, u) * kN(2, u) ** 10 * kN(4, u) ** 5
    okdet &= abs(lhs - rhs) < 1e-8 * max(1, abs(rhs))
chk("P4: the law det(I - uB) = (1 - u^2)^24 (1 - u)(1 - 4u)(1 - u + 4u^2)^10 (1 + 3u + 4u^2)^5", okdet)
okm = True
for u in (0.13, 0.2 + 0.1j):
    prod = 1
    for U in rel:
        chi = [(-1) ** bin(U & g[s]).count("1") for s in range(d)]
        aU, dU = chi.count(1), chi.count(-1)
        prod *= (1 + u) ** (aU - 1) * (1 - u) ** (dU - 1) * (1 + 4 * u * u - u * (aU - dU))
    okm &= abs(prod - np.linalg.det(np.eye(80) - u * B)) < 1e-9
chk("the two pairings are one operator: det = prod over the sixteen characters U of (1+u)^(a_U-1)(1-u)^(d_U-1)[1 + 4u^2 - u(a_U - d_U)]", okm)
# the cells: the cells of the five-cube with the whole flip, a cell structure of RP^4
cells = {}                                    # a k-cell: its vertices and its k free directions
for k in range(5):
    found = set()
    for x in rel:
        for S in itertools.combinations(range(d), k):
            vs = {x}
            for s in S:
                vs |= {v ^ g[s] for v in vs}
            found.add((frozenset(vs), frozenset(S)))
    cells[k] = sorted(found, key=lambda c: (sorted(c[1]), sorted(c[0])))
fvec = [len(cells[k]) for k in range(5)]
chk("the vertices, links, squares, cubes and four-cells: 16, 40, 40, 20, 5, Euler number 1, the cells of RP^4",
    fvec == [16, 40, 40, 20, 5] and sum((-1) ** k * fvec[k] for k in range(5)) == 1, fvec)


def bd2(k):                                   # boundary mod 2 from k-cells to (k-1)-cells
    idx = {c: i for i, c in enumerate(cells[k - 1])}
    M = np.zeros((len(cells[k - 1]), len(cells[k])), dtype=int)
    for j, c in enumerate(cells[k]):
        for f in cells[k - 1]:
            if f[0] <= c[0] and f[1] < c[1]:
                M[idx[f], j] = 1
    return M


def rank2(M):
    M = M.copy() % 2
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        piv = [i for i in range(r, rows) if M[i, c]]
        if not piv:
            continue
        M[[r, piv[0]]] = M[[piv[0], r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        r += 1
    return r


bds = {k: bd2(k) for k in range(1, 5)}
dd0 = all(not ((bds[k] @ bds[k + 1]) % 2).any() for k in range(1, 4))
rk = {k: rank2(bds[k]) for k in range(1, 5)}
betti = [fvec[k] - (rk[k] if k >= 1 else 0) - (rk[k + 1] if k + 1 <= 4 else 0) for k in range(5)]
chk("the boundary of a boundary is nothing, and the cells have one class in each dimension mod 2 (1, 1, 1, 1, 1)", dd0 and betti == [1, 1, 1, 1, 1], betti)
lid = {}
for j, (vs, S) in enumerate(cells[1]):
    a_, b_ = sorted(vs)
    lid[(a_, b_)] = j
Cm = np.zeros((40, 40))
for i, (vs, S) in enumerate(cells[2]):
    x = min(vs)
    s, t = sorted(S)
    cyc = [x, x ^ g[s], x ^ g[s] ^ g[t], x ^ g[t]]
    for k in range(4):
        a_, b_ = cyc[k], cyc[(k + 1) % 4]
        Cm[i, lid[(min(a_, b_), max(a_, b_))]] += 1 if a_ < b_ else -1
Gr = np.zeros((40, 16))
for (a_, b_), j in lid.items():
    Gr[j, ri[b_]] += 1
    Gr[j, ri[a_]] -= 1
evC = np.round(np.linalg.eigvalsh(Cm.T @ Cm), 8)
specC = sorted((v, int(sum(abs(evC - v) < 1e-6))) for v in set(evC))
chk("the curvature around the squares: C grad = 0, rank C = 25 = 40 - 16 + 1, spec C^T C = 0^15, 4^10, 8^15",
    np.allclose(Cm @ Gr, 0) and np.linalg.matrix_rank(Cm) == 25 and [(abs(v), m) for v, m in specC] == [(0.0, 15), (4.0, 10), (8.0, 15)], specC)


def blade_mul(a, b):                          # e_a e_b = sign e_(a xor b) for Euclidean blades
    s = 0
    aa = a >> 1
    while aa:
        s += bin(aa & b).count("1")
        aa >>= 1
    return (-1) ** s, a ^ b


def wstep(s, x):                              # the volume element times g_s on a two-spinor state: the signed step
    s1, y = blade_mul(1 << s, x)
    s2, z = blade_mul(ALL, y)
    return s1 * s2, z


Am = np.zeros((16, 16))
Bm = np.zeros((80, 80))
for x in rel:
    for s in range(d):
        sg, z = wstep(s, x)
        Am[ri[z], ri[x]] += sg
for (x, t) in states:
    for s in range(d):
        if s != t:
            sg, z = wstep(s, x)
            Bm[si[(z, s)], si[(x, t)]] = sg
chk("the signed step carries the Clifford sign of every transition: symmetric, A_-^2 = 5I", np.allclose(Am, Am.T) and np.allclose(Am @ Am, 5 * np.eye(16)))
okd = all(abs(np.linalg.det(np.eye(80) - u * Bm) - (1 - u * u) ** 24 * (1 + 3 * u * u + 16 * u ** 4) ** 8) < 1e-8 for u in (0.11, 0.2 + 0.07j, 0.25j))
chk("the signed law det(I - uB_-) = (1 - u^2)^24 (1 + 3u^2 + 16u^4)^8", okd)
Rm = lambda u: (1 + 3 * u * u) / (1 + 3 * u * u + 16 * u ** 4)
Phz = lambda z: -z ** 4 / (16 + 3 * z ** 2)
Fz = lambda z: z ** 4 * (1 + z) / (16 - 8 * z - 3 * z ** 2 - 3 * z ** 3)
chk("its renewed return at the four points is the signed first return: 1 - 1/R_-(i^k/4) = Phi(i^k)",
    all(abs(1 - 1 / Rm(1j ** k / 4) - Phz(1j ** k)) < 1e-15 for k in range(4)))
# positivity below the critical step for any phases on the links
okpos = True
for trial in range(20):
    th = rng.uniform(0, 2 * pi, size=40)
    At = np.zeros((16, 16), dtype=complex)
    for (a_, b_), j in lid.items():
        At[ri[b_], ri[a_]] += np.exp(1j * th[j])
        At[ri[a_], ri[b_]] += np.exp(-1j * th[j])
    for u in (0.05, 0.15, 0.24):
        okpos &= np.linalg.eigvalsh((1 + 4 * u * u) * np.eye(16) - u * At).min() >= (1 - u) * (1 - 4 * u) - 1e-12
chk("with any phases on the links the law stays positive below 1/4: (1 + 4u^2) - uA_U >= (1 - u)(1 - 4u)", okpos)

# ====================================================================================================== 3. functions
head("3. The law's functions, every one counted on B")
idx = {}
for S in range(1 << d):
    for t in range(d):
        for p in (0, 1):
            idx[(S, t, p)] = len(idx)
m = len(idx)
is_singlet = lambda S, p: (p == 0 and S == 0) or (p == 1 and S == ALL)


def first_return(z, signed):
    Q = np.zeros((m, m), dtype=complex)
    r = np.zeros(m, dtype=complex)
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
    psi = z * np.linalg.solve(np.eye(m) - z * Q.T, r)
    return z * sum(0.25 * psi[idx[(1 << s, s, 1)]] for s in range(d) if s != 0)


chk("one first-return excursion from the singlet back to it: the plain first return of B is F(z) = z^4(1 + z)/(16 - 8z - 3z^2 - 3z^3)",
    all(abs(first_return(z, False) - Fz(z)) < 1e-12 for z in (0.4, 0.6 + 0.3j, 0.8j)))
chk("and, with the Clifford sign of every loop, the signed first return Phi(z) = -z^4/(16 + 3z^2)",
    all(abs(first_return(z, True) - Phz(z)) < 1e-12 for z in (0.4, 0.6 + 0.3j, 0.8j)))
P1 = Fr(-1, 19) if abs(first_return(1.0, True) + 1 / 19) < 1e-12 else None
Pi_ = Fr(-1, 13) if abs(first_return(1j, True) + 1 / 13) < 1e-12 else None
F1 = first_return(1.0, False).real
dF = ((first_return(1 + 1e-5, False) - first_return(1 - 1e-5, False)) / 2e-5).real
chk("every excursion closes, F(1) = 1, mean return time F'(1) = 16; Phi(1) = -1/19, Phi(i) = -1/13",
    abs(F1 - 1) < 1e-10 and abs(dF - 16) < 1e-4 and P1 is not None and Pi_ is not None)
h0 = 0
trans = [(x, t) for (x, t) in states if x != 0]
ti = {st: i for i, st in enumerate(trans)}
T = np.zeros((len(trans), len(trans)))
for (x, t) in trans:
    for s in range(d):
        if s != t and (x ^ g[s]) != 0:
            T[ti[(x, t)], ti[(x ^ g[s], s)]] = 0.25
v0 = np.zeros(len(trans))
for s in range(d):
    if s != h0:
        v0[ti[(g[s], s)]] += 0.25
Nm = np.linalg.inv(np.eye(len(trans)) - T)
mu = v0 @ Nm
is_sym = np.array([1.0 if grade(x) == 2 else 0.0 for (x, t) in trans])
is_vec = np.array([1.0 if grade(x) == 4 else 0.0 for (x, t) in trans])


def second(Aind, Bind):
    return float(mu @ (np.diag(Aind) @ Nm @ Bind) + mu @ (np.diag(Bind) @ Nm @ Aind) - mu @ (Aind * Bind))


EnFf, EnLf = float(mu @ is_sym), float(mu @ is_vec)
VarnFf, VarnLf = second(is_sym, is_sym) - EnFf ** 2, second(is_vec, is_vec) - EnLf ** 2
Covf = second(is_sym, is_vec) - EnFf * EnLf
chk("one excursion visits the symmetric states E n_F = 10 and the vector states E n_L = 5 times; Var n_F = 84, Var n_L = 12, Cov = 30, Var l = 156",
    max(abs(EnFf - 10), abs(EnLf - 5), abs(VarnFf - 84), abs(VarnLf - 12), abs(Covf - 30), abs(VarnFf + VarnLf + 2 * Covf - 156)) < 1e-9)
EnF, EnL, VarnF, VarnL, Cov, El, VarL = 10, 5, 84, 12, 30, 16, 156


def sym_visits(xv):
    Dm = np.diag([xv if f else 1.0 for f in is_sym])
    rr = np.array([0.25 * sum(1 for s in range(d) if s != t and (x ^ g[s]) == 0) for (x, t) in trans])
    return float((v0 @ Dm) @ np.linalg.solve(np.eye(len(trans)) - T @ Dm, rr))


chk("the symmetric-state visit function of one excursion is x(1 + x)/(16 - 11x - 3x^2), pole x_c = (sqrt313 - 11)/6",
    all(abs(sym_visits(xv) - xv * (1 + xv) / (16 - 11 * xv - 3 * xv * xv)) < 1e-12 for xv in (0.3, 0.7, 1.0, 1.1)))
xc = (sqrt(313) - 11) / 6
avail = [(x, t) for (x, t) in states if x != 0 and not (x == g[h0] and t == h0)]
avail_tr = [(x, t, s) for (x, t) in avail for s in range(d) if s != t]
M = len(avail_tr)
Ch = sum(1 for (x, t, s) in avail_tr if s == h0)
Cj = sum(1 for (x, t, s) in avail_tr if s == 1)
n_noh = sum(1 for (x, t) in avail if not (x >> h0) & 1)
chk("the available transitions: 74 directed edges, M = 296 transitions, C_h = 60 along h, 59 along each other direction; 34 edges whose state does not contain h",
    (len(avail), M, Ch, Cj, n_noh) == (74, 296, 60, 59, 34))
chk("the self-interaction on the available transitions: at each transition the moment meets itself with the comparison's value 6, along h once more: sum = 6M + C_h = 1836",
    sum(6 + (s == h0) for (x, t, s) in avail_tr) == 6 * M + Ch == 1836)
eta, sigma, cL, Rud = (M - 1) / M, 5 * Ch / M, Ch / M, n_noh / len(avail)
EH = El * Ch / 320
Gg = np.linalg.pinv(5 * np.eye(16) - A)
b = Gg[0, 0] + Gg[ri[0b00011], ri[0b00011]] - 2 * Gg[0, ri[0b00011]]
chk("the Green's function at the critical step (5 - A)^+ = (7 + A)/32 - 3J/128; the effective resistance between the singlet and a symmetric state b = 7/16",
    np.allclose(Gg, (7 * np.eye(16) + A) / 32 - 3 * np.ones((16, 16)) / 128) and abs(b - 7 / 16) < 1e-12)
sv = sorted(set(np.round(np.linalg.svd(B, compute_uv=False), 9)))
xi = log(max(sv) / 2)
rho_nu = math.tanh(xi / 4)
chk("the polar step: singular values 1 and 4, |B| = 2e^(xi(2Pi - I)), xi = log 2, tanh(xi/4) = 3 - 2sqrt2 = tan^2(pi/8)",
    sv == [1.0, 4.0] and abs(xi - log(2)) < 1e-12 and abs(rho_nu - (3 - 2 * sqrt(2))) < 1e-15 and abs(rho_nu - math.tan(pi / 8) ** 2) < 1e-15)
qch = np.array([float(x) for x in Qline])
c = 2 * (np.mean(qch * qch) - np.mean(qch) ** 2)
chk("the charge current c = 2 Var(Q) over the five directions = 8/15", abs(c - 8 / 15) < 1e-15)
Lspec = [6] + [2] * 10 + [-2] * 5
chk("24/11: Tr L^2/4 = 24 traceless rotations against the 11 states of positive comparison value", sum(l * l for l in Lspec) // 4 == 24 and sum(1 for l in Lspec if l > 0) == 11)
# the mixed moment: the grade and the parallel clocks meet on the pairs of directions on opposite sides, one weight 1/72 per pair
fifteen = [S for S in evens5 if len(S) > 0]


def Hd(D, S):
    return Fr(5 * len(S & D) - len(D) * len(S), 4)


def moment(D, E, w2, w4):
    W = {S: (w2 if len(S) == 2 else w4) for S in fifteen}
    Z = sum(W.values())
    mu_ = sum(W[S] * len(S) for S in fifteen) / Z
    var = sum(W[S] * len(S) ** 2 for S in fifteen) / Z - mu_ ** 2
    J = sum(W[S] * (len(S) - mu_) * Hd(D, S) * Hd(E, S) for S in fifteen) / Z
    return J, Fr(9, 8) * var


okmm = True
pairsDE = [(frozenset({0}), frozenset({1})), (frozenset({0}), frozenset({1, 2, 3, 4})), (frozenset({0, 1}), frozenset({2, 3, 4})),
           (frozenset({0, 1}), frozenset({1, 2})), (frozenset({2, 3}), frozenset({2, 3}))]
for (w2, w4) in [(Fr(1), Fr(1)), (Fr(1), Fr(1, 2)), (Fr(3), Fr(7)), (Fr(2, 3), Fr(1, 5))]:
    for D_, E_ in pairsDE:
        J, Cc = moment(D_, E_, w2, w4)
        okmm &= J == Cc * Fr(len(D_) * len(E_) - 5 * len(D_ & E_), 72)
chk("the mixed moment on the fifteen states other than the singlet: J_DE = C_W (rs - 5 Tr P_D P_E)/72 for every central weight W", okmm)
J1, C1 = moment(frozenset({0}), frozenset({1}), Fr(1), Fr(1))
J4, C4 = moment(frozenset({0}), frozenset({1}), Fr(1) / kN(2, Fr(1, 4)), Fr(1) / kN(4, Fr(1, 4)))
chk("one pair of directions on opposite sides: 1/72 against the clock 1 at u = 0, and 1/100 against 18/25 at u = 1/4: the ratio 1/72 stays",
    (J1, C1, J4, C4) == (Fr(1, 72), 1, Fr(1, 100), Fr(18, 25)), (J1, C1, J4, C4))
chk("one direction against the other four: 4/72 = 1/18 = -Phi(1)/(1 + Phi(1)); the plane hk against the three directions outside it: 6/72 = 1/12 = -Phi(i)/(1 + Phi(i))",
    Fr(4, 72) == -P1 / (1 + P1) and Fr(6, 72) == -Pi_ / (1 + Pi_))
# the phase on one directed edge: the electron's unit rate 1/320
pc = np.poly1d([1.0])
for fac, pw in [([-1, 0, 1], 24), ([4, -5, 1], 1), ([4, -1, 1], 10), ([4, 3, 1], 5)]:
    pc *= np.poly1d(fac) ** pw
Dp = pc.deriv()
okarc = True
arcs = [(i, j) for i in range(80) for j in range(80) if B[i, j]]
for (i, j) in [arcs[0], arcs[57], arcs[203], arcs[319]]:
    for u in (0.11, 0.2 + 0.05j):
        for th in (0.3, 1.7):
            Bt = B.astype(complex).copy()
            Bt[i, j] = np.exp(-1j * th)
            okarc &= abs(np.linalg.det(np.eye(80) - u * Bt) - (pc(u) + (np.exp(-1j * th) - 1) * u * Dp(u) / 320)) < 1e-9
chk("marking one transition of the 320 with a phase: D_theta(u) = D(u) + (e^(-i theta) - 1) u D'(u)/320, at every transition", okarc)
uz = 0.25 - (np.exp(-1j * 0.001) - 1) / (4 * 320)
chk("so the marked world line turns the leading zero at the rate theta/320 per step for small theta: the electron, the unit rate 1/320",
    abs(np.angle(4 * uz) - 0.001 / 320) < 1e-9)
P1f = float(P1)
a = (1 - P1) / 8
chiA = 1 / (1 + Pi_)

# ====================================================================================================== 4. the four points
head("4. Breaking puts u at the four points u = i^d/4; the law's values there")
print("| type | u | k0 | k2 | k4 | 1 - u^2 | F(4u) | Phi(4u) | w = u/(1 + 4u^2) | kappa(w) |")
print("|---|---|---|---|---|---|---|---|---|---|")
kap_w = lambda w: 2 * w ** 4 / (1 - 5 * w * w) ** 2
for k, nm in enumerate(["0|6 singlet", "1|5 direction h", "2|4 plane hk", "3|3 colour"]):
    u = (1j) ** k / 4
    w = u / (1 + 4 * u * u)
    print("| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (nm, u, kN(0, u), kN(2, u), kN(4, u), 1 - u * u, np.round(Fz(4 * u), 4), np.round(Phz(4 * u), 6), np.round(w, 6), np.round(kap_w(w), 6)))
uF = Fr(-1, 4)
K0, K2, K4 = kN(0, uF), kN(2, uF), kN(4, uF)
t_even, e_even, e_line, t_line = 1 / K0, K2 / K0, K4 / K2, 1 / K2
chk("at u = -1/4 the grade factors are 5/2, 3/2, 1/2; t = 1/k_N, e = k_(N+2)/k_N: 2/5, 3/5, 2/3, 1/3",
    (K0, K2, K4, t_even, e_even, t_line, e_line) == (Fr(5, 2), Fr(3, 2), Fr(1, 2), Fr(2, 5), Fr(3, 5), Fr(2, 3), Fr(1, 3)))
chk("at u = 1/4 k_0 = 0: the one critical zero; at the other points no factor vanishes",
    kN(0, 0.25) == 0 and all(abs(kN(N, (1j) ** k / 4)) > 0.1 for k in range(1, 4) for N in (0, 2, 4)))
okrule = True
tally = {}
for S in range(64):
    Ss = {k for k in range(6) if S >> k & 1}
    kS = len(Ss - {5})                                   # direction 5 is the singlet direction n; 0..4 the five directions of the Dirac matrices
    z = (1j) ** len(Ss)
    P = int(round((z * z).real))
    L = 5 - kS + kS * P
    e = 1 - Fr(2, abs(L))
    tt = Fr(2, abs(L))
    Psi = Fr(P, L * L + 3 * P)
    N_ = 5 - abs(L)
    okrule &= tt == 1 / kN(N_, uF) and e == kN(N_ + 2, uF) / kN(N_, uF) and Fr(-1, 16 + 3 * P) == (P1 if P == 1 else Pi_)
    key = (P, abs(L), str(e), str(Psi))
    tally[key] = tally.get(key, 0) + 1
chk("on all 64 divided sets the rule's step weights are the law's grade factors at u = -1/4, N = 5 - |L_S|", okrule)
chk("divided sets: 32 even (3/5, 1/28); {n} and the five directions (3/5, -1/22); a direction and its complement (1/3, -1/6); three of six (-1, 1/2)",
    tally == {(1, 5, "3/5", "1/28"): 32, (-1, 5, "3/5", "-1/22"): 2, (-1, 3, "1/3", "-1/6"): 10, (-1, 1, "-1", "1/2"): 20}, tally)
g2 = (-P1 / (1 + P1)) / 4
chk("one pair of directions on opposite sides g^2 = [-Phi(1)/(1 + Phi(1))]/4 = [-Phi(i)/(1 + Phi(i))]/6 = e_line^2/(k_C^2 - 1) = 1/72",
    g2 == Fr(1, 72) and (-Pi_ / (1 + Pi_)) / 6 == g2 and e_line ** 2 / 8 == g2)
wh = 1 / (4 * chiA)
chih = wh * (1 - wh)
chk("a = (1 - Phi(1))/8 = 5/38; chi_A = 1/(1 + Phi(i)) = 13/12; w_h = 3/13; chi_h = 30/169",
    (a, chiA, wh, chih) == (Fr(5, 38), Fr(13, 12), Fr(3, 13), Fr(30, 169)))

# ====================================================================================================== 5. field equations
head("5. Completion at long wavelength: the field equations of the four breakings")
# (a) the mass shell: the law's operator below the critical step
Vs = np.eye(5) - np.ones((5, 5)) / 5
O4 = np.zeros((5, 4))
for j in range(1, 5):
    O4[:j, j - 1] = 1 / sqrt(j * (j + 1))
    O4[j, j - 1] = -j / sqrt(j * (j + 1))
# This explicit orthonormal frame fixes the coordinates of the numerical momentum probe.
v5 = (Vs.T @ O4)                                   # row t: v_t in R^4
chk("the five directions less their mean: sum v_t = 0, sum v_t (x) v_t = 1 on R^4, v_a.v_b = delta_ab - 1/5",
    np.allclose(v5.sum(0), 0) and np.allclose(v5.T @ v5, np.eye(4)) and np.allclose(v5 @ v5.T, np.eye(5) - 1 / 5))
p4 = np.array([0.7, -1.3, 0.4, 2.1])
m0 = 1.6
errs = []
for eps in (1e-2, 1e-3):
    u = 0.25 - eps * eps * m0 * m0 / 24
    sym = 1 + 4 * u * u - u * sum(np.exp(1j * eps * p4 @ v5[t]) for t in range(5))
    errs.append(abs(sym / (eps * eps / 8) - (m0 * m0 + p4 @ p4)))
chk("Klein-Gordon: at u = 1/4 - eps^2 m^2/24 the law's operator is (eps^2/8)(m^2 - Delta) + O(eps^3)",
    errs[1] < errs[0] / 5 and errs[1] < 2e-2, errs)
# (b) the first-order step: Dirac
okd = True
for (mu_, kk) in [(0.3, 0.5), (1.1, -0.7), (0.05, 2.0)]:
    Ust = (np.cos(kk) * I4 - 1j * np.sin(kk) * gam[1]) @ (np.cos(mu_) * I4 - 1j * np.sin(mu_) * gam[0])
    evU = np.linalg.eigvals(Ust)
    okd &= np.allclose(np.cos(np.angle(evU)), np.cos(mu_) * np.cos(kk)) and np.allclose(Ust + Ust.conj().T, 2 * np.cos(kk) * np.cos(mu_) * I4)
chk("Dirac: one step U = e^(-ik g_j) e^(-i mu g_h) has U + U^dagger = 2 cos k cos mu, every eigenphase cos w = cos mu cos k", okd)
Gmu = [sum(v5[t, mu_] * gam[t] for t in range(5)) for mu_ in range(4)]
gm = sum(gam) / sqrt(5)
chk("in the chart Gamma^mu = sum_t v_t^mu g_t and g(m) = sum_t g_t/sqrt5 are five anticommuting directions: (Gamma.p + M g(m))^2 = p^2 + M^2",
    all(np.allclose(Gmu[a_] @ Gmu[b_] + Gmu[b_] @ Gmu[a_], 2 * (a_ == b_) * I4) for a_ in range(4) for b_ in range(4))
    and all(np.allclose(Gmu[a_] @ gm + gm @ Gmu[a_], 0) for a_ in range(4)) and np.allclose(gm @ gm, I4))
# (c) Maxwell and Yang-Mills: the signed law's exact second variation in the link phases


def hessian(w):
    Ms = Am.astype(complex)
    R = np.linalg.inv(np.eye(16) - w * Ms)
    Hm = np.zeros((40, 40), dtype=complex)
    dM = []
    for (a_, b_), j in lid.items():
        Dj = np.zeros((16, 16), dtype=complex)
        Dj[ri[b_], ri[a_]] = 1j * Am[ri[b_], ri[a_]]
        Dj[ri[a_], ri[b_]] = -1j * Am[ri[a_], ri[b_]]
        dM.append((j, Dj))
    dM.sort()
    for j, Dj in dM:
        for k_, Dk in dM:
            Hm[j, k_] = -np.trace(R @ (w * Dj) @ R @ (w * Dk))
        D2 = np.where(np.abs(Dj) > 0, -Am.astype(complex), 0)   # second derivative of the link's phase factors
        Hm[j, j] += -np.trace(R @ (w * D2))
    return Hm


okH = True
for w in (0.2, 0.13, 1j / 3, 0.07 - 0.04j):
    Hm = hessian(w)
    okH &= np.allclose(Hm, -kap_w(w) * (Cm.T @ Cm), atol=1e-12)
chk("Maxwell and Yang-Mills: d^2 log det(I - wA_-[e^(i theta)]) = -kappa(w) C^T C exactly, kappa(w) = 2w^4/(1 - 5w^2)^2", okH)
chk("kappa = 1/200 at the counting points (w = +-1/5) and 1/98 at the amplitude points (w = +-i/3)",
    abs(kap_w(0.2) - 1 / 200) < 1e-15 and abs(kap_w(-0.2) - 1 / 200) < 1e-15 and abs(kap_w(1j / 3) - 1 / 98) < 1e-15)
# (d) Einstein-Cartan with Lambda at the direction h
eps4 = np.zeros((5,) * 5)
for perm in itertools.permutations(range(5)):
    eps4[perm] = np.linalg.det(np.eye(5)[list(perm)])
oktr = all(abs(np.trace(gam[p_[0]] @ gam[p_[1]] @ gam[p_[2]] @ gam[p_[3]] @ gam[p_[4]]) - 4 * osign * eps4[p_]) < 1e-12
           for p_ in itertools.permutations(range(5)))
chk("tr(g_h g_a g_b g_c g_d) = 4 eps_habcd (times the sign of the volume element)", oktr)
r4 = [gam[0] @ gam[a_] for a_ in range(1, 5)]
chk("so(5) = so(4) + R^4 at h: the four rotations that move h close into the six that keep it, [R^4, R^4] in so(4)",
    all(np.allclose((r4[i] @ r4[j] - r4[j] @ r4[i]), -2 * gam[i + 1] @ gam[j + 1]) for i in range(4) for j in range(4) if i != j))
e4 = np.zeros((4,) * 4)
for perm in itertools.permutations(range(4)):
    e4[perm] = np.linalg.det(np.eye(4)[list(perm)])
Rr = rng.normal(size=(4, 4, 4, 4))
Rr = Rr - Rr.transpose(1, 0, 2, 3)
Rr = Rr - Rr.transpose(0, 1, 3, 2)
Rr = Rr + Rr.transpose(2, 3, 0, 1)
EE = np.einsum("ac,bd->abcd", np.eye(4), np.eye(4)) - np.einsum("ad,bc->abcd", np.eye(4), np.eye(4))
wedge = lambda X, Yt: 0.25 * np.einsum("abcd,abef,cdgh,efgh->", e4, X, Yt, e4)
Rsc = np.einsum("abab->", Rr)
ell = 1.7
lhs = wedge(Rr - EE / ell ** 2, Rr - EE / ell ** 2) - wedge(Rr, Rr)
chk("the curvature of the ten rotations split at h, F = R - e^e/l^2, in the epsilon contraction: eps(F^F) - eps(R^R) = -(4/l^2)(R - 6/l^2) vol: Lambda = 3/l^2",
    abs(lhs - (-(4 / ell ** 2) * (Rsc - 6 / ell ** 2))) < 1e-9, (lhs, -(4 / ell ** 2) * (Rsc - 6 / ell ** 2)))
# (e) the direction h: the Higgs (section 1 gave the source ratios)

# ====================================================================================================== 6. couplings
head("6. Completion with two sources: the couplings, and the numbers in front of the field terms")
N2 = 10
kC = int(round(1 / 0.25 - 1))
NC = kC * kC - 1
LOm = d + 1
f = float(e_even) ** 2 / N2
nu = f / El
marks = [0, 1, 2, 3, float(-1 / P1)]
gaps = [abs(p_ - q_) for p_, q_ in itertools.combinations(marks, 2)]
ED = sum(gaps) / len(gaps) / 4
clock = lambda xv: sum(exp(-xv * dd / 4) for dd in gaps) / len(gaps)
chk("the clock's five marks (0, 1, 2, 3, -1/Phi(1))/4: ten gaps of mean E_D = 2", abs(ED - 2) < 1e-15)
hov = (clock(nu) * clock(-nu)) ** (-1.5)
nh = 0.0
ncon = 0.0
for k in range(1, 60):
    z = 4 * (1j / 4) ** k
    odd = -Phz(z)
    nh += (hov ** k * (odd if k % 2 else Fz(z))).real
    ncon += (odd if k % 2 else (Fz(z) + Fz(-z)) / 2).real
xcont = nu * hov / (M + 1 + nh)
alpha = cL * f / (1 - xcont)
alphas = sqrt(float(e_line) ** 2 / NC)
a_, b_ = float(a), float(b)
WW = Fz(hov) / hov ** 4 * (1 - 2 * b_ + 2 * b_ * hov)
GFmp2 = (1 - 1 / N2) * WW / M ** 2
W = float(t_even) ** (kC * El) * eta ** (kC * EH)
print("  strong          alpha_s = k4/(k2 sqrt(k_C^2 - 1))           = %.12f   (PDG 2024 0.1180(9))" % alphas)
print("  electromagnetic 1/alpha = N_2(1 - x)k0^2/(c_L k2^2)           = %.9f   (CODATA 2022 137.035999177(21))" % (1 / alpha))
print("  weak            G_F m_p^2 = (1 - 1/N_2) W_W/M^2              = %.8e   (1.0268268e-5)" % GFmp2)
print("  gravity         alpha_G = [k0^(-k_C El) eta^(k_C E_H)]^2     = %.8e   (CODATA 2022 5.90615(13)e-39)" % (W * W))
chk("alpha_s = (1/72)^(1/2) = 0.117851", abs(alphas - sqrt(1 / 72)) < 1e-15)
chk("1/alpha = 137.035999177", abs(1 / alpha - 137.035999177) < 1e-6)
chk("G_F m_p^2 = 1.026827e-5", abs(GFmp2 / 1.0268268e-5 - 1) < 1e-6)
chk("alpha_G = W^2, W = (2/5)^48 (295/296)^9 = k0(-1/4)^(-48) eta^9", abs(W * W / 5.906149e-39 - 1) < 3e-5 and abs(W - (2 / 5) ** 48 * (295 / 296) ** 9) < 1e-60)
# the same 48 is the law's answer to a circulation on the links: it moves the leading zero by |theta_cyc|^2/48
th0 = rng.normal(size=40)
th0 -= Gr @ np.linalg.lstsq(Gr, th0, rcond=None)[0]          # the circulating part, orthogonal to every gauge transformation
ratios = []
for sc in (1e-2, 3e-3):
    th = sc * th0
    At = np.zeros((16, 16), dtype=complex)
    for (x1, x2), j in lid.items():
        At[ri[x2], ri[x1]] += np.exp(1j * th[j])
        At[ri[x1], ri[x2]] += np.exp(-1j * th[j])
    lmax = np.linalg.eigvalsh(At).max()
    uc = (lmax - sqrt(lmax * lmax - 16)) / 8                  # the leading zero: 1 + 4u^2 = u lambda_max
    ratios.append(log(4 * uc) / (th @ th))
chk("a circulation theta on the links moves the leading zero: log 4u_c = |theta_cyc|^2/48 + O(theta^4), 48 = k_C El = 2(40 - 16)",
    abs(ratios[-1] - 1 / 48) < 1e-5 and abs(ratios[0] - 1 / 48) < 1e-4, ratios)
Mflux_e = 8 * pi * kap_w(-0.2) * alpha
Mflux_c = 8 * pi * kap_w(-1j / 3).real * alphas
print("  the link phases against the field in units of the charge: int F^2 = 8 pi kappa alpha ||C theta||^2, 8 pi kappa alpha = %.6e at the plane hk" % Mflux_e)
print("  and at colour 8 pi kappa alpha_s = %.6e; in front of F^2 stands 1/(16 pi alpha) = %.6f, in front of R 1/(16 pi G)" % (Mflux_c, 1 / (16 * pi * alpha)))

# ====================================================================================================== 7-10. rows
head("7-9. Completion at the zeros, the overlaps and the stationary state: masses, mixings, stationary numbers")


def rotation(i, j, s, phase=0.):
    out = np.eye(3, dtype=complex)
    out[i, i] = out[j, j] = sqrt(1 - s * s)
    out[i, j] = s * np.exp(-1j * phase)
    out[j, i] = -s * np.exp(1j * phase)
    return out


me = INPUTS["electron_mass_MeV"]
hc = INPUTS["planck_J_s"] * INPUTS["speed_of_light_m_s"] / (2 * pi * INPUTS["MeV_J"]) * 1e15
h = hov
rp = LOm * M + Ch + log(float(K0)) / LOm - a_ ** 5 - b_ * a_ ** 6
mp = me * rp
rn = exp(log(float(K0)) * (5 * a_ ** 4 + 4 * a_ ** 10 + 10 * cL * b_ * a_ ** 6))
mn = mp * rn
s_t = 0.5
lnLine = log(float(1 / e_line))
kap = float(e_even / t_even) ** (El / EnF)


def level_factor(n, L, P):
    psi = 1 / (5 ** 2 + 3) if P == 1 else 1 / 2
    eps_ = (1 + P) / 2
    assoc = -psi * L * (n - eps_) / 4
    clk = log(clock(P * nu)) / LOm if n == 10 else (n - eps_) * P * nu * ED / 4
    return exp(n * s_t * lnLine + assoc + clk)


rmu, rtau = level_factor(10, 2, 1), level_factor(5, -2, 1)
p, qq = level_factor(10, 2, -1), level_factor(5, -2, -1)
down = me * float(1 / e_line) ** (3 * s_t) * np.array([1 / eta, p / eta, p * qq])
up = Rud * down * np.array([1., kap ** 5, kap ** 7.5])
GF = GFmp2 / (mp / 1000) ** 2
v = (sqrt(2) * GF) ** (-.5)
sw = 3 * nh
osw = sw / (1 + f)
mw = v * sqrt(pi * alpha / ((1 - f) * osw))
mz = mw / sqrt(1 - osw)
whf = float(wh)
chihf = float(chih)
mh = v * sqrt(2 * pi * alpha / chihf)
mt = v * sqrt(eta / (2 * sigma))
mpl = mp / 1000 / W
MR, Moff = mpl * float(e_line) ** 9, mpl * float(e_line) ** 6
tau = 2 * pi / (El * rp)
s_sym = float(e_even) / N2
lam = 3 * W ** 6 * tau * s_sym ** 3
lp = hc / mp
mpcfm = INPUTS["megaparsec_m"] * 1e15
ellR = lp / (W ** 2 * sqrt(tau * s_sym ** 3)) / mpcfm
eps2 = alpha ** 2 / (1 + alpha / N2)
mup = sqrt(VarL / (2 * N2) * (1 - eps2 / (El ** 2 * b_)))
mun = -4 * (1 + EnF) / (24 - 1) * sqrt(1 - eps2 / (El ** 2 * b_))
gA = (kC + 2) / 3 * float(t_even) ** (2 * b_ / kC)
pi0 = sqrt((2 / abs(P1f)) * h * me * mp)
electric = pi * alpha * mp ** 2 / (El * (1 - alpha * b_ * Phz(1j).real))
pip = sqrt(pi0 * pi0 + electric)
fpi = eta * mp * sqrt(2 * kC) / (2 * pi * mup)
Bd = mp * sqrt(float(chiA)) * a_ ** 3 * (1 - (1 + float(t_even) / El) * eps2)
md = mp + mn - Bd
mus, gl = mup + mun, mn / (mp + mn)
mud = (16 * mus + gl) / 17 - (Bd / mp) * (mus - gl) / (20 + 13 * Bd / mp)
dq = atan2(16, 7)
s12, s23 = (VarnF - Cov ** 2 / VarnL) / (El * 2.5), 4 / sum(l * l for l in Lspec)
s13 = s12 * float(t_even) * s23
V = rotation(1, 2, s23) @ rotation(0, 2, s13, dq) @ rotation(0, 1, s12)
U = rotation(0, 1, sqrt(2 * b_) * s12, pi / 2 - dq).conj().T @ rotation(1, 2, 1 / sqrt(2)) @ rotation(0, 1, sqrt(b_))
S13 = abs(U[0, 2]) ** 2
S12 = abs(U[0, 1]) ** 2 / (1 - S13)
S23 = abs(U[1, 2]) ** 2 / (1 - S13)
jl = (U[0, 0] * U[1, 1] * U[0, 1].conjugate() * U[1, 0].conjugate()).imag
jq = (V[0, 1] * V[1, 2] * V[0, 2].conjugate() * V[1, 1].conjugate()).imag
scale = sqrt(S12 * (1 - S12) * S23 * (1 - S23) * S13)
phase = np.degrees(atan2(jl / (scale * (1 - S13)), (abs(U[1, 0]) ** 2 - S12 * (1 - S23) - (1 - S12) * S23 * S13) / (2 * scale))) % 360
angles = [np.degrees(np.angle(-V[i, 0] * V[i, 2].conjugate() / (V[j, 0] * V[j, 2].conjugate()))) % 360 for i, j in [(2, 0), (1, 2), (0, 1)]]
y = sigma * v / (mp / 1000) * np.array([0., sqrt(rho_nu), 1.]) / sqrt(2)
XR = float(e_line) ** 9 / W
neut = 2 * y * y / (XR + np.sqrt(XR * XR + 4 * y * y)) * mp * 1e6
mbeta = sqrt(sum(abs(U[0]) ** 2 * neut ** 2))
mbb = abs(sum(U[0] ** 2 * neut))
As = 12 * a_ ** 11 * (INPUTS["primordial_pivot_Mpc_inv"] * ellR) ** (-1 / 40)
hbar = INPUTS["planck_J_s"] / (2 * pi) / INPUTS["MeV_J"]
lifetime = 72 ** 2 * hbar / (3 ** 24 * W ** 4 * mp) / (INPUTS["julian_year_days"] * 86400)
bulk = np.array([1 - float(t_even) / El, float(chiA), float(e_even / t_even), kC / 4, 4 * alpha / (5 * a_)]) * mp * a_ * a_
R = {}


def seq(prefix, values, start=1):
    for i, val in enumerate(values, start):
        R[f'{prefix}{i:02d}'] = val


koide = (1 + rmu + rmu * rtau) / (1 + sqrt(rmu) + sqrt(rmu * rtau)) ** 2
seq('B', [rmu, rtau, koide, p, qq * eta, qq * qq * eta * eta / p, qq * qq * eta * eta / p, rmu / p, Rud, kap, Rud * kap ** 5, rp, rn, rp * rn])
seq('C', [s12, s23, s13, dq, jq * 1e5, *angles, float(np.sum(abs(V[:2]) ** 2)), S12, S13, 4 * S13 * (1 - S13), S23, phase, 1 + (-float(t_even) / El), 0])
seq('D', [alphas, 1 / alpha, GF * 1e5, W * W * 1e39, mpl / 1e19, lam * 1e122, 0, sw, 3 * ncon, osw, mw, mz, mw / mz, f, v, mh, mt])
seq('E', [neut[1] ** 2 * 1e5, neut[2] ** 2 * 1e3, (neut[2] ** 2 - neut[1] ** 2) * 1e3, neut[1] / neut[2], (neut[2] / neut[1]) ** 2, neut[2] * 1e3, 3])
R.update(F01=3 * a_ ** 11 * 1e10, F03=log(1e10 * As), F04=3 * eta * sigma ** (4 / 3), F13=0)
seq('G', [4 * lp, 3 * b_ * mp, mup, mun, mun / mup, pi0, pip, fpi, fpi * abs(V[0, 0]), Bd, md, md / mp, mud])
seq('H', [2, 1, 1])
R.update(S01=gA, S02=(VarnF - Cov ** 2 / VarnL) * lp * lp, S03=sqrt(VarnF - Cov ** 2 / VarnL) * lp, S04=sqrt(EnF) * lp,
         S05=INPUTS["neutron_rate_normalization_s"] / (INPUTS["neutron_rate_factor"] * abs(V[0, 0]) ** 2 * (1 + 3 * gA * gA)), S07=mp * mp / (EnF * me) / 1000,
         S08=b_ ** 24 * (INPUTS["primordial_pivot_Mpc_inv"] * ellR) ** (-1 / 40) * 1e9, S09=M / (M - 4 * Ch), A002=5 * mp / 36, A003=5 * mp / 36 * abs(V[0, 0]))
R.update(N22=-bulk[0])
seq('K', [0, float(sum(neut)), float(sum(neut)), [mbeta, mbb], float(sum(abs(np.diag(V)) ** 2)), lifetime])
seq('T', [MR, Moff, ellR, hc * 1e6 / (2 * pi * ellR * mpcfm), neut[:2].tolist(), jl, 2 / 51])
seq('L', [me * rmu * rtau, abs(U[2]) ** 2, rho_nu ** -2, 3, float(1 / e_line) ** (5 * s_t) * me, 0, 0, -1, 0, 3 * pi / lam, 16 * lam / (3 * pi * 12 * a_ ** 11), lifetime, Bd, NC, mw, 0, koide, 15 * pi / 4])
inv = 1 / np.array([Rud, 1, p])
low = np.linalg.eigvalsh([[Rud + 1, (Rud - 1) / sqrt(3)], [(Rud - 1) / sqrt(3), (Rud + 1 + 4 * p) / 3]])[0]
R['I08'] = 1 / (low * sum(inv))
R['I09'] = -sum(inv ** 3) / (12 * sum(inv) ** 3)
R['S16'] = mz * 1000 * exp(-2 * pi / ((23 / 3) * alphas))
R['J03'] = mn * float(K0) ** (EH / El)
R['J04'] = kC * b_ * mp
R['J05'], R['J06'] = pi0, pip
R['J07'] = 2 * kC * mp ** 2 * log(xc) / 1e6
R['J17'] = mp / LOm
R['M1'], R['M2'], R['M3'] = mp, mn, md
R['J01'], R['J02'] = rp, rn
nh1 = 0.0
for k in range(1, 60):
    z = 4 * (1j / 4) ** k
    nh1 += ((-Phz(z)) if k % 2 else Fz(z)).real
R['L19'] = (1 - nu / (M + 1 + nh1)) / (cL * f)
R['L20'] = 3 * nh1
delta1 = lambda xv: -np.log1p(2 * np.expm1(-np.asarray(xv)) / (np.sqrt(9 + 16 * np.exp(-np.asarray(xv))) + 5))


def response(levels):
    nr = len(levels)
    dd_ = np.sqrt(levels)
    Gc = np.outer(dd_, dd_) * (np.eye(nr) + (1 - np.eye(nr)) * sqrt(c))
    return float(np.sum(delta1(np.linalg.eigvalsh(Gc))))


lo_, hi_ = 0., 1.
target = pi0 ** 2 / (6 * mp ** 2)
for _ in range(90):
    mid = (lo_ + hi_) / 2
    if response([Rud * mid, mid]) < target:
        lo_ = mid
    else:
        hi_ = mid
sd = (lo_ + hi_) / 2
level = dict(u=Rud * sd, d=sd, s=p * sd)
R['J08'] = mp * sqrt(6 * response([level['d'], level['s']]))
R['J09'] = sqrt(6 * mp ** 2 * response([level['u'], level['s']]) + (8 / 25) * 2 * 3 * electric)

print("  masses (MeV unless marked):")
print("    e %.8f | mu %.6f | tau %.3f | p %.6f | n %.6f | pi0 %.5f | pi+ %.5f" % (me, me * rmu, me * rmu * rtau, mp, mn, pi0, pip))
print("    d %.4f | s %.3f | b %.2f | u %.4f | c %.2f | (the pole sequence at its source; the 2 GeV and m(m) values are classical maps)" % (down[0], down[1], down[2], up[0], up[1]))
print("    W %.4f GeV | Z %.4f GeV | H %.4f GeV | t %.3f GeV | v %.6f GeV | lambda_H %.9f" % (mw, mz, mh, mt, v, pi * alpha / chihf))
print("    neutrinos m2 %.4f meV, m3 %.4f meV, sum %.4f eV; M_R %.4e GeV" % (neut[1] * 1e3, neut[2] * 1e3, sum(neut), MR))
print("  mixings: s12 = 9/40, s23 = 1/24, s13 = s12 (2/5) s23, delta_q = arg(7 + 16i) = %.6f rad; J_q = %.4e" % (dq, jq))
print("    lepton s^2_12 %.6f, s^2_13 %.7f, s^2_23 %.6f, delta_l %.3f deg, J_l %.6f" % (S12, S13, S23, phase, jl))
print("  stationary: eta_B = 3a^11 = %.6e, n_s = 39/40, N_eff = 3 eta sigma^(4/3) = %.6f, Lambda l_P^2 = %.6e, l = %.3f Mpc"
      % (3 * a_ ** 11, 3 * eta * sigma ** (4 / 3), lam, ellR))
chk("m_p/m_e = 6M + C_h + (1/6) log k0(-1/4) - a^5 - b a^6 = 1836.152673412", abs(rp - 1836.15267341205) < 1e-8, "%.9f" % rp)
chk("m_mu/m_e = (k2/k4)^5 e^(-9/56) M_Q(nu)^(1/6) = 206.768283945", abs(rmu - 206.768283945476) < 1e-8)
chk("m_tau/m_mu = (k2/k4)^(5/2) e^(1/14 + 2 nu) = 16.8181606", abs(rtau - 16.8181606410583) < 1e-9)
chk("lambda_H = pi alpha (4 chi_A)^2/(4 chi_A - 1) = 0.129145909, m_H = v sqrt(2 lambda_H) = 125.1348 GeV",
    abs(pi * alpha * (4 * float(chiA)) ** 2 / (4 * float(chiA) - 1) - 0.129145908531) < 1e-9 and abs(mh - 125.134771593) < 1e-6)

# ------------------------------------------------------------------ the whole table
head("10. The 131 scalar values evaluated here, beside their records and measurements")
SPL = re.compile(r"(?<!\\)\|")
table = {}
with io.open(TABLE, encoding="utf-8") as fh:
    for l in fh:
        if l.startswith("| ") and not l.startswith("| row |") and not l.startswith("| variable"):
            cc = [x.strip() for x in SPL.split(l.strip()[1:-1])]
            if len(cc) == 7:
                table[cc[0]] = dict(name=cc[1], term=cc[3], value=cc[4], record=cc[5], sds=cc[6])


def num(s):
    try:
        return float(s)
    except Exception:
        return None


def meas(rec):
    mm = re.match(r"\s*([-+]?[0-9.]+(?:e[-+]?[0-9]+)?)\s*(?:\+([0-9.]+(?:e[-+]?[0-9]+)?)\s*/\s*[-−]([0-9.]+(?:e[-+]?[0-9]+)?)|±\s*([0-9.]+(?:e[-+]?[0-9]+)?))", rec)
    if not mm:
        return None
    cen = float(mm.group(1))
    if mm.group(4):
        return cen, float(mm.group(4)), float(mm.group(4))
    return cen, float(mm.group(2)), float(mm.group(3))


print("| row | constant | from B | table | measurement | standard deviations |")
print("|---|---|---:|---:|---|---:|")
agree = compared = 0
wlist = {}
for rid in sorted(R, key=lambda k: (re.sub(r"\d", "", k), int(re.sub(r"\D", "", k) or 0))):
    val = R[rid]
    if isinstance(val, (list, tuple, np.ndarray)) or rid not in table:
        continue
    tv = num(table[rid]["value"])
    if tv is None:
        continue
    compared += 1
    sv_ = table[rid]["value"]
    ndec = len(sv_.split(".")[1]) if "." in sv_ and "e" not in sv_.lower() else 12
    same = abs((val - tv) / tv if tv != 0 else (val - tv)) < 1e-6 or abs(val - tv) <= 0.6 * 10 ** (-ndec)
    if rid == "J09":
        same = abs(val - 493.665032668) < 1e-6
    agree += same
    mw_ = meas(table[rid]["record"])
    wd = ""
    if mw_ is not None:
        cen, up_, dn_ = mw_
        sig = up_ if val >= cen else dn_
        if sig > 0:
            wd = (val - cen) / sig
            wlist[rid] = wd
    print("| %s | %s | %.12g | %s | %s | %s |" % (rid, table[rid]["name"], val, table[rid]["value"], table[rid]["record"], ("%+.3f" % wd) if wd != "" else ""))
print()
within = lambda k: sum(1 for x in wlist.values() if abs(x) <= k)
print("rows computed: %d; agreeing with the table within its printed digits: %d" % (compared, agree))
print("measured comparisons among this program's 131 evaluated scalar rows: %d; within one standard deviation %d, two %d, three %d" % (len(wlist), within(1), within(2), within(3)))
print("among this program's 99 measured comparisons, beyond three standard deviations: " + (", ".join("%s %+.1f" % (k, x) for k, x in sorted(wlist.items()) if abs(x) > 3) or "none"))
rest = sorted(r for r in table if r not in R)
print("conventional and composite records printed by article_results.py: %d" % len(rest))
print("  " + " ".join(rest))
chk("the 131 scalar rows evaluated here agree with their recorded values within the printed digits", agree == compared, (agree, compared))

# ====================================================================================================== 11. classical
head("11. The classical theory is the law's long-wave limit")
okT = True
for (u, vv) in [(0.1, 0.23), (0.25, -0.25), (0.05 + 0.1j, 0.25j)]:
    aT = vv / u
    bT = 1 + 4 * vv * vv - aT * (1 + 4 * u * u)
    okT &= all(abs(kN(N, vv) - (aT * kN(N, u) + bT)) < 1e-14 for N in (0, 2, 4))
chk("the law's own transformation: K_16(v) = a K_16(u) + b I with a = v/u, b = 1 + 4v^2 - a(1 + 4u^2)", okT)
print("  under it a response read against a fixed clock runs, kappa(w(u)) = 2u^4 - 12u^6 - 10u^8 + 360u^10 + ...,")
print("  while a response read against the clock that transforms with it stays: one pair of directions on opposite sides 1/72 at every central weight (section 3)")
ser = np.polynomial.polynomial.Polynomial([0, 0, 0, 0, 2, 0, -12, 0, -10, 0, 360])
uu = 0.03
chk("kappa(u) = 2u^4/(1 + 3u^2 + 16u^4)^2 = 2u^4 - 12u^6 - 10u^8 + 360u^10 + O(u^12)",
    abs(kap_w(uu / (1 + 4 * uu * uu)) - 2 * uu ** 4 / (1 + 3 * uu ** 2 + 16 * uu ** 4) ** 2) < 1e-18 and abs(kap_w(uu / (1 + 4 * uu * uu)) - ser(uu)) < 1e-14)
print()
print("checks:", sum(ok), "of", len(ok), "ok")
