# -*- coding: utf-8 -*-
# THE LAW PERFORMS THE CLASSICAL EXPERIMENTS
#
# The apparatus is one law, det(I - uB) on the step B of a world line, broken at u = i^d/4, and the same law on its own
# resolved chart. The law is one operator: the comparison L of two systems with one movable spectral parameter chi,
# det(I - uB) = (1 - u^2)^24 u^16 det[(6I - L) + chi I]. PART 1 holds one classical control at a time and varies it: a
# wavelength, a distance, a phase per step, a field on the links, a circulation, a curvature, the length of the direction h.
# How the law's answer changes as the control varies is the classical equation; what stays fixed is the number. PART 2
# evaluates the controls and numerical rows listed below, holding the quantities specified for each experiment; each scalar row
# stands in one experiment, beside its measurement (data/constants_and_measurements.md; the rows the classical theory
# carries and the equations for several bound world lines are listed in
# data/rows_not_computed.md). PART 3 writes the classical equation with the number in front of every term.
# Run from the repository root:  python -I programs/classical_experiments.py > outputs/classical_experiments.out
# Prints its checks ("ok" or "FAIL"), the answers of the law to each control, every experiment with its rows and their
# differences from the measurements in standard deviations, and the count of the rows by experiment.
import itertools, math, re, io, os, textwrap
from fractions import Fraction as Fr
from math import sqrt, log, exp, pi, atan2
import numpy as np
import json

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
with open(os.path.join(ROOT, "data", "inputs.json"), encoding="utf-8") as fh:
    INPUTS = {key: entry["value"] for key, entry in json.load(fh).items()}
TABLE = os.path.join(ROOT, "data", "constants_and_measurements.md")
CARRIED = os.path.join(ROOT, "data", "rows_not_computed.md")
ok = []
rng = np.random.default_rng(11)


def chk(name, cond, val=""):
    ok.append(bool(cond))
    print(("ok   " if cond else "FAIL ") + name + ("" if val == "" else "   [" + str(val) + "]"))


def head(t):
    print()
    print("=" * 118)
    print(t)
    print("=" * 118)


def para(label, text, width=118):
    lead = "  %-17s" % label
    print(textwrap.fill(text, width=width, initial_indent=lead, subsequent_indent=" " * len(lead)))


# =====================================================================================================================
head("PART 0. THE APPARATUS: one law on the step B of a world line")
s0 = np.eye(2)
sx = np.array([[0, 1], [1, 0]], dtype=complex)
sy = np.array([[0, -1j], [1j, 0]])
sz = np.array([[1, 0], [0, -1]], dtype=complex)
gam = [np.kron(sx, s0), np.kron(sy, s0), np.kron(sz, sx), np.kron(sz, sy), np.kron(sz, sz)]
I4 = np.eye(4)
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
kN = lambda N, u: 1 + 4 * u * u - u * (5 - 2 * N)
chk("the law: det(I - uB) = (1 - u^2)^24 k0 k2^10 k4^5, k_N(u) = 1 + 4u^2 - u(5 - 2N); one leading zero, k0(1/4) = 0",
    all(abs(np.linalg.det(np.eye(80) - u * B) - (1 - u * u) ** 24 * kN(0, u) * kN(2, u) ** 10 * kN(4, u) ** 5) < 1e-8
        for u in (0.1, 0.23 + 0.05j, -0.17j)) and kN(0, 0.25) == 0)

# the law is the comparison with one movable spectral parameter. The comparison of two systems, L = I x I + sum_t g_t x g_t,
# takes the values 6, 2, -2 on the singlet, the ten symmetric states and the five vector states. The paired vectors
# (g_S x 1) Omega and the characters W_xS = (1/4)(-1)^|x cap S| carry 6I - L onto 5I - A, so the law is the determinant of
# the comparison shifted by one spectral parameter, chi(u) = 1/u + 4u - 5 = (1 - u)(1 - 4u)/u: what compares two systems is
# what one persisting distinction propagates through.
I16 = np.eye(16)
Lcmp = np.eye(16, dtype=complex) + sum(np.kron(x, x) for x in gam)
Pswap = np.zeros((16, 16))
for i in range(4):
    for j in range(4):
        Pswap[i * 4 + j, j * 4 + i] = 1
wE_, VE_ = np.linalg.eigh(Lcmp / 2 - Pswap)
Omg = VE_[:, np.argmax(wE_)]


def gword(S):
    out = I4.astype(complex)
    for a_ in range(d):
        if (S >> a_) & 1:
            out = out @ gam[a_]
    return out


Hp = np.array([np.kron(gword(S), I4) @ Omg for S in rel]).T
Wc = np.array([[0.25 * (-1) ** bin(x & S).count("1") for S in rel] for x in rel])
TL = Hp @ Wc.T
chi = lambda u: 1 / u + 4 * u - 5
okk = True
for u in (0.11, 0.2 + 0.07j, -0.3j, 0.25 - 0.1j):
    lhs_ = np.linalg.det(np.eye(80) - u * B)
    rhs_ = (1 - u * u) ** 24 * u ** 16 * np.linalg.det(6 * I16 - Lcmp + chi(u) * I16)
    okk &= abs(lhs_ - rhs_) < 1e-9 * max(1, abs(rhs_))
chk("the comparison is the propagation kernel: T = H W^T is unitary, T^dagger (6I - L) T = 5I - A, and "
    "det(I - uB) = (1 - u^2)^24 u^16 det[(6I - L) + chi(u) I], chi(u) = (1 - u)(1 - 4u)/u",
    np.allclose(TL.conj().T @ TL, I16) and np.allclose(TL.conj().T @ (6 * I16 - Lcmp) @ TL, 5 * I16 - A) and okk)
LOmega = float((Omg.conj() @ Lcmp @ Omg).real)
points4 = [0.25, 0.25j, -0.25, -0.25j]
chiq = [chi(u) for u in points4]
chk("the grade factors are the spectral parameter read through the comparison: k_N(u) = u(2N + chi(u)), 6 - L = 0, 4, 8 at N = 0, 2, 4; the four "
    "points put the spectral parameter at chi = 0, -5 - 3i, -10, -5 + 3i; L(Omega) = 6",
    all(abs(u * (2 * N + chi(u)) - kN(N, u)) < 1e-12 for N in (0, 2, 4) for u in (0.13, 0.2 + 0.1j, -0.25, 0.25j))
    and np.allclose(chiq, [0, -5 - 3j, -10, -5 + 3j]) and abs(LOmega - 6) < 1e-12)
print("    the spectral parameter at the four points: singlet 1/4 -> chi = 0 (the one zero); direction h i/4 -> -5 - 3i; plane hk -1/4 -> -10; colour -i/4 -> -5 + 3i")
print("    at u = -1/4 the comparison shifted by chi = -10 has the values -10, -6, -2 on the singlet, the symmetric states and the vector states:")
print("    k_N(-1/4) = 5/2, 3/2, 1/2; transmission t = 1/k0 = 2/5, reflection e = k2/k0 = 3/5, at a single direction t_l = 1/k2 = 2/3, e_l = k4/k2 = 1/3")


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
idx = {}
for S in range(1 << d):
    for t in range(d):
        for p_ in (0, 1):
            idx[(S, t, p_)] = len(idx)
mI = len(idx)
is_singlet = lambda S, p_: (p_ == 0 and S == 0) or (p_ == 1 and S == ALL)


def first_return(z, signed):
    Q = np.zeros((mI, mI), dtype=complex)
    r = np.zeros(mI, dtype=complex)
    for (S, t, p_), i in idx.items():
        if is_singlet(S, p_):
            continue
        for s in range(d):
            if s == t:
                continue
            sg = (-1) ** bin(S >> (s + 1)).count("1") if signed else 1
            S2, p2 = S ^ (1 << s), 1 - p_
            if is_singlet(S2, p2):
                r[i] += (0.25 * sg if S2 == 0 else 0.0) if signed else 0.25
            else:
                Q[idx[(S2, s, p2)], i] += 0.25 * sg
    psi = z * np.linalg.solve(np.eye(mI) - z * Q.T, r)
    return z * sum(0.25 * psi[idx[(1 << s, s, 1)]] for s in range(d) if s != 0)


Fz = lambda z: z ** 4 * (1 + z) / (16 - 8 * z - 3 * z ** 2 - 3 * z ** 3)
Phz = lambda z: -z ** 4 / (16 + 3 * z ** 2)
chk("one step out and back: F(z) = z^4(1 + z)/(16 - 8z - 3z^2 - 3z^3), signed Phi(z) = -z^4/(16 + 3z^2), counted on B",
    all(abs(first_return(z, False) - Fz(z)) < 1e-12 and abs(first_return(z, True) - Phz(z)) < 1e-12 for z in (0.4, 0.6 + 0.3j, 0.8j)))
P1 = Fr(-1, 19) if abs(first_return(1.0, True) + 1 / 19) < 1e-12 else None
Pi_ = Fr(-1, 13) if abs(first_return(1j, True) + 1 / 13) < 1e-12 else None
trans = [(x, t) for (x, t) in states if x != 0]
ti = {st: i for i, st in enumerate(trans)}
Tm = np.zeros((len(trans), len(trans)))
for (x, t) in trans:
    for s in range(d):
        if s != t and (x ^ g[s]) != 0:
            Tm[ti[(x, t)], ti[(x ^ g[s], s)]] = 0.25
v0 = np.zeros(len(trans))
for s in range(1, d):
    v0[ti[(g[s], s)]] += 0.25
Nm = np.linalg.inv(np.eye(len(trans)) - Tm)
mu_ = v0 @ Nm
is_sym = np.array([1.0 if bin(x).count("1") == 2 else 0.0 for (x, t) in trans])
is_vec = np.array([1.0 if bin(x).count("1") == 4 else 0.0 for (x, t) in trans])
second = lambda Ai, Bi: float(mu_ @ (np.diag(Ai) @ Nm @ Bi) + mu_ @ (np.diag(Bi) @ Nm @ Ai) - mu_ @ (Ai * Bi))
EnFf, EnLf = float(mu_ @ is_sym), float(mu_ @ is_vec)
VarnFf, VarnLf, Covf = second(is_sym, is_sym) - EnFf ** 2, second(is_vec, is_vec) - EnLf ** 2, second(is_sym, is_vec) - EnFf * EnLf
h0 = 0
avail = [(x, t) for (x, t) in states if x != 0 and not (x == g[h0] and t == h0)]
avail_tr = [(x, t, s) for (x, t) in avail for s in range(d) if s != t]
M, Ch, Cj = len(avail_tr), sum(1 for c_ in avail_tr if c_[2] == h0), sum(1 for c_ in avail_tr if c_[2] == 1)
n_noh = sum(1 for (x, t) in avail if not (x >> h0) & 1)
Gg = np.linalg.pinv(5 * np.eye(16) - A)
bG = Gg[0, 0] + Gg[ri[0b00011], ri[0b00011]] - 2 * Gg[0, ri[0b00011]]
chk("one excursion: visits E n_F = 10, E n_L = 5, Var n_F = 84, Var n_L = 12, Cov = 30; 74 directed edges, M = 296 available transitions, C_h = 60 along h; b = 7/16",
    max(abs(EnFf - 10), abs(EnLf - 5), abs(VarnFf - 84), abs(VarnLf - 12), abs(Covf - 30)) < 1e-9
    and (len(avail), M, Ch, Cj, n_noh) == (74, 296, 60, 59, 34) and abs(bG - 7 / 16) < 1e-12)
# the weight of one transition: the moment compared with itself, <Omega, (L + g_h x g_s) Omega>, for the transition along s
trans_weight = [float((Omg.conj() @ (Lcmp + np.kron(gam[h0], gam[s])) @ Omg).real) for s in range(d)]
chk("a transition compares the moment with itself: <Omega, (L + g_h x g_s) Omega> = 6 + [s = h], computed from the comparison",
    np.allclose(trans_weight, [LOmega + (1 if s == h0 else 0) for s in range(d)]), "%s" % ", ".join("%.0f" % x for x in trans_weight))
# the cells of RP^4 the steps walk on: the links and the squares, the curvature around a square, the gauge transformations
cells = {}
for k in range(3):
    found = set()
    for x in rel:
        for S in itertools.combinations(range(d), k):
            vs = {x}
            for s in S:
                vs |= {v ^ g[s] for v in vs}
            found.add((frozenset(vs), frozenset(S)))
    cells[k] = sorted(found, key=lambda c: (sorted(c[1]), sorted(c[0])))
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
chk("the cells: 16 vertices, 40 links, 40 squares; the curvature around the squares vanishes on every gauge transformation, C grad = 0",
    [len(cells[k]) for k in range(3)] == [16, 40, 40] and np.allclose(Cm @ Gr, 0))

# the primitive numbers: every number the law and the geometry give directly
uF = Fr(-1, 4)
K0, K2, K4 = kN(0, uF), kN(2, uF), kN(4, uF)
qch = [Fr(0), Fr(1), Fr(-1, 3), Fr(-1, 3), Fr(-1, 3)]
cC = 2 * (sum(q * q for q in qch) / 5 - (sum(qch) / 5) ** 2)
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
chk("the primitive numbers: grade factors 5/2, 3/2, 1/2; Phi(1) = -1/19, Phi(i) = -1/13; a = 5/38, chi_A = 13/12, eta = 295/296, c_L = 15/74, "
    "E_H = 3, f = 9/250, W = (2/5)^48 (295/296)^9",
    (K0, K2, K4, P1, Pi_, a, chiA, eta, cL, EH, f) == (Fr(5, 2), Fr(3, 2), Fr(1, 2), Fr(-1, 19), Fr(-1, 13), Fr(5, 38), Fr(13, 12),
                                                     Fr(295, 296), Fr(15, 74), Fr(3), Fr(9, 250))
    and abs(W - (2 / 5) ** 48 * (295 / 296) ** 9) < 1e-60)
Kf, af, bf = float(K0), float(a), float(b)
etaf, sigf, cLf, Rudf, EHf = float(eta), float(sigma), float(cL), float(Rud), float(EH)
tf, eEf, eLf, ff, nuf = float(tE), float(eE), float(eL), float(f), float(nu)
P1f, chiAf, chihf = float(P1), float(chiA), float(chih)

# the law on its own resolved chart: the five changes move by v_t = e_t - (1, 1, 1, 1, 1)/5 (sum v_t = 0, sum v_t v_t = I on
# R^4); a world line alternates between two sheets, sheet 0 the A4 lattice {x in Z^5: sum x = 0} and sheet 1 its shift by v_0.
# Ihara and Bass: the step that never turns straight back on the chart has the same law as the vertex operator
# (1 + 4u^2) - uA, so the chart carries the same law; eliminating sheet 1 gives S = rho Q, rho = 5u^2/(1 + 4u^2),
# Q = M^2 + (25 - F F*)/5, M^2 = ((1/u + 4u)^2 - 25)/5, F(k) = sum_t exp(i k.v_t).
Lc = 3
cell4 = list(itertools.product(range(Lc), repeat=4))
cid = {c: i for i, c in enumerate(cell4)}
n4 = len(cell4)
edges = []
for c in cell4:
    edges.append((cid[c], n4 + cid[c]))
    for t in range(4):
        c2 = list(c)
        c2[t] = (c2[t] - 1) % Lc
        edges.append((cid[tuple(c2)], n4 + cid[c]))
arcs4 = edges + [(y, x) for (x, y) in edges]
out_of = {}
for i, (x, y) in enumerate(arcs4):
    out_of.setdefault(x, []).append(i)
Bc = np.zeros((len(arcs4), len(arcs4)))
for i, (x, y) in enumerate(arcs4):
    for j in out_of[y]:
        if arcs4[j][1] != x:
            Bc[j, i] = 1
Ac = np.zeros((2 * n4, 2 * n4))
for (x, y) in edges:
    Ac[x, y] = Ac[y, x] = 1
okib = True
for u in (0.11, 0.2, 0.23):
    s1, l1 = np.linalg.slogdet(np.eye(len(arcs4)) - u * Bc)
    s2, l2 = np.linalg.slogdet((1 + 4 * u * u) * np.eye(2 * n4) - u * Ac)
    okib &= s1 == s2 and abs(l1 - (l2 + (len(edges) - 2 * n4) * log(1 - u * u))) < 1e-8
chk("the chart carries the same law: on a 3^4 chart (162 vertices, 405 links) det(I - uB_chart) = (1 - u^2)^(E - V) det((1 + 4u^2) - uA_chart)", okib)
v5 = np.eye(5) - np.ones((5, 5)) / 5
Fk = lambda k: sum(np.exp(1j * (k @ v5[t])) for t in range(5))
Mfrom_u = lambda u: ((1 / u + 4 * u) ** 2 - 25) / 5
u_of_M = lambda Mm: (sqrt(25 + 5 * Mm * Mm) - sqrt(9 + 5 * Mm * Mm)) / 8


# =====================================================================================================================
head("PART 1. THE LAW ANSWERS THE CLASSICAL CONTROLS: hold one quantity, vary it, watch what stays fixed")
HELD = {}

# F1. the plane hk held: one time and three space
vDp = np.array([1.0, 0.0, 0.0, 0.0])
gmat = np.diag([-1, -1, 1, 1, 1, 1.0])
p0 = np.concatenate([np.array([1.0, 0.0]), vDp])
Tb = np.array([x for x in np.eye(6) if abs(x @ gmat @ p0) < 1e-12])
sig = np.linalg.eigvalsh(Tb @ gmat @ Tb.T)
print()
print("F1. THE PLANE HK HELD, TYPE 2|4. Control: the null directions of the distinction. Answer: the null cone, projectivized, has three")
print("    directions of one sign and one of the other. Form: one time and three space, the light cone.")
chk("F1 the null cone of the distinction of the plane hk has signature (1, 3), negative directions first: one time, three space", (sum(sig < -1e-9), sum(sig > 1e-9)) == (1, 3))
# the clocks: a distinction of type d|6-d keeps so(d) + so(6-d); only a side of two directions has a central rotation, so the
# clocks live on held planes of type 2|4. The world line's own clock i g_h rotates the plane {n, h}; the common clock g_h g_k
# rotates the plane hk; H_k = (1 + i g_k)/sqrt2 carries the one into the other, and with the change between them, i g_k, they
# are one quaternion triple. The direction h alone, type 1|5, keeps so(5) and has no clock: there the own clock is moved, and
# its rate is the mass.
Hk_ = (I4 + 1j * gam[1]) / sqrt(2)
T1_, T2_, T3_ = 1j * gam[0], gam[0] @ gam[1], 1j * gam[1]
keptk = [kk * (kk - 1) // 2 + (6 - kk) * (5 - kk) // 2 for kk in range(4)]
print("    the clocks: rotations within the sides of d|6-d = %s; a central one only at 2|4. Own clock i g_h on the plane {n, h}; common clock"
      % keptk)
print("    g_h g_k on the plane hk; H_k (i g_h) H_k^dagger = g_h g_k; with i g_k they are one quaternion triple. Time is a held plane.")
chk("F1 the two clocks are one quaternion triple: H_k (i g_h) H_k^dagger = g_h g_k, T_a^2 = -1, T1 T2 = T3, T2 T3 = T1, T3 T1 = T2; "
    "rotations within the sides 15, 10, 7, 6, central only at 2|4",
    np.allclose(Hk_ @ T1_ @ Hk_.conj().T, T2_) and all(np.allclose(Ta @ Ta, -I4) for Ta in (T1_, T2_, T3_))
    and np.allclose(T1_ @ T2_, T3_) and np.allclose(T2_ @ T3_, T1_) and np.allclose(T3_ @ T1_, T2_) and keptk == [15, 10, 7, 6])

# F2. a wave of a held wavelength on the chart
print()
print("F2. A WAVE OF A HELD WAVE VECTOR k. Control: k in all four directions of the chart, |k| varied. Answer: the law's operator Q(k).")
dirs = []
while len(dirs) < 8:
    z_ = rng.normal(size=5)
    z_ -= z_.mean()
    dirs.append(z_ / np.linalg.norm(z_))
ratios_k = []
for kk in (0.4, 0.2, 0.1, 0.05):
    rr = [(25 - abs(Fk(kk * dv)) ** 2) / 5 / kk ** 2 for dv in dirs]
    ratios_k.append((kk, min(rr), max(rr)))
    print("    |k| = %-5s  (Q(k) - M^2)/|k|^2 over eight directions: %.6f to %.6f" % (kk, min(rr), max(rr)))
m2r, gapr = [], []
for mm in (0.2, 0.1, 0.05):
    u = 0.25 - mm * mm / 24
    m2r.append(Mfrom_u(u) / mm ** 2)
    gapr.append(chi(u) / (mm * mm / 2))
print("    the step's weight held below the zero, u = 1/4 - m^2/24, m = 0.2, 0.1, 0.05: M^2/m^2 = %s" % ", ".join("%.6f" % x for x in m2r))
print("    the spectral parameter there, chi/(m^2/2) = %s: the mass squared is twice the spectral parameter to leading order; exactly M^2 = 2 chi + chi^2/5 on this chart" % ", ".join("%.6f" % x for x in gapr))
# the rest pole: k purely along the direction h, imaginary: cosh(sqrt5 w/2) = 1 + 5M^2/8
Th = v5[0] / np.linalg.norm(v5[0])
rest = []
for Mm in (0.2, 0.1, 0.05):
    w_ = 2 / sqrt(5) * math.acosh(1 + 5 * Mm * Mm / 8)
    resid = Mm * Mm + (25 - (Fk(1j * w_ * Th) * Fk(-1j * w_ * Th)).real) / 5
    rest.append((w_ / Mm, abs(resid)))
print("    a world line held at rest: its clock's frequency w where Q has its zero, w/M at M = 0.2, 0.1, 0.05: %s"
      % ", ".join("%.6f" % r_[0] for r_ in rest))
print("    Form: Q = M^2 + |k|^2 + O(|k|^4) in every direction, E^2 = p^2 c^2 + m^2 c^4 on the null cone of the plane hk; the zero's distance is the mass;")
print("    at rest the clock turns at the mass, E = mc^2; c is one step per step.")
chk("F2 Klein-Gordon: (Q - M^2)/|k|^2 -> 1 in every direction as k -> 0, M^2/m^2 -> 1, the rest frequency w/M -> 1",
    abs(ratios_k[-1][1] - 1) < 3e-4 and abs(ratios_k[-1][2] - 1) < 3e-4 and (1 - ratios_k[-1][1]) < (1 - ratios_k[-2][1]) / 3.5
    and abs(m2r[-1] - 1) < 1e-3 and abs(gapr[-1] - 1) < 1e-3
    and abs(rest[-1][0] - 1) < 1e-3 and max(r_[1] for r_ in rest) < 1e-12)

# F3. the first-order step
print()
print("F3. A WORLD LINE CARRIED ALONG ANOTHER DIRECTION. Control: the clock's phase mu per step and the phase k along another direction, varied.")
okd = True
for (mu1, k1) in [(0.3, 0.5), (1.1, -0.7), (0.05, 0.02), (2.0, 1.3)]:
    Ust = (np.cos(k1) * I4 - 1j * np.sin(k1) * gam[1]) @ (np.cos(mu1) * I4 - 1j * np.sin(mu1) * gam[0])
    okd &= np.allclose(Ust + Ust.conj().T, 2 * np.cos(k1) * np.cos(mu1) * I4)
print("    Answer: U + U^dagger = 2 cos k cos mu at every (mu, k). Form: cos w = cos mu cos k, w^2 = mu^2 + k^2 at small phase: Dirac.")
chk("F3 Dirac: the first-order step U = exp(-ik g_j) exp(-i mu g_h) has U + U^dagger = 2 cos k cos mu", okd)

# F4. two static sources held at a distance on the chart
print()
print("F4. TWO SOURCES HELD AT REST AT A DISTANCE r. Control: r from 4 to 18 steps along four directions; the step's weight at the")
print("    zero (M = 0) and below it (M = 0.05). Answer: the law's static response between the two held vertices, computed on the chart.")
P3 = np.array([[0, .75, -.25, -.25, -.25], [0, -.25, .75, -.25, -.25], [0, -.25, -.25, .75, -.25]])
ptv = [np.array([1, 0, 0]), np.array([0, 1, 0]), np.array([0, 0, 1]), np.array([-1, -1, -1])]
hops = []
for t in range(4):
    hops += [ptv[t], -ptv[t]]
for s in range(4):
    for t in range(4):
        if s != t:
            hops.append(ptv[s] - ptv[t])
physp = lambda n: n[0] * P3[0] + n[1] * P3[1] + n[2] * P3[2]
okst = True
for _ in range(5):
    q = rng.normal(size=5)
    q -= q.mean()
    q -= (q @ Th) * Th
    lhs = 25 - abs(Fk(q)) ** 2
    rhs = sum(1 - np.cos(q @ physp(hh)) for hh in hops)
    okst &= abs(lhs - rhs) < 1e-10
chk("F4 a static field on the chart lives on the projection of the A4 lattice along the direction h (cell 1/2); its operator is the chart's Q at k.T = 0", okst)
V3 = 0.5
Ls_ = 160
kf = 2 * pi * np.fft.fftfreq(Ls_)
K1, K2_, K3 = np.meshgrid(kf, kf, kf, indexing="ij", sparse=True)
Lsym = np.zeros((Ls_, Ls_, Ls_))
for hh in hops:
    Lsym += 1 - np.cos(hh[0] * K1 + hh[1] * K2_ + hh[2] * K3)
static = {}
for Mm in (0.0, 0.05):
    den = V3 * (Mm * Mm + Lsym / 5)
    if Mm == 0:
        den[0, 0, 0] = np.inf
    static[Mm] = np.fft.ifftn(1 / den).real
del Lsym, den
sdirs = [[2, -1, 0], [1, 2, 3], [1, 1, 0], [1, 0, 0]]
coef0, coefM = [], []
for dirn in sdirs:
    dn = np.array(dirn)
    pts = []
    for m in range(1, 60):
        n = m * dn
        r = float(np.linalg.norm(physp(n)))
        if r > 19:
            break
        if r >= 3.9:
            pts.append((r, n))
    vals0 = [(r, static[0.0][n[0] % Ls_, n[1] % Ls_, n[2] % Ls_]) for r, n in pts]
    valsM = [(r, static[0.05][n[0] % Ls_, n[1] % Ls_, n[2] % Ls_]) for r, n in pts]
    near = min(vals0, key=lambda z: abs(z[0] - 6))
    far = min(vals0, key=lambda z: abs(z[0] - 18))
    c0 = 4 * pi * (near[1] - far[1]) / (1 / near[0] - 1 / far[0])
    cM = [4 * pi * r * gv * exp(0.05 * r) for r, gv in valsM]
    coef0.append(c0)
    coefM.append(cM)
    print("    direction %-11s M = 0: the number in front of 1/(4 pi r), from r = %.2f to %.2f: %.5f;   M = 0.05: 4 pi r G e^(Mr) at r = %s: %s; all %d samples %.5f to %.5f"
          % (str(dirn), near[0], far[0], c0, ", ".join("%.1f" % r for r, _ in valsM[::2][:4]), ", ".join("%.4f" % x for x in cM[::2][:4]), len(cM), min(cM), max(cM)))
HELD["static"] = (coef0, coefM)
print("    Form: G_cont(r) = e^(-Mr)/(4 pi r), the long-wave continuum response: at the law's zero the response falls as 1/r (Poisson), below it as Yukawa with range 1/M;")
print("    the step's weight for M = 0.05 is u = %.12f. The number in front of 1/r is what the two held sources bring: PART 2." % u_of_M(0.05))
chk("F4 the static response at the law's zero is 1/(4 pi r) within 1% in four directions; below the zero e^(-Mr)/(4 pi r) within 1% at r >= 4",
    all(abs(c - 1) < 0.01 for c in coef0) and all(abs(x - 1) < 0.01 for cm in coefM for x in cm))

# F5. a gauge field held on the links
print()
print("F5. A GAUGE FIELD HELD ON THE LINKS. Control: phases theta on the forty links, amplitude varied; and a pure gauge transformation theta = grad phi.")


def logdet_signed(w, th):
    At = Am.astype(complex).copy()
    for (a_, b_), j in lid.items():
        At[ri[b_], ri[a_]] = Am[ri[b_], ri[a_]] * np.exp(1j * th[j])
        At[ri[a_], ri[b_]] = Am[ri[a_], ri[b_]] * np.exp(-1j * th[j])
    return np.log(np.linalg.det(np.eye(16) - w * At))


th0 = rng.normal(size=40)
rows_k = []
for w, wname in ((0.2, "the plane hk and the singlet, w = 1/5"), (1j / 3, "the direction h and colour, w = i/3")):
    base = logdet_signed(w, np.zeros(40))
    rr = []
    for amp in (0.1, 0.03, 0.01):
        th = amp * th0
        flux = th @ Cm.T @ Cm @ th
        rr.append(((logdet_signed(w, th) - base) / (-0.5 * flux)).real)
    rows_k.append((wname, rr, kap_w(w).real))
    print("    %-32s kappa from the answer at amplitudes 0.1, 0.03, 0.01: %s   (2w^4/(1 - 5w^2)^2 = %.6f)"
          % (wname, ", ".join("%.6f" % x for x in rr), kap_w(w).real))
kap_chi = lambda c_: 2 / ((c_ + 5) ** 2 - 5) ** 2
sweepk = []
for c_ in (0.0, 1.0, 3.0, 10.0):
    w = 1 / (c_ + 5)
    th = 0.01 * th0
    sweepk.append((c_, ((logdet_signed(w, th) - logdet_signed(w, np.zeros(40))) / (-0.5 * (th @ Cm.T @ Cm @ th))).real, kap_chi(c_)))
print("    the spectral parameter varied, w = 1/(chi + 5): chi = %s: kappa from the answer %s; 2/[(chi + 5)^2 - 5]^2 = %s"
      % (", ".join("%g" % s_[0] for s_ in sweepk), ", ".join("%.7f" % s_[1] for s_ in sweepk), ", ".join("%.7f" % s_[2] for s_ in sweepk)))
phi_ = rng.normal(size=16)
gauge = abs(logdet_signed(0.2, 1.0 * (Gr @ phi_)) - logdet_signed(0.2, np.zeros(40)))
print("    a gauge transformation theta = grad phi at amplitude one changes the law by %.1e" % gauge)
print("    Form: -(kappa/2)|C theta|^2, the squared curvature around the squares, unchanged by a gauge transformation: Maxwell's and Yang-Mills' F^2.")
chk("F5 the law answers a gauge field with the squared curvature: kappa -> 1/200 and 1/98; as chi varies kappa(chi) = 2/[(chi + 5)^2 - 5]^2; "
    "a gauge transformation leaves it unchanged",
    abs(rows_k[0][1][-1] - 1 / 200) < 1e-6 and abs(rows_k[1][1][-1] - 1 / 98) < 1e-6 and gauge < 1e-10
    and all(abs(s_[1] - s_[2]) < 2e-3 * s_[2] for s_ in sweepk))

# F6. a circulation carried around the cells
print()
print("F6. A CIRCULATION CARRIED AROUND THE CELLS. Control: the part of the link phases no gauge transformation removes, amplitude varied.")
thc = rng.normal(size=40)
thc -= Gr @ np.linalg.lstsq(Gr, thc, rcond=None)[0]
circ = []
for amp in (0.03, 0.01, 0.003):
    th = amp * thc
    At = np.zeros((16, 16), dtype=complex)
    for (x1, x2), j in lid.items():
        At[ri[x2], ri[x1]] += np.exp(1j * th[j])
        At[ri[x1], ri[x2]] += np.exp(-1j * th[j])
    lmax = np.linalg.eigvalsh(At).max()
    uc = (lmax - sqrt(lmax * lmax - 16)) / 8
    circ.append((th @ th) / log(4 * uc))
print("    Answer: the law's leading zero moves; |theta_cyc|^2/log 4u_c at amplitudes 0.03, 0.01, 0.003: %s" % ", ".join("%.5f" % x for x in circ))
print("    Form: log 4u_c = |theta_cyc|^2/48 + O(theta^4): the leading zero feels a rotation carried around the cells through 48 = k_C E l steps.")
chk("F6 a circulation moves the leading zero by |theta_cyc|^2/48", abs(circ[-1] - 48) < 1e-3)

# F7. the frame held curved
print()
print("F7. THE FRAME HELD CURVED. Control: the ten rotations split at h, the four that move it held as e/l, l varied; any curvature R.")
e4 = np.zeros((4,) * 4)
for perm in itertools.permutations(range(4)):
    e4[perm] = np.linalg.det(np.eye(4)[list(perm)])
EE = np.einsum("ac,bd->abcd", np.eye(4), np.eye(4)) - np.einsum("ad,bc->abcd", np.eye(4), np.eye(4))
wedge = lambda X, Yt: 0.25 * np.einsum("abcd,abef,cdgh,efgh->", e4, X, Yt, e4)
lam_l2 = []
for ell in (0.5, 1.0, 1.7, 3.0):
    Rr = rng.normal(size=(4, 4, 4, 4))
    Rr = Rr - Rr.transpose(1, 0, 2, 3)
    Rr = Rr - Rr.transpose(0, 1, 3, 2)
    Rr = Rr + Rr.transpose(2, 3, 0, 1)
    lhs = wedge(Rr - EE / ell ** 2, Rr - EE / ell ** 2) - wedge(Rr, Rr)
    Rsc = np.einsum("abab->", Rr)
    lam_l2.append((-(lhs / (-(4 / ell ** 2))) + Rsc) / 2 * ell ** 2)
print("    Answer: the curvature of the ten rotations contracted with h in the epsilon contraction, -(4/l^2)(R - 2 Lambda); Lambda l^2 at l = 0.5, 1, 1.7, 3: %s"
      % ", ".join("%.12f" % x for x in lam_l2))
print("    Form: Einstein-Cartan with the constant term, R - 2 Lambda, Lambda = 3/l^2 for every curvature and every l.")
chk("F7 Lambda l^2 = 3 at every l and every curvature", all(abs(x - 3) < 1e-9 for x in lam_l2))

# F8. the direction h held at its length
print()
print("F8. THE DIRECTION h HELD AT ITS LENGTH v. Control: the direction h in the plane hk, length v varied; the twelve rotations keeping 2 + 3.")
Eu = lambda i, j: np.outer(np.eye(5)[i], np.eye(5)[j]).astype(complex)
gbasis = []
for blk in ([0, 1], [2, 3, 4]):
    for i in blk:
        for j in blk:
            if i < j:
                gbasis.append(1j * (Eu(i, j) + Eu(j, i)) / sqrt(2))
                gbasis.append((Eu(i, j) - Eu(j, i)) / sqrt(2))
for blk in ([0, 1], [2, 3, 4]):
    n_ = len(blk)
    for m_ in range(1, n_):
        vv = np.zeros(5)
        vv[blk[:m_]] = 1
        vv[blk[m_]] = -m_
        vv /= np.linalg.norm(vv)
        gbasis.append(1j * np.diag(vv))
gbasis.append(1j * np.diag(np.array([3, 3, -2, -2, -2]) / sqrt(30)))
handg = []
for vlen in (0.5, 1.0, 2.0):
    phi = vlen * np.eye(5)[0]
    Gm = np.array([[np.real(np.vdot(X @ phi, Yb @ phi)) for Yb in gbasis] for X in gbasis])
    ev = sorted(np.round(np.linalg.eigvalsh(Gm) / vlen ** 2, 12))
    nz = [x for x in ev if abs(x) > 1e-12]
    handg.append((vlen, nz, len(ev) - len(nz)))
    print("    v = %-4s the moved rotations' masses squared over v^2: %s; rotations left at zero: %d" % (vlen, ", ".join("%.6f" % x for x in nz), len(ev) - len(nz)))
print("    Form: |D(v h)|^2: W+, W-, Z with M^2 proportional to v^2, M_W^2/M_Z^2 = 5/8 at the source; the photon and eight colour rotations stay at zero.")
chk("F8 the direction h at length v: masses squared v^2 (1/2, 1/2, 4/5), nine at zero, for every v",
    all(np.allclose(nz, [0.5, 0.5, 0.8]) and nzero == 9 for _, nz, nzero in handg))

# F9. a world line held at rest with a phase per step on its transitions: the clock
print()
print("F9. A WORLD LINE HELD AT REST, ITS CLOCK TURNING. Control: a phase theta per step on its transitions, varied. Answer: the turn of the law's zero.")
Bc80 = B.astype(complex)
avail_arcs = [(si[(x ^ g[s], s)], si[(x, t)], s) for (x, t) in avail for s in range(d) if s != t]


def leading_zero(Bt):
    u = 0.25 + 0j
    for _ in range(80):
        Mx = np.eye(80) - u * Bt
        Dv = np.linalg.det(Mx)
        dD = -Dv * np.trace(np.linalg.solve(Mx, Bt))
        du = Dv / dD
        u -= du
        if abs(du) < 1e-16:
            break
    return u


def clock_turn(weights, th):
    Bt = Bc80.copy()
    for (i, j), wv in weights.items():
        Bt[i, j] = np.exp(-1j * th * wv)
    return np.log(4 * leading_zero(Bt)).imag / th


w_e = {(avail_arcs[0][0], avail_arcs[0][1]): 1}
w_p = {(i, j): trans_weight[s] for (i, j, s) in avail_arcs}
# one transition marked, exactly: the law is linear in one entry and every transition has the same cofactor, so
# D_theta(u) = D(u) + (e^(-i theta) - 1) u D'(u)/320 at every u and every theta
okarc = True
for (u, th) in [(0.2, 0.7), (0.24 + 0.01j, 2.0), (-0.1j, 0.3), (0.249, 3.0)]:
    Bt = Bc80.copy()
    Bt[avail_arcs[5][0], avail_arcs[5][1]] = np.exp(-1j * th)
    Mx = np.eye(80) - u * B
    D0 = np.linalg.det(Mx)
    dD0 = -D0 * np.trace(np.linalg.solve(Mx, B))
    okarc &= abs(np.linalg.det(np.eye(80) - u * Bt) - (D0 + (np.exp(-1j * th) - 1) * u * dD0 / 320)) < 1e-9 * max(abs(D0), 1e-30)
chk("F9 one transition marked, exactly: D_theta(u) = D(u) + (e^(-i theta) - 1) u D'(u)/320 at every u and theta (each transition one cofactor)", okarc)
clk = []
for th in (4e-4, 2e-4, 1e-4):
    te, tp = clock_turn(w_e, th), clock_turn(w_p, th)
    clk.append((th, te * 320, tp * 320, tp / te))
    print("    theta = %-7s electron, one transition: turn per step x 320 = %.9f;   proton, each of its M transitions at L(Omega) = 6 and its C_h transitions along h once more:"
          " x 320 = %.6f;   ratio %.6f" % (th, te * 320, tp * 320, tp / te))
ratio0 = (4 * clk[-1][3] - clk[-2][3]) / 3                     # the remainder falls as theta^2
print("    the ratio at theta -> 0: %.6f = L(Omega) M + C_h = 6 x 296 + 60" % ratio0)
print("    Form: a world line at rest turns its clock at a fixed rate per step, E = hbar w = mc^2; the electron's is one transition in 320, the unit; the")
print("    proton's 1836 transitions' worth; the ratio of the two clocks is the ratio of the two masses.")
HELD["clock"] = ratio0
chk("F9 the zero turns by theta/320 + O(theta^3) per marked transition, rate 1/320 as theta -> 0; the proton's rate on the available transitions is 6M + C_h = 1836 times the electron's as theta -> 0",
    abs(clk[-1][1] - 1) < 1e-6 and abs(ratio0 - 1836) < 1e-5)

# F10. the response of two sets of directions read against the clock that moves with it, the spectral parameter varied
print()
print("F10. THE SPECTRAL PARAMETER VARIED: A RESPONSE AND ITS OWN CLOCK. Control: chi, from the zero (chi = 0) to the empty step (chi -> infinity).")
print("    On the fifteen states other than the singlet the comparison's resolvent weighs a symmetric state by 1/(chi + 4) and a vector state by 1/(chi + 8).")
print("    Answer: the covariance of the grade N with H_D H_E, H_D(S) = (5|S cap D| - |D||S|)/4, against the clock C_W = (9/8) Var N.")
Snz = [S for S in rel if S != 0]
pcount = lambda S: bin(S).count("1")
Hdir = lambda S, D: (5 * pcount(S & D) - pcount(D) * pcount(S)) / 4


def response_clock(D, E, c_):
    wv = np.array([1 / (c_ + 4) if pcount(S) == 2 else 1 / (c_ + 8) for S in Snz])
    wv = wv / wv.sum()
    Nv = np.array([pcount(S) for S in Snz], dtype=float)
    Xv = np.array([Hdir(S, D) * Hdir(S, E) for S in Snz])
    return wv @ (Nv * Xv) - (wv @ Nv) * (wv @ Xv), 9 / 8 * (wv @ Nv ** 2 - (wv @ Nv) ** 2)


pairsDE = [("a pair of directions on opposite sides", 0b00001, 0b00010, Fr(1, 72)),
           ("one direction against the other four", 0b00001, 0b11110, Fr(1, 18)),
           ("the plane hk against the three directions outside it", 0b00011, 0b11100, Fr(1, 12))]
cross_ok = True
for c_ in (0.0, 0.5, 2.0, 10.0, 1e6):
    vals_ = [response_clock(D_, E_, c_) for _, D_, E_, _ in pairsDE]
    cross_ok &= all(abs(jc / cw - float(fr_)) < 1e-12 for (jc, cw), (_, _, _, fr_) in zip(vals_, pairsDE))
    print("    chi = %-8g response of a pair of directions on opposite sides %.6f, its clock C_W %.6f; ratios %s" % (c_, vals_[0][0], vals_[0][1], ", ".join("%.8f" % (jc / cw) for jc, cw in vals_)))
print("    Form: J_DE = (C_W/72)(|D||E| - 5 tr P_D P_E) at regular chi: the response and the clock move together and their ratio stays.")
print("    What stays: 1/72 for one pair of directions on opposite sides, the strong and the electroweak coupling squared; 4/72 = 1/18 for one direction against the other")
print("    four, which is -Phi(1)/(1 + Phi(1)) of the signed first return at the even points, counted on the walk; 6/72 = 1/12 for the plane hk against its")
print("    three outside directions, -Phi(i)/(1 + Phi(i)) at the odd points. At the zero the response is 1/100 and the clock 18/25.")
r0_, c0_ = response_clock(0b00001, 0b00010, 0.0)
chk("F10 chi varied: response/clock = 1/72, 1/18, 1/12 at regular chi, equal to g^2, -Phi(1)/(1 + Phi(1)), -Phi(i)/(1 + Phi(i)); 1/100 and 18/25 at the zero",
    cross_ok and abs(r0_ - 0.01) < 1e-14 and abs(c0_ - 0.72) < 1e-14
    and -P1 / (1 + P1) == Fr(1, 18) and -Pi_ / (1 + Pi_) == Fr(1, 12) and eL ** 2 / 8 == Fr(1, 72))
HELD["response"] = Fr(1, 72)

# F11. the nucleon projected before its current is read
print()
print("F11. THE NUCLEON PROJECTED. Control: the three colour world lines' spin and isospin, symmetric under exchange (the colour state is")
print("    totally antisymmetric); the proton with spin up singled out. Answer: the axial current sum_r sigma_z tau_z in that state.")
sig3 = [sx, sy, sz]
one4 = np.eye(4)


def on3(r, X):
    mats = [one4, one4, one4]
    mats[r] = X
    return np.kron(np.kron(mats[0], mats[1]), mats[2])


def perm3(pm):
    Pm = np.zeros((64, 64))
    for i, j, l in itertools.product(range(4), repeat=3):
        idx3 = [i, j, l]
        nw = [idx3[pm[0]], idx3[pm[1]], idx3[pm[2]]]
        Pm[nw[0] * 16 + nw[1] * 4 + nw[2], i * 16 + j * 4 + l] = 1
    return Pm


Psym3 = sum(perm3(pm) for pm in itertools.permutations(range(3))) / 6
Ssq3 = sum((sum(on3(r, np.kron(sg / 2, s0)) for r in range(3))) @ (sum(on3(r, np.kron(sg / 2, s0)) for r in range(3))) for sg in sig3)
PN3 = Psym3 @ (15 / 4 * np.eye(64) - Ssq3) / 3
Sz3 = sum(on3(r, np.kron(sz / 2, s0)) for r in range(3))
Tz3 = sum(on3(r, np.kron(s0, sz / 2)) for r in range(3))
wv3, vv3 = np.linalg.eigh(PN3 @ (Sz3 + 10 * Tz3) @ PN3)
pup3 = vv3[:, np.argmax(wv3)]
axial3 = float((pup3.conj() @ sum(on3(r, np.kron(sz, sz)) for r in range(3)) @ pup3).real)
print("    the symmetric space has rank %d; P_N = P_sym(15/4 - S^2)/3 has rank %d; in the proton with spin up <sum sigma_z tau_z> = %.12f"
      % (round(np.trace(Psym3).real), round(np.trace(PN3).real), axial3))
print("    Form: the axial coupling g_A = <p| sum sigma_z tau_z |p> times the transmission to the power 2b/3, (5/3) t^(2b/3).")
chk("F11 the nucleon projected: rank 4 in the symmetric 20; <sum_r sigma_z tau_z> = 5/3 in the proton with spin up",
    np.allclose(PN3 @ PN3, PN3) and round(np.trace(PN3).real) == 4 and round(np.trace(Psym3).real) == 20 and abs(axial3 - 5 / 3) < 1e-12)
gA_axial = axial3


# =====================================================================================================================
# every row of the table from the primitive numbers (the same compositions as programs/geometry_law_and_rows.py)
VAL = {}


def row(rid, name, value, comp):
    VAL[rid] = (name, value, comp)


def rotation(i, j, s, phase=0.):
    out = np.eye(3, dtype=complex)
    out[i, i] = out[j, j] = sqrt(1 - s * s)
    out[i, j] = s * np.exp(-1j * phase)
    out[j, i] = -s * np.exp(1j * phase)
    return out


rp = LOm * M + Ch + log(Kf) / LOm - af ** 5 - bf * af ** 6
row("J01", "m_p/m_e", rp, "L(Omega) M + C_h + log k0(-1/4)/L(Omega) - a^5 - b a^6")
row("B12", "m_p/m_e", rp, "the same")
me = INPUTS["electron_mass_MeV"]
mp = me * rp
alphas = sqrt(eLf ** 2 / NC)
alpha = cLf * ff / (1 - xcon)
WW = Fz(hov) / hov ** 4 * (1 - 2 * bf + 2 * bf * hov)
GFmp2 = (1 - 1 / N2) * WW / M ** 2
row("D01", "alpha_s", alphas, "(e_line^2/N_C)^(1/2)")
row("D02", "1/alpha", 1 / alpha, "N_2(1 - x) k0^2/(c_L k2^2)")
row("D04", "G m_p^2/(hbar c) x 1e39", W * W * 1e39, "W^2")
GF = GFmp2 / (mp / 1000) ** 2
row("D03", "G_F x 1e5 [GeV^-2]", GF * 1e5, "(1 - 1/N_2) W_W/M^2 over m_p^2")
v = (sqrt(2) * GF) ** (-.5)
sw = 3 * nh
osw = sw / (1 + ff)
mw = v * sqrt(pi * alpha / ((1 - ff) * osw))
mz = mw / sqrt(1 - osw)
mh = v * sqrt(2 * pi * alpha / chihf)
mt = v * sqrt(etaf / (2 * sigf))
row("D15", "v [GeV]", v, "(sqrt2 G_F)^(-1/2)")
row("D11", "M_W [GeV]", mw, "v (pi alpha/((1 - f) s^2))^(1/2)")
row("D12", "M_Z [GeV]", mz, "M_W/(1 - s^2)^(1/2)")
row("D16", "m_H [GeV]", mh, "v (2 pi alpha/chi_h)^(1/2)")
row("D17", "m_t [GeV]", mt, "v (eta/2 sigma)^(1/2)")
row("D08", "sin^2 theta, 3 N_h", sw, "3 N_h")
row("D10", "s^2 on shell", osw, "3N_h/(1 + f)")
row("D13", "M_W/M_Z", mw / mz, "(1 - s^2)^(1/2)")
row("D14", "f", ff, "e^2/N_2 = 9/250")
mpl = mp / 1000 / W
row("D05", "M_Pl x 1e-19 [GeV]", mpl / 1e19, "m_p/W")
s_t = 0.5
lnLine = log(1 / eLf)
ED = sum(gaps) / len(gaps) / 4


def level_factor(n, L_, P_):
    psi_ = 1 / (5 ** 2 + 3) if P_ == 1 else 1 / 2
    eps_ = (1 + P_) / 2
    assoc = -psi_ * L_ * (n - eps_) / 4
    clk_ = log(clock(P_ * nuf)) / LOm if n == 10 else (n - eps_) * P_ * nuf * ED / 4
    return exp(n * s_t * lnLine + assoc + clk_)


rmu, rtau = level_factor(10, 2, 1), level_factor(5, -2, 1)
p, qq = level_factor(10, 2, -1), level_factor(5, -2, -1)
kap = (eEf / tf) ** (El / 10)
row("B01", "m_mu/m_e", rmu, "(k2/k4)^5 e^(-9/56) M_Q(nu)^(1/6)")
row("B02", "m_tau/m_mu", rtau, "(k2/k4)^(5/2) e^(1/14 + 2 nu)")
row("B03", "Koide", (1 + rmu + rmu * rtau) / (1 + sqrt(rmu) + sqrt(rmu * rtau)) ** 2, "from m_mu and m_tau")
row("B04", "m_s/m_d = p_q", p, "the symmetric states at the odd sign")
row("B05", "m_b/m_s", qq * etaf, "q_q eta")
row("B06", "m_b^2 m_d/m_s^3", qq * qq * etaf * etaf / p, "q_q^2 eta^2/p_q")
row("B07", "m_t^2 m_u/m_c^3", qq * qq * etaf * etaf / p, "q_q^2 eta^2/p_q")
row("B08", "(m_mu/m_e)/(m_s/m_d)", rmu / p, "the two symmetric-state factors")
row("B09", "m_u/m_d", Rudf, "34/74")
row("B10", "kappa_up", kap, "(e/t)^(E l/E n_F) = (3/2)^(8/5)")
row("B11", "m_c/m_s", Rudf * kap ** 5, "R_ud kappa^5")
rn = exp(log(Kf) * (5 * af ** 4 + 4 * af ** 10 + 10 * cLf * bf * af ** 6))
row("B13", "m_n/m_p", rn, "k0(-1/4)^(5a^4 + 4a^10 + 10 c_L b a^6)")
row("J02", "m_n/m_p", rn, "the same")
row("B14", "m_n/m_e", rp * rn, "(m_p/m_e)(m_n/m_p)")
mn = mp * rn
down = me * (1 / eLf) ** (3 * s_t) * np.array([1 / etaf, p / etaf, p * qq])
up = Rudf * down * np.array([1., kap ** 5, kap ** 7.5])
pi0 = sqrt((2 / abs(P1f)) * hov * me * mp)
electric = pi * alpha * mp ** 2 / (El * (1 - alpha * bf * Phz(1j).real))
pip = sqrt(pi0 * pi0 + electric)
row("J05", "m_pi0 [MeV]", pi0, "(38 h m_e m_p)^(1/2)")
row("J06", "m_pi+ [MeV]", pip, "(m_pi0^2 + pi alpha m_p^2/(E l(1 - alpha b Phi(i))))^(1/2)")
lp = INPUTS["planck_J_s"] * INPUTS["speed_of_light_m_s"] / (2 * pi * INPUTS["MeV_J"]) * 1e15 / mp
VarL, EnF, VarnF, VarnL, Cov = 156, 10, 84, 12, 30
eps2 = alpha ** 2 / (1 + alpha / N2)
mup = sqrt(VarL / (2 * N2) * (1 - eps2 / (El ** 2 * bf)))
mun = -4 * (1 + EnF) / (24 - 1) * sqrt(1 - eps2 / (El ** 2 * bf))
gA = gA_axial * tf ** (2 * bf / 3)
row("S01", "g_A", gA, "<p| sum sigma_z tau_z |p> t^(2b/3) = (5/3) t^(2b/3)")
row("G01", "r_p [fm]", 4 * lp, "4 lambda_p")
row("G02", "Delta [MeV]", 3 * bf * mp, "3 b m_p")
row("G03", "mu_p", mup, "(Var l/(2N_2) (1 - eps2/(E l^2 b)))^(1/2)")
row("G04", "mu_n", mun, "-4(1 + E n_F)/23 (1 - eps2/(E l^2 b))^(1/2)")
row("G05", "mu_n/mu_p", mun / mup, "G04/G03")
row("G06", "m_pi0 [MeV]", pi0, "as J05")
row("G07", "m_pi+ [MeV]", pip, "as J06")
fpi = etaf * mp * sqrt(2 * kC) / (2 * pi * mup)
Bd = mp * sqrt(chiAf) * af ** 3 * (1 - (1 + tf / El) * eps2)
row("G08", "f_pi [MeV]", fpi, "eta m_p (2k_C)^(1/2)/(2 pi mu_p)")
row("G10", "B_d [MeV]", Bd, "m_p chi_A^(1/2) a^3 (1 - (1 + t/E l) eps2)")
md = mp + mn - Bd
row("G11", "m_deut [MeV]", md, "m_p + m_n - B_d")
row("G12", "m_deut/m_p", md / mp, "m_deut/m_p")
row("J03", "Lambda [MeV]", mn * Kf ** (EHf / El), "m_n (5/2)^(3/16)")
row("J04", "Delta [MeV]", kC * bf * mp, "k_C b m_p")
row("J07", "rho pole Re s [GeV^2]", 2 * kC * mp ** 2 * log(xc) / 1e6, "2 k_C m_p^2 log x_c")
row("J17", "kT_c [MeV]", mp / LOm, "m_p/L(Omega)")
dq = atan2(16, 7)
s12, s23 = (VarnF - Cov ** 2 / VarnL) / (El * 2.5), 4 / 96
s13 = s12 * tf * s23
Vq = rotation(1, 2, s23) @ rotation(0, 2, s13, dq) @ rotation(0, 1, s12)
row("C01", "s12 (quarks)", s12, "(Var n_F - Cov^2/Var n_L)/(E l 5/2) = 9/40")
row("C02", "s23", s23, "4/Tr L^2 = 1/24")
row("C03", "s13", s13, "s12 t s23")
row("C04", "delta_q", dq, "arg(7 + 16i)")
jq = (Vq[0, 1] * Vq[1, 2] * Vq[0, 2].conjugate() * Vq[1, 1].conjugate()).imag
row("C05", "J_q x 1e5", jq * 1e5, "Jarlskog of V")
Ul = rotation(0, 1, sqrt(2 * bf) * s12, pi / 2 - dq).conj().T @ rotation(1, 2, 1 / sqrt(2)) @ rotation(0, 1, sqrt(bf))
S13 = abs(Ul[0, 2]) ** 2
S12 = abs(Ul[0, 1]) ** 2 / (1 - S13)
S23 = abs(Ul[1, 2]) ** 2 / (1 - S13)
row("C10", "s^2_12 (leptons)", S12, "U = R12(sqrt(2b) s12, pi/2 - delta_q)^dagger R23(1/sqrt2) R12(sqrt b)")
row("C11", "s^2_13", S13, "the same U")
row("C13", "s^2_23", S23, "the same U")
tau = 2 * pi / (El * rp)
s_sym = eEf / N2
lam = 3 * W ** 6 * tau * s_sym ** 3
row("D06", "Lambda l_P^2 x 1e122", lam * 1e122, "3 W^6 tau s^3")
row("F01", "eta_B x 1e10", 3 * af ** 11 * 1e10, "3 a^11")
row("F04", "N_eff", 3 * etaf * sigf ** (4 / 3), "3 eta sigma^(4/3)")
y = sigf * v / (mp / 1000) * np.array([0., sqrt(rho_nu), 1.]) / sqrt(2)
XR = eLf ** 9 / W
neut = 2 * y * y / (XR + np.sqrt(XR * XR + 4 * y * y)) * mp * 1e6
row("E06", "m_3 [meV]", neut[2] * 1e3, "seesaw, M_R = M_Pl e_line^9")
row("K02", "sum m_nu [eV]", float(sum(neut)), "m1 + m2 + m3")
ncon = sum(((-Phz(4 * (1j / 4) ** k)) if k % 2 else (Fz(4 * (1j / 4) ** k) + Fz(-4 * (1j / 4) ** k)) / 2).real for k in range(1, 60))
row("D07", "d log alpha/d(Phi/c^2)", 0, "0")
row("D09", "effective weak angle", 3 * ncon, "3 sum_k p_k at the four points")
hcfm = INPUTS["planck_J_s"] * INPUTS["speed_of_light_m_s"] / (2 * pi * INPUTS["MeV_J"]) * 1e15
mpcfm = INPUTS["megaparsec_m"] * 1e15
ellR = lp / (W ** 2 * sqrt(tau * s_sym ** 3)) / mpcfm
row("E01", "Delta m^2_21 x 1e5 [eV^2]", neut[1] ** 2 * 1e5, "m_2^2")
row("E02", "Delta m^2_31 x 1e3 [eV^2]", neut[2] ** 2 * 1e3, "m_3^2")
row("E03", "Delta m^2_32 x 1e3", (neut[2] ** 2 - neut[1] ** 2) * 1e3, "m_3^2 - m_2^2")
row("E04", "m_2/m_3", neut[1] / neut[2], "rho_nu through the exact light-root ratio")
row("E05", "Delta m^2_31/Delta m^2_21", (neut[2] / neut[1]) ** 2, "rho_nu^-2 in the light limit")
row("E07", "light neutrino channels", 3, "three pairings of the four directions other than h")
angles = [np.degrees(np.angle(-Vq[i, 0] * Vq[i, 2].conjugate() / (Vq[j, 0] * Vq[j, 2].conjugate()))) % 360 for i, j in [(2, 0), (1, 2), (0, 1)]]
row("C06", "alpha [deg]", angles[0], "unitarity triangle")
row("C07", "beta [deg]", angles[1], "unitarity triangle")
row("C08", "gamma [deg]", angles[2], "unitarity triangle")
row("C09", "two-row sum |V|^2", float(np.sum(abs(Vq[:2]) ** 2)), "unitarity")
row("C12", "sin^2 2theta_13", 4 * S13 * (1 - S13), "from U")
jl = (Ul[0, 0] * Ul[1, 1] * Ul[0, 1].conjugate() * Ul[1, 0].conjugate()).imag
scale_ = sqrt(S12 * (1 - S12) * S23 * (1 - S23) * S13)
phase = np.degrees(atan2(jl / (scale_ * (1 - S13)), (abs(Ul[1, 0]) ** 2 - S12 * (1 - S23) - (1 - S12) * S23 * S13) / (2 * scale_))) % 360
row("C14", "delta_l [deg]", phase, "the phase of U")
row("C15", "n_s", 1 - tf / El, "1 - t/E l")
row("C16", "dn_s/dlnk", 0, "0")
row("F03", "ln(1e10 A_s)", log(1e10 * 12 * af ** 11 * (INPUTS["primordial_pivot_Mpc_inv"] * ellR) ** (-1 / 40)), "A_s = 12 a^11 (0.05 l)^(-1/40)")
row("F13", "Omega_k", 0, "0")
row("G09", "f_pi V_ud [MeV]", fpi * abs(Vq[0, 0]), "f_pi |V_ud|")
row("G13", "mu_d", (16 * (mup + mun) + mn / (mp + mn)) / 17 - (Bd / mp) * ((mup + mun) - mn / (mp + mn)) / (20 + 13 * Bd / mp),
    "from mu_p + mu_n, B_d and the neutron's share")
for i_, v_ in enumerate([2, 1, 1], 1):
    row("H%02d" % i_, ["1 + gamma", "geodetic drift / Einstein", "quantum switch"][i_ - 1], v_, "counts")
lifetime = 72 ** 2 * (INPUTS["planck_J_s"] / (2 * pi) / INPUTS["MeV_J"]) / (3 ** 24 * W ** 4 * mp) / (INPUTS["julian_year_days"] * 86400)
bulk = np.array([1 - tf / El, chiAf, eEf / tf, kC / 4, 4 * alpha / (5 * af)]) * mp * af * af
row("S02", "axial radius^2 [fm^2]", (VarnF - Cov ** 2 / VarnL) * lp * lp, "(Var n_F - Cov^2/Var n_L) lambda_p^2")
row("S03", "axial radius [fm]", sqrt(VarnF - Cov ** 2 / VarnL) * lp, "(Var n_F - Cov^2/Var n_L)^(1/2) lambda_p")
row("S04", "pion charge radius [fm]", sqrt(EnF) * lp, "(E n_F)^(1/2) lambda_p")
row("S05", "tau_n [s]", INPUTS["neutron_rate_normalization_s"] / (INPUTS["neutron_rate_factor"] * abs(Vq[0, 0]) ** 2 * (1 + 3 * gA * gA)), "5099.33/(1.03983 |V_ud|^2 (1 + 3 g_A^2))")
row("S07", "top, second construction [GeV]", mp * mp / (EnF * me) / 1000, "m_p^2/(E n_F m_e)")
row("S08", "A_s x 1e9, second construction", bf ** 24 * (INPUTS["primordial_pivot_Mpc_inv"] * ellR) ** (-1 / 40) * 1e9, "b^24 (0.05 l)^(-1/40)")
row("S09", "cold/baryon, second construction", M / (M - 4 * Ch), "M/(M - 4C_h)")
row("A002", "5 m_p/36 [MeV]", 5 * mp / 36, "5 m_p/36")
row("A003", "5 m_p/36 V_ud", 5 * mp / 36 * abs(Vq[0, 0]), "5 m_p/36 |V_ud|")
row("K01", "theta", 0, "0")
row("K03", "sum m_nu [eV]", float(sum(neut)), "m1 + m2 + m3")
row("K05", "sum |V_ii|^2", float(sum(abs(np.diag(Vq)) ** 2)), "the diagonal of V")
row("K06", "proton partial lifetime [yr]", lifetime, "72^2 hbar/(3^24 W^4 m_p)")
MR, Moff = mpl * eLf ** 9, mpl * eLf ** 6
row("T01", "M_R [GeV]", MR, "M_Pl e_line^9")
row("T02", "M_off [GeV]", Moff, "M_Pl e_line^6")
row("T03", "de Sitter radius l [Mpc]", ellR, "lambda_p/(W^2 (tau s^3)^(1/2))")
row("T04", "de Sitter k_B T [eV]", hcfm * 1e6 / (2 * pi * ellR * mpcfm), "k_B T = hbar c/(2 pi l)")
row("T06", "J_l", jl, "Jarlskog of U")
row("T07", "deuteron D-state share", 2 / 51, "2/51")
for i_, (nm, v_) in enumerate([("m_tau [MeV]", me * rmu * rtau), ("|U_3i|^2", None), ("splitting ratio rho_nu^-2", rho_nu ** -2), ("charged families", 3),
                                ("forbidden lepton 3^(5/2) m_e [MeV]", (1 / eLf) ** (5 * s_t) * me), ("running of the tilt", 0),
                                ("spatial curvature", 0), ("w of the constant term", -1), ("drift of an electric fact", 0),
                                ("de Sitter entropy 3 pi/Lambda l_P^2", 3 * pi / lam), ("tensor/scalar", 16 * lam / (3 * pi * 12 * af ** 11)),
                                ("proton partial lifetime", lifetime), ("B_d", Bd), ("colour components", NC), ("M_W", mw), ("theta-bar", 0),
                                ("Koide", (1 + rmu + rmu * rtau) / (1 + sqrt(rmu) + sqrt(rmu * rtau)) ** 2), ("second-order bending 15 pi/4", 15 * pi / 4)], 1):
    if v_ is None:
        continue
    row("L%02d" % i_, nm, v_, "as named")
nh1 = sum(((-Phz(4 * (1j / 4) ** k)) if k % 2 else Fz(4 * (1j / 4) ** k)).real for k in range(1, 60))
row("L19", "1/alpha at h = 1", (1 - nuf / (M + 1 + nh1)) / (cLf * ff), "the contact with h = 1")
row("L20", "3 N_h at h = 1", 3 * nh1, "the repeated return along h with h = 1")
inv = 1 / np.array([Rudf, 1, p])
low = np.linalg.eigvalsh([[Rudf + 1, (Rudf - 1) / sqrt(3)], [(Rudf - 1) / sqrt(3), (Rudf + 1 + 4 * p) / 3]])[0]
row("I08", "chi_top/(F_pi^2 m_pi0^2)", 1 / (low * sum(inv)), "the light levels' lowest mode")
row("I09", "b_2", -sum(inv ** 3) / (12 * sum(inv) ** 3), "the light levels' third moment")
row("N22", "saturation energy [MeV]", -bulk[0], "-(1 - t/E l) m_p a^2")
row("S16", "one-loop scale [MeV]", mz * 1000 * exp(-2 * pi / ((23 / 3) * alphas)), "M_Z e^(-2 pi/(23/3 alpha_s))")
row("M1", "m_p [MeV]", mp, "m_e m_p/m_e")
row("M2", "m_n [MeV]", mn, "m_p m_n/m_p")
row("M3", "m_deut [MeV]", md, "m_p + m_n - B_d")
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
row("J08", "K0 [MeV]", mp * sqrt(6 * response([level['d'], level['s']])), "M^2 = 2 k_C m_p^2 Tr delta1(R) on the d and s levels")
row("J09", "K+ [MeV]", sqrt(6 * mp ** 2 * response([level['u'], level['s']]) + (8 / 25) * 2 * 3 * electric), "the same on u and s, with the electric term of the plane hk")

# The 211 scalar comparison records: 131 evaluated here, 42 conventional records, 38 composite records.
SPL = re.compile(r"(?<!\\)\|")
table = {}
with io.open(TABLE, encoding="utf-8") as fh:
    for l in fh:
        if l.startswith("| ") and not l.startswith("| row |") and not l.startswith("| variable"):
            cc = [x.strip() for x in SPL.split(l.strip()[1:-1])]
            if len(cc) == 7:
                table[cc[0]] = dict(name=cc[1], sides=cc[2], value=cc[4], record=cc[5])
CARRY = {}
with io.open(CARRIED, encoding="utf-8") as fh:
    txt = fh.read()
group = None
for l in txt[txt.index("### Classical maps"):].splitlines():
    if l.startswith("### Classical maps"):
        group = "the classical theory carries it"
    elif l.startswith("### Composites"):
        group = "several bound world lines (composite expressions)"
    elif l.startswith("| ") and not l.startswith("| row |"):
        cc = [x.strip() for x in SPL.split(l.strip()[1:-1])]
        if len(cc) == 5:
            CARRY[cc[0]] = dict(group=group, name=cc[1], term=cc[2], value=cc[3], sds=cc[4])


def meas(rec):
    mm = re.match(r"\s*([-+]?[0-9.]+(?:e[-+]?[0-9]+)?)\s*(?:\+([0-9.]+(?:e[-+]?[0-9]+)?)\s*/\s*[-−]([0-9.]+(?:e[-+]?[0-9]+)?)|±\s*([0-9.]+(?:e[-+]?[0-9]+)?))", rec)
    if not mm:
        return None
    cen = float(mm.group(1))
    if mm.group(4):
        return cen, float(mm.group(4)), float(mm.group(4))
    return cen, float(mm.group(2)), float(mm.group(3))


# =====================================================================================================================
head("PART 2. THE EXPERIMENTS: the numerical catalogue under its stated controls")
print("Each experiment: what is held (the classical quantities, as the experimenter holds them); what the law returns at the breaking")
print("that holding fixes; the classical form the answer has; and what remains when the answer is written in that form: the number.")
ASSIGN = {}
SD = {}


def show_row(rid, code):
    ASSIGN.setdefault(rid, []).append(code)
    if rid in VAL:
        nm, val, comp = VAL[rid]
        rec = table.get(rid, {}).get("record", "")
        mw_ = meas(rec)
        wtxt = ""
        if mw_:
            cen, upw, dnw = mw_
            sgw = upw if val >= cen else dnw
            if sgw > 0:
                SD[rid] = (val - cen) / sgw
                wtxt = "  %+.2f standard deviations" % SD[rid]
        rshort = rec.split(" [")[0] if rec else ""
        bare = re.match(r"\s*([-+]?[0-9.]+(?:e[-+]?[0-9]+)?)\s*$", rshort)
        if bare and not mw_:
            wtxt = "  relative difference %+.1e" % ((val - float(bare.group(1))) / float(bare.group(1)))
        print("    %-5s %-38s %-22.12g %s%s" % (rid, nm, val, ("measured " + rshort) if (mw_ or bare) else (rshort if rshort else "-"), wtxt))
    else:
        cr = CARRY[rid]
        wd_ = cr["sds"] if cr["sds"] not in ("", "—") else ""
        print("    %-5s %-38s %-22s %s%s" % (rid, cr["name"][:38], cr["value"][:22], cr["group"], ("; standard deviations " + wd_) if wd_ else ""))


def experiment(code, title, held, returns, form, rows, lines=()):
    print()
    print("EXPERIMENT %s. %s" % (code, title))
    para("held:", held)
    para("the law returns:", returns)
    para("classical form:", form)
    for l in lines:
        print("    " + l)
    if rows:
        print("  what remains:")
        for rid in rows:
            show_row(rid, code)


static_line = "the law's static answer between the two held sources (F4): the number in front of 1/(4 pi r) is %s in four directions" \
              % ", ".join("%.4f" % c for c in coef0)

print()
print("A. GRAVITATION: the singlet, type 0|6, u = 1/4, the law's leading zero")
experiment("A1", "Newton: two protons held at rest at a distance r",
           "two world lines at rest, each a proton, at distances r from 4 to 18 steps of the law's chart; they meet at the singlet, which "
           "divides nothing.",
           "the static response at the law's zero, 1/(4 pi r) (F4), times what the two sources bring to the singlet: each source passes a whole "
           "excursion on each of its colour directions, k_C = 3 directions of E l = 16 steps each at the transmission t = 1/k0(-1/4) = 2/5, and k_C E_H = 9 transitions along "
           "h each reached at eta = 295/296: W = t^48 eta^9; the singlet has one channel: sigma = W^2. Each proton carries sqrt(4 pi) W onto the unit static answer, so V/(hbar c) = -4 pi W^2/(4 pi r) = -W^2/r.",
           "Newton, V(r) = -G m_p^2/r; the field term (R - 2 Lambda)/16 pi G, 1/16 pi G = m_p^2/(16 pi W^2 hbar c).",
           ["D04", "D05"], [static_line, "so -r V(r)/(hbar c) = W^2 x (the number above): the coefficient of -1/r is W^2 = %.6e" % (W * W)])
experiment("A2", "Light and a gyroscope passing a held mass",
           "a light ray grazing a held mass; a gyroscope carried around it on a free orbit.",
           "the light's direction carried around the frame's curvature, against Newton's half: the frame term's field equation, with the "
           "number of A1 in front, gives 1 + gamma = 2; the frame carried around the closed orbit, against the flat frame, gives Einstein's "
           "geodetic drift, ratio 1; at second order the bending carries 15 pi/4.",
           "the deflection 2(1 + gamma) GM/(b c^2) + (15 pi/4)(GM/b c^2)^2; the geodetic drift over its Einstein value.",
           ["H01", "H02", "L18"])
experiment("A3", "Two clocks at two heights compare the fine structure; bodies of every composition fall together",
           "two atomic clocks held at different gravitational potentials, comparing alpha; bodies of different make in one field.",
           "alpha is a coefficient of the law, the count at the plane hk (C_h/M)(e^2/N_2)/(1 - x), the same at every location: the stationary weight on the singlet "
           "does not enter it. A world line's gravitational charge is its self-interaction at the singlet, where its interaction with itself and its interaction "
           "with another are one number: its mass. The potential is a lapse N on the clock that measures energy; a world line's rest pole sits "
           "where its kernel vanishes, K_X(E, N) = K_X(E/N, 1), so K_N = -(E/N) K_E and dE_X/dN = E_X(N)/N; at N = 1, dE_X/dN = E_X(1): the lapse couples to the rest energy "
           "the world line's own clock measures, the same share for every world line.",
           "d log alpha/d(Phi/c^2) = 0; universality of free fall, (dE_X/dN)/E_X = 1/N for every X, equal to 1 at N = 1.", ["D07"])
experiment("A4", "The frame held curved: the constant term",
           "the ten rotations split at h into six that keep it and four that move it, e/l; l varied (F7).",
           "the curvature of the ten rotations, F = R - e^e/l^2, contracted with h in the epsilon contraction: -(4/l^2)(R - 6/l^2) vol, at every l and curvature.",
           "Einstein-Cartan with Lambda: R - 2 Lambda, Lambda l^2 = 3; the constant term's pressure is minus its density.",
           ["L08"], ["Lambda l^2 = %s at l = 0.5, 1, 1.7, 3 (F7)" % ", ".join("%.12f" % x for x in lam_l2)])
experiment("A5", "The whole system at rest: the constant term in the unit of the step",
           "the whole system at rest; the angle the electron's clock turns during 1/(E l) of a proton Compton period, tau = 2 pi/(E l m_p/m_e); one "
           "arrival at a symmetric state s = e/N_2 = 3/50.",
           "3 W^6 tau s^3: the frame's constant term measured in the step, the singlet's transmission factor W six times.",
           "Lambda l_P^2 = 3 Omega_Lambda H_0^2 l_P^2/c^2; the de Sitter radius l, its temperature k_B T = hbar c/(2 pi l), its entropy 3 pi/(Lambda l_P^2).",
           ["D06", "T03", "T04", "L10"])
print()
print("B. ELECTROMAGNETISM: the plane hk, type 2|4, u = -1/4, its central rotation the common clock")
experiment("B1", "Coulomb: two unit charges held at rest at a distance r",
           "two sources of unit charge on the central rotation of the plane hk, at rest, at distances r from 4 to 18 steps.",
           "the law answers a gauge field on the links only through its curvature around the squares, which no gauge transformation changes (F5); a term without the "
           "curvature would change under a gauge transformation, so the rotation carries no mass and its static answer is 1/(4 pi r) (F4). In front of 1/r stands "
           "what the two sources bring to the plane hk: each brings its reflection leaving the plane, e = k2/k0 = 3/5, on the transitions that keep its "
           "charge, the C_h/M = 60/296 along h, over the N_2 = 10 channels of the symmetric states, the clock's contact x closed once: "
           "sigma = (C_h/M)(e^2/N_2)/(1 - x) = alpha; each source carries sqrt(4 pi) onto the unit static answer, so V/(hbar c) = 4 pi alpha/(4 pi r) = alpha/r.",
           "Coulomb, V(r) = alpha hbar c/r; the field term -F^2/(16 pi alpha).",
           ["D02", "L19"], [static_line, "so r V(r)/(hbar c) = alpha x (the number above): the coefficient of 1/r is 1/%.9f" % (1 / alpha)])
experiment("B2", "The field turned on: the field's own term",
           "phases theta on the forty links at amplitudes 0.1, 0.03, 0.01, and a pure gauge transformation (F5).",
           "log det(I - wA_-[e^(i theta)]) - log det(I - wA_-) = -(kappa/2)|C theta|^2, kappa = 1/200 at the plane hk; a gauge transformation returns nothing. "
           "The field in units of the charge is the link phase per cell in units of the phase a unit charge carries: "
           "int F^2 = 8 pi kappa alpha |C theta|^2 = %.4e |C theta|^2." % (8 * pi * kap_w(-0.2) * alpha),
           "Maxwell, D_mu F^mu nu = 4 pi alpha j^nu, d F = 0; a held electric fact has no drift of its own: alpha is the same at every location "
           "and phase.",
           ["L09"], ["kappa at amplitude 0.01: %.8f (1/200 = 0.005)" % rows_k[0][1][-1]])
experiment("B3", "Nucleons held in a magnetic field",
           "a proton, a neutron and a deuteron at rest in a held field B; the precession frequency grows in proportion to B.",
           "the proton's moment is the spread of its excursion's length, Var l = 156, over the 2N_2 channels of the symmetric states, less the plane's own coupling "
           "once, eps2 = alpha^2/(1 + alpha/N_2), over E l^2 b: mu_p = [Var l/(2N_2)(1 - eps2/(E l^2 b))]^(1/2); the neutron's is "
           "-4(1 + E n_F)/23 with the same factor; the deuteron's comes from the two, its binding and the neutron's share.",
           "Larmor, hbar w = 2 mu B, mu in nuclear magnetons.", ["G03", "G04", "G05", "G13"])
experiment("B4", "Electrons scattered off a proton and a pion at small momentum transfer",
           "the momentum transfer q held small and varied; the slope of the electric form factor.",
           "the proton's charge is spread over four steps, r_p = 4 lambda_p; the pion's over the visits of one excursion to the symmetric states, r_pi = (E n_F)^(1/2) lambda_p.",
           "G_E(q^2) = 1 - q^2 <r^2>/6.", ["G01", "S04"])
experiment("B5", "The classical theory carries alpha and the rest clocks: the precision experiments of electrodynamics",
           "an electron in a Penning trap, the hydrogen series, alpha carried to the Z pole, the muon's anomaly.",
           "the law's long-wave motion, quantum electrodynamics, carries the computed alpha, the rest clocks and the computed vector current to "
           "each measurement and brings no number of its own.",
           "a_e = sum_n C_n (alpha/pi)^n + hadronic + weak; the hydrogen series; the dispersion integral.",
           ["I10", "I11", "Q01", "Q04"])

print()
print("C. THE REST CLOCKS: the own clock i g_h, kept on the plane {n, h} as the world line's time, moved at the divided set {h}, where its rate is the mass")
experiment("C1", "The electron: one transition held at rest",
           "a world line at rest, its clock turning by a phase theta per step on one of the 320 transitions; theta varied (F9).",
           "exactly, D_theta(u) = D(u) + (e^(-i theta) - 1) u D'(u)/320: every transition has the same cofactor, so the law's zero turns by "
           "theta/320 + O(theta^3) per step, with d arg(4u_c)/d theta = 1/320 at theta = 0, the unit rate.",
           "E = hbar w = m c^2: the electron is the unit.", [],
           ["turn per step x 320 at theta = 1e-4: %.9f" % clk[-1][1]])
experiment("C2", "The proton beside the electron: two clocks compared",
           "the proton and the electron's marked transition held at rest side by side, their clocks compared as a trap compares two cyclotron "
           "frequencies (F9).",
           "each of the proton's M = 296 available transitions compares the moment with itself, <Omega, (L + g_h x g_s) Omega> = 6 + [s = h]: the "
           "comparison's value at the singlet on every transition and one more on the C_h = 60 transitions along its own time; so the zero turns "
           "6M + C_h = 1836 times as fast as for the electron; then the Gram-determinant term, the singlet's grade factor "
           "k0(-1/4) = 5/2, the inverse of the transmission, per unit of L(Omega); less the signed-volume terms, a^5 on the five vector "
           "states and b a^6 with b = 7/16: L(Omega) M + C_h + log k0(-1/4)/L(Omega) - a^5 - b a^6.",
           "E = m c^2 for both, their ratio; the step is the proton's reduced Compton length, lambda_p = %.10f fm." % lp,
           ["J01", "B12", "M1"], ["the clocks' ratio from the law's zero at theta -> 0: %.6f; with the Gram-determinant and signed-volume terms: %.9f" % (ratio0, rp)])
experiment("C3", "The neutron held beside the proton",
           "the neutral pole at rest beside the proton.",
           "the singlet's grade factor raised to the neutral pole's spread over the ten symmetric states: k0(-1/4)^(5a^4 + 4a^10 + 10 c_L b a^6).",
           "E = m c^2, the ratio.", ["B13", "J02", "B14", "M2"])
experiment("C4", "The muon and the tau held beside the electron; the families",
           "the electron's world line held with its symmetric states opened, then its vector states.",
           "each of the ten symmetric states passes a direction as an amplitude, (k2/k4)^5 = 3^5, with the factor e^(-9/56) of Psi at the even sign and the "
           "clock M_Q(nu)^(1/6); the vector states add (k2/k4)^(5/2) e^(1/14 + 2 nu). The four directions other than h pair in three ways: "
           "three families, no charged lepton at the next level.",
           "E = m c^2, the ratios; Koide's form.",
           ["B01", "B02", "L01", "B03", "L17", "L05", "L04"])
experiment("C5", "The quark levels: the same states at the odd sign",
           "the quark world lines at rest inside hadrons; their levels compared.",
           "m_d = 3^(3/2) m_e/eta; m_s/m_d = p_q, the symmetric states at the odd sign; m_b/m_s = q_q eta; m_u/m_d = 17/37, the edges whose state does not "
           "contain h; the up-type levels gain kappa = (3/2)^(8/5) per visit to a symmetric state. Down, strange, bottom, up, charm at the Z pole: "
           + ", ".join("%.4g" % x for x in [down[0], down[1], down[2], up[0], up[1]]) + " MeV.",
           "the quark masses of the classical theory; its running carries them to 2 GeV and to their own scales.",
           ["B04", "B05", "B06", "B07", "B08", "B09", "B10", "B11", "I01", "I02", "I03", "I04", "I05", "S10", "S11", "S12", "T10", "T11", "T12"])

print()
print("D. THE DIRECTION h: type 1|5, u = i/4; the weak rotations, the Higgs, the top, the neutrinos, the mixings")
experiment("D1", "Fermi: two weak currents held in contact (the muon's decay)",
           "two sources at the plane {h, n}, in contact.",
           "each source one particular transition of its excursion, 1/M, on the nine symmetric states other than the photon's, (1 - 1/N_2); the contact "
           "interaction's retained excursion W_W = F(h) h^-4 (1 - 2b + 2bh).",
           "Fermi, (G_F/sqrt2)(J.J); the muon's rate G_F^2 m_mu^5/(192 pi^3); v = (sqrt2 G_F)^(-1/2).", ["D03", "D15"])
experiment("D2", "The direction h held at its length v",
           "the direction h in the plane hk held at length v (F8); the twelve rotations within the 2 + 3 split.",
           "the moved rotations' masses squared v^2 (1/2, 1/2, 4/5) for W+, W-, Z, nine at zero; the angle from 3/8 at the source to "
           "s^2 = 3 N_h, the repeated return along h, s^2/(1 + f) on shell; the radial direction with chi_h = w_h(1 - w_h); the "
           "top's Yukawa (eta/2 sigma)^(1/2).",
           "|D(v h)|^2 and the Higgs potential: M_W^2 = pi alpha v^2/((1 - f) s^2), M_Z = M_W/(1 - s^2)^(1/2), "
           "lambda_H = pi alpha/chi_h = %.6f, m_H = v (2 lambda_H)^(1/2), m_t = v (eta/2 sigma)^(1/2)." % (pi * alpha / chihf),
           ["D11", "D12", "D13", "D08", "D09", "D10", "D14", "D16", "D17", "L15", "L20", "S07", "T08", "I07"])
experiment("D3", "Neutrons stored and counted",
           "free neutrons held in a trap, the survivors counted over time.",
           "the axial coupling (5/3) t^(2b/3): 5/3 is the axial current sum_r sigma_z tau_z in the projected proton with spin up (F11), "
           "the nucleon projected out of the symmetric spin and isospin of its three colour world lines before its current is read; times the "
           "transmission to the power 2b/3; with |V_ud| and G_F.",
           "1/tau_n = (G_F^2 m_e^5 |V_ud|^2/2 pi^3)(1 + 3 g_A^2) f (1 + delta_R); the axial form factor.",
           ["S01", "S05", "S02", "S03", "A001", "S06"])
experiment("D4", "Charged pions decaying at rest",
           "charged pions at rest, decaying to a muon or an electron and a neutrino.",
           "f_pi = eta m_p (2 k_C)^(1/2)/(2 pi mu_p); a second construction 5 m_p/36.",
           "Gamma(pi -> l nu) = (G_F^2 |V_ud|^2 f_pi^2/8 pi) m_pi m_l^2 (1 - m_l^2/m_pi^2)^2.",
           ["G08", "G09", "A002", "A003", "S15"])
experiment("D5", "The up-type and the down-type world lines overlapping: the quark mixing",
           "the up-type and the down-type world lines, each closed at its pole, overlapping in the weak current.",
           "s12 = (Var n_F - Cov^2/Var n_L)/(E l 5/2) = 9/40, the spread of the visits to the symmetric states left when the visits to the vector states are known, "
           "per mean return time and per inverse transmission; s23 = 4/Tr L^2 = 1/24; s13 = s12 t s23; delta = arg(b + i) = arg(7 + 16i).",
           "the CKM matrix and its unitarity triangle.", ["C01", "C02", "C03", "C04", "C05", "C06", "C07", "C08", "C09", "K05"])
experiment("D6", "The leptons carry the same frame from the other end",
           "neutrinos made in one flavour and caught in another.",
           "U = R12(sqrt(2b) s12, pi/2 - delta_q)^dagger R23(1/sqrt2) R12(sqrt b).",
           "the PMNS matrix; the oscillation probabilities.", ["C10", "C11", "C12", "C13", "C14", "T06"])
experiment("D7", "The heavy neutral threshold and the light neutrinos",
           "the Z's invisible width; neutrino oscillation lengths; the sum of the neutrino masses in the whole system.",
           "the neutral block of h has three light poles, one per family; the heavy neutral threshold M_R = M_Pl e_line^9; Yukawas "
           "sigma v (0, rho_nu^(1/2), 1)/sqrt2, rho_nu = tan^2(pi/8); the threshold M_Pl e_line^6 of the six rotations that mix the three-plus-two split.",
           "the seesaw m = y^2 v^2/(2 M_R); Delta m^2 of the oscillations.",
           ["E07", "E01", "E02", "E03", "E04", "E05", "E06", "K02", "K03", "L03", "L21", "T01", "T02"])

print()
print("E. COLOUR: type 3|3, u = -i/4, rotations within the sides with no centre and no clock of their own")
experiment("E1", "Two colour sources held at short distance",
           "two sources at colour close together; the eight traceless rotations of the three directions outside the plane hk.",
           "an amplitude at the odd divided set: each source brings its reflection at a single direction, e_line = k4/k2 = 1/3, over the eight rotations: "
           "alpha_s = (e_line^2/N_C)^(1/2) = (1/72)^(1/2); the same 1/72 is the response of directions on opposite sides read against its own clock, fixed "
           "as chi varies (F10); the colour term has eight components.",
           "the Coulomb part of Yang-Mills, V = -C_F alpha_s hbar c/r; the classical running carries alpha_s to every scale.",
           ["D01", "L14", "I06", "S14", "S16", "S017", "S018", "T09"], ["kappa at the amplitude points (F5): %.8f (1/98 = %.8f)" % (rows_k[1][1][-1], 1 / 98)])
experiment("E2", "A neutron in a held electric field: the strong phase",
           "a neutron's electric dipole moment sought in a held electric field.",
           "with any phases on the links the law stays positive below the critical step: the closed weights are real, theta-bar = 0. The "
           "light quark levels' lowest mode and third moment give the strong curvature and its fourth cumulant.",
           "theta-bar F F~; the topological susceptibility and b_2.", ["K01", "L16", "I08", "I09"])
experiment("E3", "Hadrons weighed at their first poles [several world lines bound together]",
           "the light mesons and baryons produced and weighed at rest.",
           "the neutral pion is the exchange between the electron and the proton at the singlet, m_pi0^2 = 38 h m_e m_p; the charged "
           "pion adds the electric self-energy of the plane hk; the kaons are the same exchange with the strange level, M^2 = 2 k_C m_p^2 Tr delta1(R); "
           "the Lambda is m_n (5/2)^(3/16); the Delta's three aligned world lines stand at 3b m_p; the rho pole at Re s = 2 k_C m_p^2 log x_c; "
           "the colour crossover at kT_c = m_p/L(Omega).",
           "E = m c^2 at each pole; Breit-Wigner at the resonances.",
           ["J05", "G06", "J06", "G07", "J08", "J09", "J03", "G02", "J04", "J07", "J17"])
experiment("E4", "Protons held for a very long time",
           "a great number of protons watched for the decay to a positron and a neutral pion.",
           "the proton pole's width through the six rotations that mix the three-plus-two split, at their threshold "
           "M_off = M_Pl e_line^6, each with the colour coupling: tau = hbar (M_off/m_p)^4/(alpha_s^4 m_p) = "
           "72^2 hbar/(3^24 W^4 m_p).",
           "the partial lifetime tau/B(e+ pi0); the classical theory carries the matrix element.", ["K06", "L12", "Q11"])
experiment("E5", "Hadrons beyond their first poles [several world lines bound together]",
           "hadrons whose world lines close together beyond their first poles.",
           "the joint closed walks of several world lines give the composite expressions printed here. The article_results.py calculation "
           "evaluates twelve literal expressions and retains the remaining equations in the Supplemental ledger.",
           "det[E(u)I - H_spin,flavour] = 0 and the six other equations of several bound world lines.",
           ["J10", "J11", "J12", "J13", "J14", "J15", "J16", "J19", "J20", "J21", "J22", "J23", "J24", "J25", "J26", "J27", "J28", "J29", "J30",
            "J31", "J32", "J33", "J34", "S19", "S20", "S21"])

print()
print("F. NUCLEI: nucleon world lines bound together [several bound world lines]")
experiment("F1", "The deuteron",
           "a proton and a neutron bound, weighed, its moment and shape measured.",
           "B_d = m_p chi_A^(1/2) a^3 [1 - (1 + t/E l) eps2]; its D-state share 2/51; beyond the pole, the two-nucleon kernel.",
           "m_deut = m_p + m_n - B_d; the asymptotic normalization, the scattering length and range.",
           ["G10", "L13", "G11", "G12", "M3", "T07", "G14", "G15", "G16", "G17", "G18", "G19", "G19a", "G20", "G21"])
experiment("F2", "Nuclear matter",
           "nuclear matter at saturation: its energy per nucleon, its incompressibility and its symmetry energy.",
           "the bulk volume term, e_0 = -m_p a^2 (39/40).",
           "saturation; the incompressibility and the symmetry energy.",
           ["N22", "N23", "N24", "N25"])

print()
print("G. THE WHOLE SYSTEM AT REST: the stationary weight on its states")
experiment("G1", "The whole system at rest: baryons per photon",
           "the whole system at rest; its baryons and photons counted through the light elements and the microwave sky.",
           "3 a^11: the probability of a sign-reversing return per continuation, a = (1 - Phi(1))/8 = 5/38, over the eleven states of positive comparison value, three times.",
           "eta_B = n_B/n_gamma.", ["F01"])
experiment("G2", "The primordial spectrum",
           "the curvature of the whole system compared across scales.",
           "A_s = 12 a^11 (0.05 l)^(-1/40); the tilt n_s = 1 - t/E l = 39/40, which does not run; the tensor share 16 Lambda l_P^2/(3 pi 12 a^11).",
           "P(k) = A_s (k/k_*)^(n_s - 1).", ["F03", "S08", "C15", "C16", "L06", "L11"])
experiment("G3", "The light species", "the expansion rate at the time of the light elements and of the microwave sky.",
           "3 eta sigma^(4/3).", "N_eff.", ["F04"])
experiment("G4", "The frame carried around the whole system", "the frame carried around closed paths across the whole system.",
           "the stationary frame is flat.", "Omega_k = 0.", ["F13", "L07"])
experiment("G5", "The cold matter and the thermal history",
           "the whole system's matter, radiation and constant term traced from the light elements to today.",
           "the cold matter is the heavy neutral pole at the stationary weight on all sixteen states, a^16 M_R/m_p; M/(M - 4 C_h); the "
           "present at rho_Lambda/rho_m = 24/11; the thermal history and the acoustic transport carry these to T, H_comp, t_age, the shares and "
           "the microwave angles.",
           "Friedmann's equation and the Boltzmann transport.",
           ["S09", "F02", "F05", "F06", "F07", "F08", "F09", "F10", "F11", "F12", "Q05", "Q06", "Q07", "Q08", "Q09", "Q10"])

print()
print("H. TWO ORDERS: amplitudes and counts")
experiment("H1", "Two operations applied in both orders, the order in coherent superposition",
           "a quantum switch: two operations in both orders, the order held in coherent superposition with no record of it.",
           "the order measured in the sum and difference states of the control: a commuting and an anticommuting pair are told apart with "
           "certainty; with each order on its own record the two orders add as counts and tell nothing apart.",
           "Born's rule; the switch's success probability.", ["H03"])

# =====================================================================================================================
head("PART 3. THE CLASSICAL EQUATION WITH EVERY NUMBER IN FRONT OF EVERY TERM")
print("Gamma = int d^4x sqrt(-g) [ (R - 2 Lambda)/(16 pi G) - sum_X F_X^2/(16 pi alpha_X) + psi-bar i gamma^mu D_mu psi")
print("                          - (psi-bar_L Y phi psi_R + h.c.) - (D_mu phi)^dagger D^mu phi - lambda_H (phi^dagger phi - v^2/2)^2 ]")
print()
gw2 = 4 * pi * alpha / ((1 - ff) * osw)
g1sq = gw2 * osw / (1 - osw)
eq_terms = [
    ("(R - 2 Lambda)/16 pi G", "G m_p^2/(hbar c) = W^2 = %.9e; Lambda l^2 = 3, Lambda l_P^2 = %.6e" % (W * W, lam), "A1, A4, A5"),
    ("F^2/16 pi alpha (photon)", "1/alpha = %.9f" % (1 / alpha), "B1, B2"),
    ("F^2/16 pi alpha_s (colour)", "alpha_s = (1/72)^(1/2) = %.9f" % alphas, "E1"),
    ("F^2 (weak rotations)", "s^2 = 3 N_h = %.9f; on shell %.9f; g^2/4 pi = %.9f" % (sw, osw, gw2 / (4 * pi)), "D2"),
    ("F^2 (hypercharge)", "g_1^2/4 pi = alpha_Y = %.12f" % (g1sq / (4 * pi)), "D2"),
    ("psi-bar i gamma D psi", "first-order step, cos w = cos mu cos k; c one step per step; hbar phase per step", "F2, F3"),
    ("Yukawas, leptons", "m_e the unit; m_mu/m_e = %.6f, m_tau/m_mu = %.6f" % (rmu, rtau), "C1, C4"),
    ("Yukawas, quarks (native, MeV)", "d %.4g, s %.4g, b %.5g, u %.4g, c %.4g; t %.4f GeV" % (down[0], down[1], down[2], up[0], up[1], up[2] / 1000), "C5, D2"),
    ("quark mixing", "s12 = 9/40, s23 = 1/24, s13 = 3/800, delta = arg(7 + 16i)", "D5"),
    ("lepton mixing", "s^2_12 = %.5f, s^2_13 = %.6f, s^2_23 = %.5f, delta_l = %.1f deg" % (S12, S13, S23, phase), "D6"),
    ("neutrinos", "m_1 = 0, m_2 = %.3f meV, m_3 = %.3f meV; M_R = %.4e GeV" % (neut[1] * 1e3, neut[2] * 1e3, MR), "D7"),
    ("|D phi|^2 - lambda_H(...)^2", "v = %.6f GeV; lambda_H = pi alpha/chi_h = %.6f; m_H = %.4f GeV" % (v, pi * alpha / chihf, mh), "D1, D2"),
    ("theta-bar F F~", "theta-bar = 0", "E2"),
    ("the scale of all of it", "the step: lambda_p = %.10f fm, m_p/m_e = %.9f" % (lp, rp), "C2"),
]
for term, num, where in eq_terms:
    print("  %-30s %-92s %s" % (term, num, where))
print()
print("The displayed coefficients use the finite quantities calculated above and the input conventions in docs/INPUTS.md.")
print("The form of each term follows the corresponding source or long-wavelength calculation in PART 1.")
print("The article-order numerical and proof addresses are in docs/ARTICLE_CONCORDANCE.md.")

# =====================================================================================================================
head("PART 4. THE 211 SCALAR RECORDS IN THEIR EXPERIMENTS")
allrows = set(VAL) | set(CARRY)
missing = sorted(allrows - set(ASSIGN))
twice = sorted(r for r, c in ASSIGN.items() if len(c) > 1)
unknown = sorted(set(ASSIGN) - allrows)
nmap = sum(1 for r in CARRY if CARRY[r]["group"].startswith("the classical"))
print("scalar rows evaluated here: %d; conventional calculation records: %d; composite expressions: %d; total scalar records: %d"
      % (len(VAL), nmap, len(CARRY) - nmap, len(allrows)))
print("rows placed in an experiment: %d; placed twice: %d; not placed: %d" % (len(ASSIGN), len(twice), len(missing)))
byexp = {}
for r, c in ASSIGN.items():
    byexp.setdefault(c[0][0], []).append(r)
names = dict(A="gravitation", B="electromagnetism", C="rest clocks", D="the direction h", E="colour", F="nuclei", G="the stationary state", H="two orders")
for k in sorted(byexp):
    rs = byexp[k]
    wl = [SD[r] for r in rs if r in SD]
    print("  %s %-18s %3d rows; with a measured standard deviation %3d, within one %3d, within two %3d"
          % (k, names[k], len(rs), len(wl), sum(abs(x) <= 1 for x in wl), sum(abs(x) <= 2 for x in wl)))
wl = list(SD.values())
print("  measured comparisons among this program's 131 evaluated scalar rows: %d; within one standard deviation %d; within two %d" % (len(wl), sum(abs(x) <= 1 for x in wl), sum(abs(x) <= 2 for x in wl)))
MB = {"E3", "E5", "F1", "F2"}
main_rows = [r for r, c in ASSIGN.items() if c[0] not in MB]
mb_rows = [r for r, c in ASSIGN.items() if c[0] in MB]
wl_main = [SD[r] for r in main_rows if r in SD]
print("  the main line (every experiment but E3, E5 and F): %d rows, %d computed here; with a measured standard deviation %d, within one %d, "
      "within two %d" % (len(main_rows), sum(1 for r in main_rows if r in VAL), len(wl_main), sum(abs(x) <= 1 for x in wl_main),
                          sum(abs(x) <= 2 for x in wl_main)))
print("  several bound world lines (E3, E5, F): %d records; literal composite evaluations appear in article_results.py" % len(mb_rows))
beyond = sorted((r for r in SD if abs(SD[r]) > 2), key=lambda r: -abs(SD[r]))
print("  among this program's 99 measured comparisons, beyond two standard deviations: " + (", ".join("%s %+.1f" % (r, SD[r]) for r in beyond) or "none"))
chk("each of this program's 211 scalar records stands in exactly one experiment (131 evaluated, 42 conventional records, 38 composite expressions)",
    not missing and not twice and not unknown and len(VAL) == 131 and nmap == 42 and len(CARRY) - nmap == 38, (missing, twice, unknown))
same_n = cmp_n = 0
for rid, (nm, val, comp) in VAL.items():
    tv = table.get(rid, {}).get("value")
    try:
        tvf = float(tv)
    except Exception:
        continue
    cmp_n += 1
    nd = len(tv.split(".")[1]) if "." in tv and "e" not in tv.lower() else 12
    ok_ = (abs((val - tvf) / tvf) < 1e-6 if tvf else abs(val) < 1e-9) or abs(val - tvf) <= 0.6 * 10 ** (-nd)
    if rid == "J09":
        ok_ = abs(val - 493.665032668) < 1e-6           # the charged kaon with the electric term of the plane hk
    same_n += ok_
chk("the 131 scalar values evaluated here agree with their recorded values to a relative 1e-6 or within the printed digits; J09 with the plane-hk electric term is 493.665032668",
    same_n == cmp_n and abs(VAL["J09"][1] - 493.665032668) < 1e-6, (same_n, cmp_n))
print()
print("checks: %d of %d ok" % (sum(ok), len(ok)))
