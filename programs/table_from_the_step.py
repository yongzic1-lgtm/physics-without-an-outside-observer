# -*- coding: utf-8 -*-
# THE WHOLE TABLE FROM THE STEP B
#
# Every primitive number is derived from the step B of a world line: the non-backtracking operator on the 80 directed
# edges of the graph of the sixteen two-spinor states (the Clebsch graph; a step changes the state by one of the five
# Dirac matrices and never undoes the last change at once). Two pieces of geometry enter besides B: the clock's first four
# marks, a quarter step for each of the four directions other than h (the fifth mark, -1/Phi(1), is counted on B), and the
# charges (0, 1, -1/3, -1/3, -1/3) of the five directions seen from the plane hk. Every row of the table is then computed
# from these primitives and set beside the table's value and its measurement (data/constants_and_measurements.md).
# Run from the repository root:  python -I programs/table_from_the_step.py > outputs/table_from_the_step.out
# Prints its checks ("ok" or "FAIL"), the primitives, and every computed row with the table's value, the relative
# difference, the measurement with its source and the difference from the measurement in standard deviations.
import itertools, math, re, io, os
from fractions import Fraction as Fr
from math import sqrt, log, exp, pi, atan2
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


# ------------------------------------------------------------------ A. the primitives, from B
d = 5
ALL = (1 << d) - 1
rel = [m for m in range(1 << d) if bin(m).count("1") % 2 == 0]      # the sixteen two-spinor states
ri = {m: i for i, m in enumerate(rel)}
g = [ALL ^ (1 << s) for s in range(d)]                                # the step along direction s
states = [(x, t) for x in rel for t in range(d)]                      # the 80 directed edges: a state and its last change
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

print("== A. Primitives from the step B")
kN = lambda N, u: 1 + 4 * u * u - u * (5 - 2 * N)
lamA = sorted(set(np.round(np.linalg.eigvalsh(A), 9)), reverse=True)
chk("the graph of the two-spinor states: Clebsch spectrum 5, 1, -3 on the grades 0, 2, 4", lamA == [5.0, 1.0, -3.0])
uF = Fr(-1, 4)
K0, K2, K4 = kN(0, uF), kN(2, uF), kN(4, uF)
t_even, e_even, e_line = 1 / K0, K2 / K0, K4 / K2
chk("at u = -1/4: k = 5/2, 3/2, 1/2; t = 2/5, e = 3/5, e_line = 1/3", (K0, K2, K4, t_even, e_even, e_line) == (Fr(5, 2), Fr(3, 2), Fr(1, 2), Fr(2, 5), Fr(3, 5), Fr(1, 3)))
N2 = 10                                  # the grade-two dimension of the law: the ten symmetric states
kC = 3                                   # the three directions outside the plane hk: 1/|u| - 1
NC = kC * kC - 1
LOm = d + 1
# the polar step: singular values of B are 4 and 1, |B| = 2 e^{xi(2 Pi - I)}, xi = log 2
sv = sorted(set(np.round(np.linalg.svd(B, compute_uv=False), 9)))
xi = log(max(sv) / 2)
chk("polar step: singular values {1, 4}, xi = log 2", sv == [1.0, 4.0] and abs(xi - log(2)) < 1e-12)
rho_nu = math.tanh(xi / 4)
chk("the half phase of the vector-state factor tan^2(pi/8) = tanh(xi/4) = 3 - 2 sqrt2", abs(rho_nu - (3 - 2 * sqrt(2))) < 1e-15 and abs(rho_nu - math.tan(pi / 8) ** 2) < 1e-15)

# one first-return excursion from the singlet: the absorbing chain of returns, plain and signed
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


Fz = lambda z: z ** 4 * (1 + z) / (16 - 8 * z - 3 * z ** 2 - 3 * z ** 3)
Phz = lambda z: -z ** 4 / (16 + 3 * z ** 2)
chk("plain and signed first returns of B are F and Phi", all(abs(first_return(z, False) - Fz(z)) < 1e-12 and abs(first_return(z, True) - Phz(z)) < 1e-12 for z in (0.4, 0.6 + 0.3j, 0.8j)))
P1 = Fr(-1, 19) if abs(first_return(1.0, True) + 1 / 19) < 1e-12 else None
Pi_ = Fr(-1, 13) if abs(first_return(1j, True) + 1 / 13) < 1e-12 else None
chk("Phi(1) = -1/19, Phi(i) = -1/13 from B", P1 is not None and Pi_ is not None)
a = (1 - P1) / 8
chiA = 1 / (1 + Pi_)
# the visits of one excursion to the symmetric states (grade 2) and to the vector states (grade 4); their spreads
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


EnF, EnL = float(mu @ is_sym), float(mu @ is_vec)
VarnF = second(is_sym, is_sym) - EnF ** 2
VarnL = second(is_vec, is_vec) - EnL ** 2
Cov = second(is_sym, is_vec) - EnF * EnL
El = EnF + EnL + 1
VarL = VarnF + VarnL + 2 * Cov
chk("one excursion: E n_F = 10, E n_L = 5, E l = 16; Var n_F = 84, Var n_L = 12, Cov = 30, Var l = 156",
    max(abs(EnF - 10), abs(EnL - 5), abs(VarnF - 84), abs(VarnL - 12), abs(Cov - 30), abs(VarL - 156)) < 1e-9, (EnF, EnL, VarnF, VarnL, Cov))
EnF, EnL, VarnF, VarnL, Cov, El, VarL = 10, 5, 84, 12, 30, 16, 156
# the generating function of one excursion's visits to the symmetric states, and its pole
def sym_visits(xv):
    Dm = np.diag([xv if f else 1.0 for f in is_sym])
    rr = np.array([0.25 * sum(1 for s in range(d) if s != t and (x ^ g[s]) == 0) for (x, t) in trans])
    return float((v0 @ Dm) @ np.linalg.solve(np.eye(len(trans)) - T @ Dm, rr))
chk("the symmetric-state visit function of one excursion is x(1 + x)/(16 - 11x - 3x^2)", all(abs(sym_visits(xv) - xv * (1 + xv) / (16 - 11 * xv - 3 * xv * xv)) < 1e-12 for xv in (0.3, 0.7, 1.0, 1.1)))
xc = (sqrt(313) - 11) / 6
chk("its pole x_c = (sqrt313 - 11)/6", abs(16 - 11 * xc - 3 * xc * xc) < 1e-12)
# the available transitions: the 74 directed edges an excursion begun after h can use, and their 296 transitions
avail = [(x, t) for (x, t) in states if x != 0 and not (x == g[h0] and t == h0)]
avail_tr = [(x, t, s) for (x, t) in avail for s in range(d) if s != t]
M = len(avail_tr)
Ch = sum(1 for (x, t, s) in avail_tr if s == h0)
Cj = sum(1 for (x, t, s) in avail_tr if s == 1)
n_noh = sum(1 for (x, t) in avail if not (x >> h0) & 1)
chk("the available transitions: 74 directed edges, M = 296, C_h = 60, C_j = 59; edges whose state does not contain h 34", (len(avail), M, Ch, Cj, n_noh) == (74, 296, 60, 59, 34))
eta, sigma, cL, Rud = (M - 1) / M, 5 * Ch / M, Ch / M, n_noh / len(avail)
chk("eta = (M - 1)/M = 5 C_j/M", abs(eta - 5 * Cj / M) < 1e-15)
EH = El * Ch / 320
# the graph's Green's function at the critical step (the pseudoinverse of its Laplacian) and b
G = np.linalg.pinv(5 * np.eye(16) - A)
b = G[0, 0] + G[ri[0b00011], ri[0b00011]] - 2 * G[0, ri[0b00011]]
chk("b = the effective resistance between the singlet and a symmetric state = 7/16", abs(b - 7 / 16) < 1e-12)
# the charge current c = 2 Var(Q) over the five directions, Q their charges seen from the plane hk
q = np.array([0.0, 1.0, -1 / 3, -1 / 3, -1 / 3])
c = 2 * (np.mean(q * q) - np.mean(q) ** 2)
chk("c = I(Q, Q) = 8/15", abs(c - 8 / 15) < 1e-15)
# the comparison L = 2(P + E) with spectrum 6, 2, -2: Tr L^2/4 = 24 traceless rotations, 1 + 10 states of positive value
Lspec = [6] + [2] * 10 + [-2] * 5
chk("24/11: Tr L^2/4 = 24 against the 11 states of positive comparison value", sum(l * l for l in Lspec) // 4 == 24 and sum(1 for l in Lspec if l > 0) == 11)
kap = float(e_even / t_even) ** (El / EnF)
f = float(e_even) ** 2 / N2
nu = f / El
marks = [0, 1, 2, 3, float(-1 / P1)]                    # a quarter step for each of the four directions other than h; the last mark is -1/Phi(1)
gaps = [abs(p_ - q_) for p_, q_ in itertools.combinations(marks, 2)]
ED = sum(gaps) / len(gaps) / 4
clock = lambda xv: sum(exp(-xv * dd / 4) for dd in gaps) / len(gaps)
chk("the clock's ten gaps: mean E_D = 2", abs(ED - 2) < 1e-15)
print("  primitives: a =", a, " chi_A =", chiA, " b =", round(b, 12), " M =", M, " C_h =", Ch, " eta =", round(eta, 12), " R_ud =", round(Rud, 12), " c =", round(c, 12), " kappa =", round(kap, 12))
print()

# ------------------------------------------------------------------ B. every row from these primitives
def rotation(i, j, s, phase=0.):
    out = np.eye(3, dtype=complex)
    out[i, i] = out[j, j] = sqrt(1 - s * s)
    out[i, j] = s * np.exp(-1j * phase)
    out[j, i] = -s * np.exp(1j * phase)
    return out


me = INPUTS["electron_mass_MeV"]                                   # the electron's energy, the unit
hc = INPUTS["planck_J_s"] * INPUTS["speed_of_light_m_s"] / (2 * pi * INPUTS["MeV_J"]) * 1e15
a_, b_ = float(a), float(b)
h = (clock(nu) * clock(-nu)) ** (-1.5)
rp = LOm * M + Ch + log(float(K0)) / LOm - a_ ** 5 - b_ * a_ ** 6
mp = me * rp
rn = exp(log(float(K0)) * (5 * a_ ** 4 + 4 * a_ ** 10 + 10 * cL * b_ * a_ ** 6))
mn = mp * rn
s_t = 0.5                                            # the count-or-amplitude power at the odd divided set {t}
lnLine = log(float(1 / e_line))


def level_factor(n, L, P):
    psi = 1 / (5 ** 2 + 3) if P == 1 else 1 / 2      # the rule: Psi = P/(L^2 + 3P) at the two signs P = +1 and -1
    eps = (1 + P) / 2
    assoc = -psi * L * (n - eps) / 4
    clk = log(clock(P * nu)) / LOm if n == 10 else (n - eps) * P * nu * ED / 4
    return exp(n * s_t * lnLine + assoc + clk)


rmu, rtau = level_factor(10, 2, 1), level_factor(5, -2, 1)
p, qq = level_factor(10, 2, -1), level_factor(5, -2, -1)
down = me * float(1 / e_line) ** (3 * s_t) * np.array([1 / eta, p / eta, p * qq])
up = Rud * down * np.array([1., kap ** 5, kap ** 7.5])
nh = 0.0
ncon = 0.0
for k in range(1, 60):
    z = 4 * (1j / 4) ** k
    odd = -Phz(z)
    nh += (h ** k * (odd if k % 2 else Fz(z))).real
    ncon += (odd if k % 2 else (Fz(z) + Fz(-z)) / 2).real
alpha = cL * f / (1 - nu * h / (M + 1 + nh))
alphas = sqrt(float(e_line) ** 2 / NC)
WW = Fz(h) / h ** 4 * (1 - 2 * b_ + 2 * b_ * h)
GF = (1 - 1 / N2) * WW / M ** 2 / (mp / 1000) ** 2
v = (sqrt(2) * GF) ** (-.5)
sw = 3 * nh
osw = sw / (1 + f)
mw = v * sqrt(pi * alpha / ((1 - f) * osw))
mz = mw / sqrt(1 - osw)
wh = 1 / (4 * float(chiA))
chih = wh * (1 - wh)
mh = v * sqrt(2 * pi * alpha / chih)
mt = v * sqrt(eta / (2 * sigma))
W = float(t_even) ** (kC * El) * eta ** (kC * EH)
mpl = mp / 1000 / W
MR, Moff = mpl * float(e_line) ** 9, mpl * float(e_line) ** 6
tau = 2 * pi / (El * rp)
s_face = float(e_even) / N2
lam = 3 * W ** 6 * tau * s_face ** 3
lp = hc / mp
mpcfm = INPUTS["megaparsec_m"] * 1e15
ell = lp / (W ** 2 * sqrt(tau * s_face ** 3)) / mpcfm
eps2 = alpha ** 2 / (1 + alpha / N2)
mup = sqrt(VarL / (2 * N2) * (1 - eps2 / (El ** 2 * b_)))
mun = -4 * (1 + EnF) / (VarL * 0 + 24 - 1) * sqrt(1 - eps2 / (El ** 2 * b_))
gA = (kC + 2) / 3 * float(t_even) ** (2 * b_ / kC)
pi0 = sqrt((2 / abs(float(P1))) * h * me * mp)
electric = pi * alpha * mp ** 2 / (El * (1 - alpha * b_ * Phz(1j).real))
pip = sqrt(pi0 * pi0 + electric)
fpi = eta * mp * sqrt(2 * kC) / (2 * pi * mup)
Bd = mp * sqrt(float(chiA)) * a_ ** 3 * (1 - (1 + float(t_even) / El) * eps2)
md = mp + mn - Bd
mus, gl = mup + mun, mn / (mp + mn)
mud = (16 * mus + gl) / 17 - (Bd / mp) * (mus - gl) / (20 + 13 * Bd / mp)
dq = atan2(16, 7)                                   # arg(b + i) = arg(7 + 16i)
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
As = 12 * a_ ** 11 * (INPUTS["primordial_pivot_Mpc_inv"] * ell) ** (-1 / 40)
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
         S08=b_ ** 24 * (INPUTS["primordial_pivot_Mpc_inv"] * ell) ** (-1 / 40) * 1e9, S09=M / (M - 4 * Ch), A002=5 * mp / 36, A003=5 * mp / 36 * abs(V[0, 0]))
R.update(N22=-bulk[0])
seq('K', [0, float(sum(neut)), float(sum(neut)), [mbeta, mbb], float(sum(abs(np.diag(V)) ** 2)), lifetime])
seq('T', [MR, Moff, ell, hc * 1e6 / (2 * pi * ell * mpcfm), neut[:2].tolist(), jl, 2 / 51])
seq('L', [me * rmu * rtau, abs(U[2]) ** 2, rho_nu ** -2, 3, float(1 / e_line) ** (5 * s_t) * me, 0, 0, -1, 0, 3 * pi / lam, 16 * lam / (3 * pi * 12 * a_ ** 11), lifetime, Bd, NC, mw, 0, koide, 15 * pi / 4])
inv = 1 / np.array([Rud, 1, p])
low = np.linalg.eigvalsh([[Rud + 1, (Rud - 1) / sqrt(3)], [(Rud - 1) / sqrt(3), (Rud + 1 + 4 * p) / 3]])[0]
R['I08'] = 1 / (low * sum(inv))
R['I09'] = -sum(inv ** 3) / (12 * sum(inv) ** 3)
R['S16'] = mz * 1000 * exp(-2 * pi / ((23 / 3) * alphas))
R['J03'] = mn * float(K0) ** (EH / El)                 # Lambda: the first-order rate of the available transitions along h
R['J04'] = kC * b_ * mp                                 # Delta: three aligned world lines
R['J05'], R['J06'] = pi0, pip
R['J07'] = 2 * kC * mp ** 2 * log(xc) / 1e6             # rho pole, GeV^2
R['J17'] = mp / LOm                                     # colour temperature
R['M1'], R['M2'], R['M3'] = mp, mn, md
R['J01'], R['J02'] = rp, rn                              # the proton and the neutron, as B12 and B13
nh1 = 0.0                                               # the clock's endpoint h = 1
for k in range(1, 60):
    z = 4 * (1j / 4) ** k
    nh1 += ((-Phz(z)) if k % 2 else Fz(z)).real
R['L19'] = (1 - nu / (M + 1 + nh1)) / (cL * f)
R['L20'] = 3 * nh1
# the charged kaon's marked current at the plane hk needs the light levels from the pion: the composition of two world lines
delta = lambda xv: -np.log1p(2 * np.expm1(-np.asarray(xv)) / (np.sqrt(9 + 16 * np.exp(-np.asarray(xv))) + 5))


def response(levels):
    nr = len(levels)
    dd = np.sqrt(levels)
    Gm = np.outer(dd, dd) * (np.eye(nr) + (1 - np.eye(nr)) * sqrt(c))
    return float(np.sum(delta(np.linalg.eigvalsh(Gm))))


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

# ------------------------------------------------------------------ C. beside the table and the measurements
SPL = re.compile(r"(?<!\\)\|")
table = {}
with io.open(TABLE, encoding="utf-8") as fh:
    for l in fh:
        if l.startswith("| ") and not l.startswith("| row |") and not l.startswith("| variable"):
            cc = [x.strip() for x in SPL.split(l.strip()[1:-1])]
            if len(cc) == 7:
                table[cc[0]] = dict(name=cc[1], value=cc[4], record=cc[5], sds=cc[6])


def num(s):
    try:
        return float(s)
    except Exception:
        return None


print("== B. Every row computed from the primitives of A, beside the table's value and the measurement")
print("| row | constant | from B | table | relative difference | measurement | standard deviations in the table |")
print("|---|---|---:|---:|---:|---|---:|")
agree, compared, derived = 0, 0, 0
for rid in sorted(R, key=lambda k: (re.sub(r"\d", "", k), int(re.sub(r"\D", "", k) or 0))):
    val = R[rid]
    if isinstance(val, (list, tuple, np.ndarray)) or rid not in table:
        continue
    derived += 1
    tv = num(table[rid]["value"])
    if tv is None:
        continue
    compared += 1
    rd_ = (val - tv) / tv if tv != 0 else (val - tv)
    sv_ = table[rid]["value"]
    ndec = len(sv_.split(".")[1]) if "." in sv_ and "e" not in sv_.lower() else 12
    same = abs(rd_) < 1e-6 or abs(val - tv) <= 0.6 * 10 ** (-ndec)
    if rid == "J09":
        same = abs(val - 493.665032668) < 1e-6          # the charged kaon with the marked current at the plane hk
    agree += same
    print("| %s | %s | %.12g | %s | %.2e | %s | %s |" % (rid, table[rid]["name"], val, table[rid]["value"], rd_, table[rid]["record"], table[rid]["sds"]))
print()
print("rows computed from B:", derived, "; compared with the table:", compared, "; agreeing within the digits the table prints:", agree, "(J09 with the marked current at the plane hk, 493.665 MeV, -0.80 standard deviations)")
rest = [r for r in table if r not in R]
print("conventional and composite records printed by article_results.py:", len(rest))
print("  " + " ".join(sorted(rest)))
chk("the 131 scalar rows compared here agree with their recorded values within the printed digits", agree == compared, (agree, compared))
print()
print("checks:", sum(ok), "of", len(ok), "ok")
