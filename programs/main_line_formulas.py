# -*- coding: utf-8 -*-
# THE MAIN LINE IN FORMULAS
#
# From the comparison L of two systems and the step B of a world line to every equation and every constant, in the order
# of the breaking. Each formula is computed here from B and L alone; together they give all 113 rows of the main line
# that the law computes, each agreeing with the table's value (data/constants_and_measurements.md) to a relative 1e-6 or
# within its printed digits. The program writes outputs/main_line_formulas.md and prints its checks.
# Run from the repository root:  python -I programs/main_line_formulas.py > outputs/main_line_formulas.out
# Prints its checks ("ok" or "FAIL"), the number of formulas and of rows.
import itertools, io, os, re
from fractions import Fraction as Fr
from math import sqrt, log, exp, pi, atan2, comb, tan, factorial
import numpy as np
import json

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
with open(os.path.join(ROOT, "data", "inputs.json"), encoding="utf-8") as fh:
    INPUTS = {key: entry["value"] for key, entry in json.load(fh).items()}
TABLE = os.path.join(ROOT, "data", "constants_and_measurements.md")
OUTMD = os.path.join(ROOT, "outputs", "main_line_formulas.md")
ok = []
MD = []
ROWS = {}
NUM = [0]


def chk(name, cond, val=""):
    ok.append(bool(cond))
    print(("ok   " if cond else "FAIL ") + name + ("" if val == "" else "   [" + str(val) + "]"))


def sec(title, text=""):
    MD.append("")
    MD.append("## " + title)
    MD.append("")
    if text:
        MD.append(text)
        MD.append("")


TAG = {}


def eq(formula, meaning, rows=(), key=None):
    NUM[0] += 1
    tag = "(%d)" % NUM[0]
    for r_ in rows:
        TAG.setdefault(r_, tag)
    if key:
        TAG[key] = tag
    MD.append("**%s**  %s" % (tag, formula))
    MD.append("")
    line = meaning
    if rows:
        line += "  Rows: " + ", ".join(rows) + "."
    MD.append(line)
    MD.append("")
    return tag


SUP = str.maketrans("-0123456789", "⁻⁰¹²³⁴⁵⁶⁷⁸⁹")


def sci(x, nd):
    m_, e_ = ("%.*e" % (nd, x)).split("e")
    return "%s × 10%s" % (m_.replace("-", "−"), str(int(e_)).translate(SUP))


def mn_(s_):
    return s_.replace("-", "−")


def row(rid, value):
    ROWS[rid] = value
    return value


# =====================================================================================================================
# 1. The comparison
s0 = np.eye(2)
sx = np.array([[0, 1], [1, 0]], dtype=complex)
sy = np.array([[0, -1j], [1j, 0]])
sz = np.array([[1, 0], [0, -1]], dtype=complex)
gam = [np.kron(sx, s0), np.kron(sy, s0), np.kron(sz, sx), np.kron(sz, sy), np.kron(sz, sz)]
I4, I16 = np.eye(4), np.eye(16)
d = 5
cliff = all(np.allclose(gam[i] @ gam[j] + gam[j] @ gam[i], 2 * (i == j) * I4) for i in range(d) for j in range(d))
five = np.allclose(gam[0] @ gam[1] @ gam[2] @ gam[3] @ gam[4], I4) or np.allclose(gam[0] @ gam[1] @ gam[2] @ gam[3] @ gam[4], -I4)
L = I16.astype(complex) + sum(np.kron(x, x) for x in gam)
Psw = np.zeros((16, 16))
for i in range(4):
    for j in range(4):
        Psw[i * 4 + j, j * 4 + i] = 1
Ep = L / 2 - Psw
wE, VE = np.linalg.eigh(Ep)
Om = VE[:, np.argmax(wE)]
specL = sorted(np.round(np.linalg.eigvalsh(L), 9))
LOm = float((Om.conj() @ L @ Om).real)
chk("(1)-(3) the five Dirac matrices on four amplitudes; L = 2(P + E) with spectrum 6, 2^10, (-2)^5; L(Omega) = 6",
    cliff and five and specL == [-2.0] * 5 + [2.0] * 10 + [6.0] and abs(LOm - 6) < 1e-12 and np.allclose(L, 2 * (Psw + Ep)))
kept = [kk * (kk - 1) // 2 + (6 - kk) * (5 - kk) // 2 for kk in range(4)]
moved = [kk * (6 - kk) for kk in range(4)]
Hk = (I4 + 1j * gam[1]) / sqrt(2)
T1, T2, T3 = 1j * gam[0], gam[0] @ gam[1], 1j * gam[1]
clocks = (np.allclose(Hk @ T1 @ Hk.conj().T, T2) and all(np.allclose(T @ T, -I4) for T in (T1, T2, T3))
          and np.allclose(T1 @ T2, T3) and np.allclose(T2 @ T3, T1) and np.allclose(T3 @ T1, T2))
chk("(4)-(5) rotations within the sides 15, 10, 7, 6, mixing them 0, 5, 8, 9; the world line's own clock and the common clock one quaternion triple",
    kept == [15, 10, 7, 6] and moved == [0, 5, 8, 9] and clocks)
ALL = (1 << d) - 1
rel = [m for m in range(1 << d) if bin(m).count("1") % 2 == 0]
ri = {m: i for i, m in enumerate(rel)}
pc = lambda S: bin(S).count("1")
F_face, C_out = 0b00011, 0b11100
qch = [Fr(0), Fr(1), Fr(-1, 3), Fr(-1, 3), Fr(-1, 3)]
Y = [Fr(pc(S & F_face), 2) - Fr(pc(S & C_out), 3) for S in rel]
chk("(6) one generation: Sum Y = Sum Y^3 = 0 over the sixteen; the five directions carry (0, 1, -1/3, -1/3, -1/3)",
    sum(Y) == 0 and sum(y ** 3 for y in Y) == 0 and sum(qch) == 0)
Eu = lambda i, j: np.outer(np.eye(5)[i], np.eye(5)[j]).astype(complex)
gb = []
for blk in ([0, 1], [2, 3, 4]):
    for i in blk:
        for j in blk:
            if i < j:
                gb.append(1j * (Eu(i, j) + Eu(j, i)) / sqrt(2))
                gb.append((Eu(i, j) - Eu(j, i)) / sqrt(2))
for blk in ([0, 1], [2, 3, 4]):
    for m_ in range(1, len(blk)):
        vv = np.zeros(5)
        vv[blk[:m_]] = 1
        vv[blk[m_]] = -m_
        gb.append(1j * np.diag(vv / np.linalg.norm(vv)))
gb.append(1j * np.diag(np.array([3, 3, -2, -2, -2]) / sqrt(30)))
phi = np.eye(5)[0]
Gm = np.array([[np.real(np.vdot(X @ phi, Yb @ phi)) for Yb in gb] for X in gb])
gev = sorted(np.round(np.linalg.eigvalsh(Gm), 12))
chk("(7) the Gram of h on the twelve rotations that keep 2 + 3: 1/2, 1/2, 4/5 and nine zeros; M_W^2/M_Z^2 = 5/8 at the source",
    np.allclose([x for x in gev if abs(x) > 1e-12], [0.5, 0.5, 0.8]) and sum(abs(x) < 1e-12 for x in gev) == 9)
gmat = np.diag([-1, -1, 1, 1, 1, 1.0])
p0 = np.concatenate([np.array([1.0, 0.0]), np.array([1.0, 0, 0, 0])])
Tb = np.array([x for x in np.eye(6) if abs(x @ gmat @ p0) < 1e-12])
sig = np.linalg.eigvalsh(Tb @ gmat @ Tb.T)
chk("(8) the null cone of the distinction of the plane hk has signature (1, 3), negative directions first", (sum(sig < -1e-9), sum(sig > 1e-9)) == (1, 3))

sec("1. The comparison", "Two distinctions compared. No physical name is given in this section.")
eq("γ_aγ_b + γ_bγ_a = 2δ_ab on ℂ⁴,  γ₁γ₂γ₃γ₄γ₅ = ±1", "Four amplitudes and five Dirac matrices.")
eq("L = I⊗I + Σ_t γ_t⊗γ_t = 2(P + E),  spec L = 6¹ ⊕ 2¹⁰ ⊕ (−2)⁵",
   "The comparison: P the exchange, E the singlet channel pairing each amplitude with its conjugate; one comparison tells the singlet (6), one of the ten symmetric states (2) or one of the five vector states (−2).")
eq("L(Ω) = ⟨Ω, LΩ⟩ = 6", "Ω pairs every amplitude with its conjugate: the singlet.")
eq("within C(d, 2) + C(6 − d, 2) = 15, 10, 7, 6;  mixing d(6 − d) = 0, 5, 8, 9;  a central rotation within the sides only at 2¦4",
   "The four types of distinction of the six directions; the rotations each keeps within its two sides and the rotations mixing them.")
eq("T₁ = iγ_h,  T₂ = γ_hγ_k,  T₃ = iγ_k:  H_kT₁H_k† = T₂,  H_k = (1 + iγ_k)/√2,  T_a² = −1,  T₁T₂ = T₃",
   "The central rotation of the plane {n, h} and that of the plane hk, one quaternion triple with the change between them.")
eq("Y = |S ∩ F|/2 − |S ∩ C|/3,  Q = N_k − N_C/3:  ΣY = ΣY³ = 0",
   "The sixteen two-spinor states seen from the plane hk (F = {h, k}): one generation; the five directions carry the charges (0, 1, −1/3, −1/3, −1/3).")
eq("Gram of the twelve rotations keeping 2 + 3, moved by h: (1/2, 1/2, 4/5) and nine zeros",
   "Three moved, nine kept; M_W²/M_Z² = 5/8 and sin²θ = 3/8 at the source.")
eq("the null directions of the distinction of the plane hk: signature (1, 3), negative directions first", "One time and three space.")

# =====================================================================================================================
# 2. The law
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
chi = lambda u: 1 / u + 4 * u - 5
kN = lambda N, u: u * (2 * N + chi(u))
Hp = np.array([np.kron(_g, I4) @ Om for _g in
               [np.linalg.multi_dot([I4] + [gam[a_] for a_ in range(d) if (S >> a_) & 1] + [I4]) for S in rel]]).T
Wc = np.array([[0.25 * (-1) ** pc(x & S) for S in rel] for x in rel])
TL = Hp @ Wc.T
okk = all(abs(np.linalg.det(np.eye(80) - u * B) - (1 - u * u) ** 24 * u ** 16 * np.linalg.det(6 * I16 - L + chi(u) * I16))
          < 1e-9 * max(1, abs(np.linalg.det(np.eye(80) - u * B))) for u in (0.11, 0.2 + 0.07j, -0.3j, 0.25 - 0.1j))
chk("(9)-(11) B has 80 directed edges and 320 transitions; T^dagger(6I - L)T = 5I - A; det(I - uB) = (1 - u^2)^24 u^16 det[(6I - L) + chi I]; "
    "k_N = u(2N + chi)",
    B.shape == (80, 80) and B.sum() == 320 and np.allclose(TL.conj().T @ TL, I16) and np.allclose(TL.conj().T @ (6 * I16 - L) @ TL, 5 * I16 - A)
    and okk and all(abs(kN(N, u) - (1 + 4 * u * u - u * (5 - 2 * N))) < 1e-12 for N in (0, 2, 4) for u in (0.13, 0.2 + 0.1j)))
uF = Fr(-1, 4)
K = {N: 1 + 4 * uF * uF - uF * (5 - 2 * N) for N in (0, 2, 4)}
t_, e_, tl_, el_ = 1 / K[0], K[2] / K[0], 1 / K[2], K[4] / K[2]
chk("(12)-(13) the spectral parameter at the four points 0, -5 - 3i, -10, -5 + 3i; at u = -1/4 5/2, 3/2, 1/2; t, e, t_l, e_l = 2/5, 3/5, 2/3, 1/3",
    np.allclose([chi(u) for u in (0.25, 0.25j, -0.25, -0.25j)], [0, -5 - 3j, -10, -5 + 3j])
    and (K[0], K[2], K[4], t_, e_, tl_, el_) == (Fr(5, 2), Fr(3, 2), Fr(1, 2), Fr(2, 5), Fr(3, 5), Fr(2, 3), Fr(1, 3)))

sec("2. One world line persists: the law", "A world line's state is a two-spinor state and its last change; each step keeps the last change and never undoes it at once.")
eq("B:  (x, t) → (x △ g_s, s),  s ≠ t,  g_s the four Dirac matrices other than s", "The step: 80 directed edges, 320 transitions.")
eq("det(I − uB) = (1 − u²)²⁴ u¹⁶ det[(6I − L) + χ(u)I],  χ(u) = 1/u + 4u − 5 = (1 − u)(1 − 4u)/u",
   "The law is the comparison with one movable spectral parameter χ: T = HWᵀ, with the paired vectors (γ_S ⊗ 1)Ω and the characters W_xS = (1/4)(−1)^|x∩S|, "
   "is unitary and T†(6I − L)T = 5I − A.")
eq("k_N(u) = u(2N + χ(u)) = 1 + 4u² − u(5 − 2N):  det(I − uB) = (1 − u²)²⁴ k₀ k₂¹⁰ k₄⁵", "The grade factors: the spectral parameter read through 6 − L = 0, 4, 8.")
eq("u = i^d/4:  χ = 0, −5 − 3i, −10, −5 + 3i", "The breaking puts the spectral parameter at the singlet (the one zero), the direction h, the plane hk and colour.")
eq("k_N(−1/4) = (5 − N)/2 = 5/2, 3/2, 1/2:  t = 1/k₀ = 2/5,  e = k₂/k₀ = 3/5,  t_ℓ = 1/k₂ = 2/3,  e_ℓ = k₄/k₂ = 1/3",
   "The transmission and the reflection, at the symmetric states and at a single direction: values of the one kernel at χ = −10.")

# =====================================================================================================================
# 3. The equations
m2c = [chi(0.25 - mm * mm / 24) / (mm * mm / 2) for mm in (0.2, 0.1, 0.05)]
okd = all(np.allclose((np.cos(k1) * I4 - 1j * np.sin(k1) * gam[1]) @ (np.cos(m1) * I4 - 1j * np.sin(m1) * gam[0])
                      + ((np.cos(k1) * I4 - 1j * np.sin(k1) * gam[1]) @ (np.cos(m1) * I4 - 1j * np.sin(m1) * gam[0])).conj().T,
                      2 * np.cos(k1) * np.cos(m1) * I4) for (m1, k1) in [(0.3, 0.5), (1.1, -0.7), (2.0, 1.3)])
chk("(14)-(15) the spectral parameter is half the mass squared near the zero; U + U^dagger = 2 cos k cos mu", abs(m2c[-1] - 1) < 1e-3 and okd,
    ", ".join("%.6f" % x for x in m2c))


def blade(a_, b_):
    s = 0
    aa = a_ >> 1
    while aa:
        s += pc(aa & b_)
        aa >>= 1
    return (-1) ** s, a_ ^ b_


Am = np.zeros((16, 16))
for x in rel:
    for s in range(d):
        s1, y = blade(1 << s, x)
        s2, z = blade(ALL, y)
        Am[ri[z], ri[x]] += s1 * s2
cells = {}
for k_ in range(3):
    found = set()
    for x in rel:
        for S in itertools.combinations(range(d), k_):
            vs = {x}
            for s in S:
                vs |= {v ^ g[s] for v in vs}
            found.add((frozenset(vs), frozenset(S)))
    cells[k_] = sorted(found, key=lambda c: (sorted(c[1]), sorted(c[0])))
lid = {}
for j, (vs, S) in enumerate(cells[1]):
    a_, b_ = sorted(vs)
    lid[(a_, b_)] = j
Cm = np.zeros((40, 40))
for i, (vs, S) in enumerate(cells[2]):
    x = min(vs)
    s, t = sorted(S)
    cyc = [x, x ^ g[s], x ^ g[s] ^ g[t], x ^ g[t]]
    for k_ in range(4):
        a_, b_ = cyc[k_], cyc[(k_ + 1) % 4]
        Cm[i, lid[(min(a_, b_), max(a_, b_))]] += 1 if a_ < b_ else -1


def logdet_signed(w, th):
    At = Am.astype(complex).copy()
    for (a_, b_), j in lid.items():
        At[ri[b_], ri[a_]] = Am[ri[b_], ri[a_]] * np.exp(1j * th[j])
        At[ri[a_], ri[b_]] = Am[ri[a_], ri[b_]] * np.exp(-1j * th[j])
    return np.log(np.linalg.det(np.eye(16) - w * At))


rng = np.random.default_rng(11)
th0 = 0.003 * rng.normal(size=40)
kap = lambda c_: 2 / ((c_ + 5) ** 2 - 5) ** 2
kres = [((logdet_signed(1 / (c_ + 5), th0) - logdet_signed(1 / (c_ + 5), np.zeros(40))) / (-0.5 * th0 @ Cm.T @ Cm @ th0)).real for c_ in (0.0, -10.0)]
kres.append(((logdet_signed(1j / 3, th0) - logdet_signed(1j / 3, np.zeros(40))) / (-0.5 * th0 @ Cm.T @ Cm @ th0)).real)
chk("(17) kappa(chi) = 2/[(chi + 5)^2 - 5]^2: 1/200 at the singlet and the plane hk, 1/98 at h and colour",
    abs(kres[0] - 1 / 200) < 2e-7 and abs(kres[1] - 1 / 200) < 2e-7 and abs(kres[2] - 1 / 98) < 4e-7 and abs(kap(0) - 1 / 200) < 1e-15,
    ", ".join("%.8f" % x for x in kres))
Gr = np.zeros((40, 16))
for (a_, b_), j in lid.items():
    Gr[j, ri[b_]] += 1
    Gr[j, ri[a_]] -= 1
thc = rng.normal(size=40)
thc -= Gr @ np.linalg.lstsq(Gr, thc, rcond=None)[0]
thc *= 0.003
At = np.zeros((16, 16), dtype=complex)
for (x1, x2), j in lid.items():
    At[ri[x2], ri[x1]] += np.exp(1j * thc[j])
    At[ri[x1], ri[x2]] += np.exp(-1j * thc[j])
lmax = np.linalg.eigvalsh(At).max()
uc = (lmax - sqrt(lmax * lmax - 16)) / 8
chk("(18) a circulation moves the leading zero by |theta_cyc|^2/48, 48 = 3 E l = 2(40 - 16)", abs((thc @ thc) / log(4 * uc) - 48) < 1e-3,
    "%.5f" % ((thc @ thc) / log(4 * uc)))
e4 = np.zeros((4,) * 4)
for perm in itertools.permutations(range(4)):
    e4[perm] = np.linalg.det(np.eye(4)[list(perm)])
EE = np.einsum("ac,bd->abcd", np.eye(4), np.eye(4)) - np.einsum("ad,bc->abcd", np.eye(4), np.eye(4))
wedge = lambda X, Yt: 0.25 * np.einsum("abcd,abef,cdgh,efgh->", e4, X, Yt, e4)
Rr = rng.normal(size=(4, 4, 4, 4))
Rr = Rr - Rr.transpose(1, 0, 2, 3)
Rr = Rr - Rr.transpose(0, 1, 3, 2)
Rr = Rr + Rr.transpose(2, 3, 0, 1)
ell = 1.7
lam_l2 = ((wedge(Rr - EE / ell ** 2, Rr - EE / ell ** 2) - wedge(Rr, Rr)) / (4 / ell ** 2) + np.einsum("abab->", Rr)) / 2 * ell ** 2
chk("(19) the curvature of the ten rotations contracted with h: Lambda l^2 = 3 at any curvature", abs(lam_l2 - 3) < 1e-9, "%.12f" % lam_l2)

sec("3. The equations", "Near the one zero, many steps summed: the law at each breaking is a classical field equation.")
eq("u = 1/4 − ε²m²/24:  χ = ε²m²/2 + O(ε⁴),  (1 + 4u²) − uA_ε = (ε²/8)(m² − Δ) + O(ε³)",
   "Klein–Gordon in the long-wave limit: χ = ε²m²/2 + O(ε⁴); on the resolved two-sheet chart exactly ε²M_ε² = 2χ + χ²/5, so M_ε → m; the rest frequency tends to the mass, E = mc².", key="KG")
eq("U = e^(−ikγ_j) e^(−iμγ_h):  U + U† = 2 cos k cos μ,  cos ω = cos μ cos k", "Dirac's first-order step; c one step per step, ħ energy over phase per step.",
   key="Dirac")
eq("G(k) = 1/[V₃(M² + L₃(k)/5)],  V₃ = 1/2;  the long-wave continuum response G_cont(r) = e^(−Mr)/(4πr)",
   "Two sources held at rest on the law's own chart: 1/(4πr) at the zero, its coefficient 0.99304 to 0.99989 in four directions; Yukawa below it "
   "(programs/classical_experiments.py, F4).")
eq("log det(I − wA₋[e^(iθ)]) = log det(I − wA₋) − ½κ‖Cθ‖² + O(θ⁴),  w = 1/(χ + 5),  κ(χ) = 2/[(χ + 5)² − 5]²",
   "Maxwell and Yang–Mills: the squared curvature around the square cells, unchanged by a gauge transformation; κ = 1/200 at the singlet and the plane hk, 1/98 at h and colour.")
eq("log 4u_c = ‖θ_cyc‖²/48 + O(θ⁴),  48 = 3Eℓ = 2(40 − 16)", "A circulation carried around the cells moves the leading zero.")
eq("ε_abcd(𝓕^ab∧𝓕^cd − R^ab∧R^cd) = −(4/ℓ²)(R − 6/ℓ²) vol,  𝓕 = R − e∧e/ℓ²:  Λℓ² = 3", "Einstein–Cartan with the constant term, in the epsilon contraction.", key="EC")
eq("K_X(E, N) = K_X(E/N, 1)  ⟹  K_N = −(E/N) K_E,  dE_X/dN = E_X(N)/N (N > 0);  at N = 1 these are −E K_E and E_X(1)",
   "A lapse on the clock that measures energy couples to the rest energy: the gravitational charge is the mass, the same share for every world line.")

# =====================================================================================================================
# 4. One first-return excursion
Fz = lambda z: z ** 4 * (1 + z) / (16 - 8 * z - 3 * z ** 2 - 3 * z ** 3)
Phz = lambda z: -z ** 4 / (16 + 3 * z ** 2)
idx = {}
for S in range(1 << d):
    for t in range(d):
        for p_ in (0, 1):
            idx[(S, t, p_)] = len(idx)
is_singlet = lambda S, p_: (p_ == 0 and S == 0) or (p_ == 1 and S == ALL)


def first_return(z, signed):
    Q = np.zeros((len(idx), len(idx)), dtype=complex)
    r = np.zeros(len(idx), dtype=complex)
    for (S, t, p_), i in idx.items():
        if is_singlet(S, p_):
            continue
        for s in range(d):
            if s == t:
                continue
            sg = (-1) ** pc(S >> (s + 1)) if signed else 1
            S2, p2 = S ^ (1 << s), 1 - p_
            if is_singlet(S2, p2):
                r[i] += (0.25 * sg if S2 == 0 else 0.0) if signed else 0.25
            else:
                Q[idx[(S2, s, p2)], i] += 0.25 * sg
    psi = z * np.linalg.solve(np.eye(len(idx)) - z * Q.T, r)
    return z * sum(0.25 * psi[idx[(1 << s, s, 1)]] for s in range(d) if s != 0)


okF = all(abs(first_return(z, False) - Fz(z)) < 1e-12 and abs(first_return(z, True) - Phz(z)) < 1e-12 for z in (0.4, 0.6 + 0.3j, 0.8j))
P1 = Fr(-1, 19) if abs(first_return(1.0, True) + 1 / 19) < 1e-12 else None
Pi = Fr(-1, 13) if abs(first_return(1j, True) + 1 / 13) < 1e-12 else None
hh = 1e-5
El = (Fz(1 + hh) - Fz(1 - hh)) / (2 * hh)
F2 = (Fz(1 + hh) - 2 * Fz(1) + Fz(1 - hh)) / hh ** 2
Varl = F2 + El - El ** 2
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
is_sym = np.array([1.0 if pc(x) == 2 else 0.0 for (x, t) in trans])
is_vec = np.array([1.0 if pc(x) == 4 else 0.0 for (x, t) in trans])
second = lambda Ai, Bi: float(mu_ @ (np.diag(Ai) @ Nm @ Bi) + mu_ @ (np.diag(Bi) @ Nm @ Ai) - mu_ @ (Ai * Bi))
EnF, EnL = float(mu_ @ is_sym), float(mu_ @ is_vec)
VarnF, VarnL, Cov = second(is_sym, is_sym) - EnF ** 2, second(is_vec, is_vec) - EnL ** 2, second(is_sym, is_vec) - EnF * EnL
h0 = 0
avail = [(x, t) for (x, t) in states if x != 0 and not (x == g[h0] and t == h0)]
avail_tr = [(x, t, s) for (x, t) in avail for s in range(d) if s != t]
M, Ch, Cj = len(avail_tr), sum(1 for c_ in avail_tr if c_[2] == h0), sum(1 for c_ in avail_tr if c_[2] == 1)
n_noh = sum(1 for (x, t) in avail if not (x >> h0) & 1)
Gg = np.linalg.pinv(5 * I16 - A)
bG = Gg[0, 0] + Gg[ri[0b00011], ri[0b00011]] - 2 * Gg[0, ri[0b00011]]
xc = (sqrt(313) - 11) / 6
chk("(21)-(25) F and Phi counted on B; E l = 16, Var l = 156; E n_F = 10, E n_L = 5, Var n_F = 84, Var n_L = 12, Cov = 30; the available transitions 74, 296, 60, 59, 34; "
    "b = 7/16", okF and P1 == Fr(-1, 19) and Pi == Fr(-1, 13) and abs(El - 16) < 1e-6 and abs(Varl - 156) < 1e-3
    and max(abs(EnF - 10), abs(EnL - 5), abs(VarnF - 84), abs(VarnL - 12), abs(Cov - 30)) < 1e-9
    and (len(avail), M, Ch, Cj, n_noh) == (74, 296, 60, 59, 34) and abs(bG - 7 / 16) < 1e-12 and abs(16 - 11 * xc - 3 * xc * xc) < 1e-12)
El, Varl, EnF, EnL, VarnF, VarnL, Cov = 16, 156, 10, 5, 84, 12, 30
# the same first return with its visits marked: x at each arrival at one of the five vector states (n_L), y at each arrival
# at one of the ten symmetric states (n_F); the state of (S, t, p) is S, or its complement when p = 1
grade = lambda S, p_: pc(S) if p_ == 0 else d - pc(S)


def first_return_marked(z, x, y):
    wt = lambda S, p_: x if grade(S, p_) == 4 else (y if grade(S, p_) == 2 else 1)
    Q = np.zeros((len(idx), len(idx)), dtype=complex)
    r = np.zeros(len(idx), dtype=complex)
    for (S, t, p_), i in idx.items():
        if is_singlet(S, p_):
            continue
        for s in range(d):
            if s == t:
                continue
            S2, p2 = S ^ (1 << s), 1 - p_
            if is_singlet(S2, p2):
                r[i] += 0.25
            else:
                Q[idx[(S2, s, p2)], i] += 0.25 * wt(S2, p2)
    psi = z * np.linalg.solve(np.eye(len(idx)) - z * Q.T, r)
    return z * sum(0.25 * wt(1 << s, 1) * psi[idx[(1 << s, s, 1)]] for s in range(d) if s != 0)


Fret = lambda z, x, y: z ** 4 * x ** 2 * y * (1 + z * y) / (16 - 8 * z * y - 3 * z ** 2 * x * y - 3 * z ** 3 * x * y ** 2)
okFret = all(abs(first_return_marked(z, x, y) - Fret(z, x, y)) < 1e-12 for (z, x, y) in [(0.4, 0.7, 1.1), (0.6 + 0.3j, 0.9, 0.5 - 0.2j), (0.8j, 1.2, 0.3)])
okFx = (all(abs(first_return_marked(1.0, x, 1.0) - x * x / (4 - 3 * x)) < 1e-12 for x in (0.2, 0.5, 0.9, 1.1))
        and all(Fret(Fr(1), xq, Fr(1)) == xq * xq / (4 - 3 * xq) for xq in (Fr(1, 3), Fr(2, 7), Fr(5, 4))))
# the law of n_L counted on B: the series of F(1; x, 1) in x, Pr(n_L = k) = (1/4) sum over the four first steps of the coefficient of x^(k-1)
QF, QL, r1 = np.zeros((len(idx), len(idx))), np.zeros((len(idx), len(idx))), np.zeros(len(idx))
for (S, t, p_), i in idx.items():
    if is_singlet(S, p_):
        continue
    for s in range(d):
        if s == t:
            continue
        S2, p2 = S ^ (1 << s), 1 - p_
        if is_singlet(S2, p2):
            r1[i] += 0.25
        elif grade(S2, p2) == 4:
            QL[idx[(S2, s, p2)], i] += 0.25
        else:
            QF[idx[(S2, s, p2)], i] += 0.25
MF = np.eye(len(idx)) - QF.T
ck = np.linalg.solve(MF, r1)
pnL = []
for k_ in range(1, 16):
    pnL.append(sum(0.25 * ck[idx[(1 << s, s, 1)]] for s in range(1, d)))
    ck = np.linalg.solve(MF, QL.T @ ck)
okK = abs(pnL[0]) < 1e-15 and all(abs(pnL[k_ - 1] - 0.25 * 0.75 ** (k_ - 2)) < 1e-14 for k_ in range(2, 16))
# K = n_L - 2 has G(x) = x^(-2) F(1; x, 1) = 1/(4 - 3x); its cumulants are j-derivatives of log G(e^j) = -log(1 - 3(e^j - 1)), as exact series
NJ = 5
ser_mul = lambda p_, q_: [sum(p_[i_] * q_[n_ - i_] for i_ in range(n_ + 1)) for n_ in range(NJ)]
u3 = [Fr(0)] + [Fr(3, factorial(m_)) for m_ in range(1, NJ)]
logG, pw = [Fr(0)] * NJ, [Fr(1)] + [Fr(0)] * (NJ - 1)
for m_ in range(1, NJ):
    pw = ser_mul(pw, u3)
    logG = [l_ + c_ / m_ for l_, c_ in zip(logG, pw)]
cumK = [logG[n_] * factorial(n_) for n_ in range(1, NJ)]
EK, VarK = cumK[0], cumK[1]
EKf, VarKf = float(EK), float(VarK)
chk("(23) the first return with its visits marked, counted on B: F(z; x, y) = z^4 x^2 y (1 + zy)/(16 - 8zy - 3z^2 xy - 3z^3 xy^2), x at each vector state, "
    "y at each symmetric state; F(1; x, 1) = x^2/(4 - 3x): two compulsory vector arrivals, and K = n_L - 2 has G(x) = 1/(4 - 3x), Pr(K = k) = (1/4)(3/4)^k; "
    "the cumulants of K from log G(e^j): E K = E n_L - 2 = 3, Var K = Var n_L = 12, then 84, 876",
    okFret and okFx and okK and cumK == [3, 12, 84, 876] and EK == EnL - 2 and VarK == VarnL, ", ".join(str(c_) for c_ in cumK))
cL, eta, sigma, Rud = Fr(Ch, M), Fr(5 * Cj, M), Fr(5 * Ch, M), Fr(n_noh, len(avail))
EH = Fr(El * Ch, 320)
b = Fr(7, 16)
a = (1 - P1) / 8
chiA = 1 / (1 + Pi)
wh = 1 / (4 * chiA)
chih = wh * (1 - wh)
chk("(26) a = 5/38, chi_A = 13/12, w_h = 3/13, chi_h = 30/169; c_L = 15/74, eta = 295/296, sigma = 75/74, R_ud = 17/37, E_H = 3",
    (a, chiA, wh, chih, cL, eta, sigma, Rud, EH) == (Fr(5, 38), Fr(13, 12), Fr(3, 13), Fr(30, 169), Fr(15, 74), Fr(295, 296), Fr(75, 74), Fr(17, 37), Fr(3)))
Snz = [S for S in rel if S != 0]
Hdir = lambda S, D: (5 * pc(S & D) - pc(D) * pc(S)) / 4


def response_ratio(D, E, c_):
    wv = np.array([1 / (c_ + 4) if pc(S) == 2 else 1 / (c_ + 8) for S in Snz])
    wv = wv / wv.sum()
    Nv = np.array([pc(S) for S in Snz], dtype=float)
    Xv = np.array([Hdir(S, D) * Hdir(S, E) for S in Snz])
    return (wv @ (Nv * Xv) - (wv @ Nv) * (wv @ Xv)) / (9 / 8 * (wv @ Nv ** 2 - (wv @ Nv) ** 2))


okc = all(abs(response_ratio(D_, E_, c_) - v_) < 1e-12 for c_ in (0.0, 2.0, 1e6)
          for (D_, E_, v_) in [(1, 2, 1 / 72), (1, 0b11110, 1 / 18), (0b00011, 0b11100, 1 / 12)])
g2 = Fr(1, 72)
chk("(27) the response of directions on opposite sides against its clock: 1/72, 1/18, 1/12 at regular chi; g^2 = 1/72 = -Phi(1)/[4(1 + Phi(1))] = -Phi(i)/[6(1 + Phi(i))] "
    "= e_l^2/8", okc and -P1 / (4 * (1 + P1)) == g2 and -Pi / (6 * (1 + Pi)) == g2 and el_ ** 2 / 8 == g2)
trans_weight = [float((Om.conj() @ (L + np.kron(gam[h0], gam[s])) @ Om).real) for s in range(d)]
Bc = B.astype(complex)
arc = [(si[(x ^ g[s], s)], si[(x, t)]) for (x, t) in avail for s in range(d) if s != t]
okarc = True
for (u, th) in [(0.2, 0.7), (0.24 + 0.01j, 2.0), (-0.1j, 0.3)]:
    Bt = Bc.copy()
    Bt[arc[3]] = np.exp(-1j * th)
    Mx = np.eye(80) - u * B
    D0 = np.linalg.det(Mx)
    dD0 = -D0 * np.trace(np.linalg.solve(Mx, B))
    okarc &= abs(np.linalg.det(np.eye(80) - u * Bt) - (D0 + (np.exp(-1j * th) - 1) * u * dD0 / 320)) < 1e-9 * abs(D0)
chk("(28)-(29) a transition weighs <Omega, (L + g_h x g_s) Omega> = 6 + [s = h]; one marked transition exactly: D_theta = D + (e^(-i theta) - 1) u D'/320",
    np.allclose(trans_weight, [7, 6, 6, 6, 6]) and okarc)

sec("4. One first-return excursion", "From leaving the singlet to coming back to it: the walk of one world line, counted on B.")
eq("F(z) = z⁴(1 + z)/(16 − 8z − 3z² − 3z³):  F(1) = 1,  Eℓ = F′(1) = 16,  Var ℓ = 156", "Every excursion closes, after sixteen steps on average: the mean return time.")
eq("Φ(z) = −z⁴/(16 + 3z²):  Φ(±1) = −1/19,  Φ(±i) = −1/13", "The same excursions with the Clifford sign of every loop.")
eq("E n_F = 10,  E n_L = 5,  Var n_F = 84,  Var n_L = 12,  Cov(n_F, n_L) = 30;  x(1 + x)/(16 − 11x − 3x²),  x_c = (√313 − 11)/6;  "
   "F(z; x, y) = z⁴x²y(1 + zy)/(16 − 8zy − 3z²xy − 3z³xy²),  F(1; x, 1) = x²/(4 − 3x):  K = n_L − 2,  G(x) = 1/(4 − 3x),  "
   "Pr(K = k) = (1/4)(3/4)^k,  E K = 3,  Var K = 12",
   "The symmetric states and the vector states one excursion visits, their spreads, and the pole of its visits to the symmetric states. "
   "With x marking each arrival at a vector state and y each arrival at a symmetric state, every return has two compulsory vector arrivals; "
   "the arrivals K beyond them have G(x) = 1/(4 − 3x), whose cumulants are %s." % ", ".join(str(c_) for c_ in cumK))
eq("74 directed edges,  M = 296 transitions,  C_h = 60 along h,  C_j = 59 along each other direction,  34 edges whose state does not contain h",
   "The available transitions, uniform under the stationary measure on these edges (not the transitions of one excursion): c_L = C_h/M = 15/74, η = 5C_j/M = 295/296, σ = 5C_h/M = 75/74, "
   "R_ud = 34/74 = 17/37, E_H = Eℓ C_h/320 = 3 transitions along h per mean return time.")
eq("b = G₀₀ + G_ff − 2G₀f,  G = (5I − A)⁺ = (7I + A)/32 − 3J/128:  b = 7/16", "The effective resistance between the singlet and a symmetric state at the critical step.")
eq("a = (1 − Φ(1))/8 = 5/38,  χ_A = 1/(1 + Φ(i)) = 13/12,  w_h = 1/(4χ_A) = 3/13,  χ_h = w_h(1 − w_h) = 30/169",
   "The signed returns at the even and the odd points, the share of h and its spread.")
eq("J_DE/C_W = (|D||E| − 5 tr P_DP_E)/72 at regular χ, and by rational continuation:  g² = 1/72 = −Φ(1)/[4(1 + Φ(1))] = −Φ(i)/[6(1 + Φ(i))] = e_ℓ²/8",
   "The response of two sets of directions against the clock that moves with it, as χ varies: 1/72 for a pair of directions on opposite sides, 1/18 for one direction against the other four, "
   "1/12 for the plane hk against the three directions outside it; the walk's first returns and the comparison's response are one number.")
eq("⟨Ω, (L + γ_h ⊗ γ_s)Ω⟩ = 6 + [s = h]", "The weight of one transition: the moment compared with itself, once more along the world line's own time.")
eq("D_θ(u) = D(u) + (e^(−iθ) − 1) u D′(u)/320:  arg 4u_c = θ/320 + O(θ³) per step as θ → 0, its rate d arg 4u_c/dθ = 1/320 at θ = 0", "One transition marked, exactly: every transition has the same cofactor. The phase on one directed edge: the unit rate.")

# =====================================================================================================================
# 5. The clock and the contact interaction
N2, kC = 10, 3
NC = kC * kC - 1
f = e_ ** 2 / N2
nu = f / El
marks = [0, 1, 2, 3, float(-1 / P1)]
gaps = [abs(p_ - q_) for p_, q_ in itertools.combinations(marks, 2)]
MQ = lambda s: sum(exp(-s * D / 4) for D in gaps) / len(gaps)
ED = sum(gaps) / len(gaps) / 4
hov = (MQ(float(nu)) * MQ(-float(nu))) ** (-1.5)
zk = lambda k_: 4 * (1j / 4) ** k_
pk = lambda k_: (-Phz(zk(k_))) if k_ % 2 else Fz(zk(k_))
Nh = sum((hov ** k_ * pk(k_)).real for k_ in range(1, 60))
Nh1 = sum(pk(k_).real for k_ in range(1, 60))
Ncon = sum(((-Phz(zk(k_))) if k_ % 2 else (Fz(zk(k_)) + Fz(-zk(k_))) / 2).real for k_ in range(1, 60))
x_ = float(nu) * hov / (M + 1 + Nh)
WW = Fz(hov) / hov ** 4 * (1 - 2 * float(b) + 2 * float(b) * hov)
chk("(30)-(34) f = 9/250, nu = 9/4000; the clock's gaps have mean E_D = 2; h, N_h, x, W_W",
    f == Fr(9, 250) and nu == Fr(9, 4000) and abs(ED - 2) < 1e-15 and abs(sum(pk(k_).real for k_ in range(60, 90)) * hov ** 60) < 1e-30,
    "h = %.11f, N_h = %.10f, x = %.6e, W_W = %.10f" % (hov, Nh, x_, WW))

sec("5. The clock and the contact interaction", "The world line's clock and the contact interaction of two sources, from the same excursion.")
eq("f = e²/N₂ = 9/250,  ν = f/Eℓ = 9/4000", "Two sources leaving the plane hk meet on one of the ten symmetric states; per mean return time.")
eq("M_Q(s) = (1/10) Σ_D e^(−sD),  D the ten gaps of the marks (0, 1, 2, 3, −1/Φ(1))/4:  E_D = 2,  h = [M_Q(ν)M_Q(−ν)]^(−3/2) = %.11f" % hov,
   "The clock's five marks: a quarter step for each of the four directions other than h and the long return 19/4 along h; the Bhattacharyya overlap of its two tilted distributions.")
eq("N_h = Re Σ_(k≥1) h^k p_k,  p_k = −Φ(4(i/4)^k) for odd k,  F(4(i/4)^k) for even k:  N_h = %.10f" % Nh,
   "The repeated return along h: the excursions as the steps of the law one level up.")
eq("x = νh/(M + 1 + N_h) = %s" % sci(x_, 6), "The contact interaction, closed once.")
eq("W_W = F(h) h⁻⁴ (1 − 2b + 2bh) = %.10f" % WW, "The weak contact interaction's retained excursion.")

# =====================================================================================================================
# 6. The four strengths
me = INPUTS["electron_mass_MeV"]
hbarc = INPUTS["planck_J_s"] * INPUTS["speed_of_light_m_s"] / (2 * pi * INPUTS["MeV_J"]) * 1e15
tf, ef, elf, af, bf = float(t_), float(e_), float(el_), float(a), float(b)
cLf, etaf, sigf, Rudf, EHf, chiAf, chihf, ff, nuf = map(float, (cL, eta, sigma, Rud, EH, chiA, chih, f, nu))
K0f = float(K[0])
alphas = row("D01", sqrt(elf ** 2 / NC))
alpha = cLf * ff / (1 - x_)
row("D02", 1 / alpha)
row("L19", (1 - nuf / (M + 1 + Nh1)) / (cLf * ff))
W = tf ** (kC * El) * etaf ** (kC * EHf)
row("D04", W * W * 1e39)
rp = sum(trans_weight[s] for (_, _, s) in avail_tr) + log(K0f) / LOm - af ** 5 - bf * af ** 6
row("J01", rp)
row("B12", rp)
mp = row("M1", me * rp)
GFmp2 = (1 - 1 / N2) * WW / M ** 2
GF = row("D03", GFmp2 / (mp / 1000) ** 2 * 1e5) * 1e-5
mpl = mp / 1000 / W
row("D05", mpl / 1e19)

sec("6. The four strengths", "Two sources meet at the distinction where they meet; each brings what its divided set asks, over the channels where they can meet.")
eq("α_s = [e_ℓ²/(k_C² − 1)]^(1/2) = 72^(−1/2) = %.9f" % alphas, "Colour: each source its reflection at a single direction, over the eight traceless rotations, as an amplitude.", ["D01"])
eq("α = c_L f/(1 − x):  1/α = %.9f;  with h = 1:  %.9f" % (1 / alpha, ROWS["L19"]),
   "The plane hk: the share of transitions along h, which give off no charge, times the two-source response at the plane, the contact closed once.", ["D02", "L19"])
eq("G_F m_p² = (1 − 1/N₂) W_W/M²:  G_F = %s GeV⁻²" % sci(GF, 8), "The plane of h and the singlet direction: one particular transition of each excursion, on the nine symmetric states other than the photon's.", ["D03"])
eq("W = t^(3Eℓ) η^(3E_H) = (2/5)⁴⁸(295/296)⁹,  α_G = Gm_p²/ħc = W² = %s,  M_Pl = m_p/W = %s GeV" % (sci(W * W, 6), sci(mpl, 8)),
   "The singlet: each source its whole excursion on the three colour directions, three excursions of sixteen steps at the transmission, nine transitions along h at η; one channel.",
   ["D04", "D05"])

# =====================================================================================================================
# 7. Rest poles: the symmetric and the vector states
rn = row("B13", K0f ** (5 * af ** 4 + 4 * af ** 10 + 10 * cLf * bf * af ** 6))
row("J02", rn)
row("B14", rp * rn)
mn = row("M2", mp * rn)


def level_factor(n, Ls, P):
    psi = 1 / 28 if P == 1 else 1 / 2
    eps = (1 + P) / 2
    clk = log(MQ(P * nuf)) / LOm if n == 10 else (n - eps) * P * nuf * ED / 4
    return exp(n / 2 * log(1 / elf) - psi * Ls * (n - eps) / 4 + clk)


rmu, rtau = row("B01", level_factor(10, 2, 1)), row("B02", level_factor(5, -2, 1))
pq_p, pq_q = row("B04", level_factor(10, 2, -1)), level_factor(5, -2, -1)
row("B05", pq_q * etaf)
row("B06", pq_q ** 2 * etaf ** 2 / pq_p)
row("B07", pq_q ** 2 * etaf ** 2 / pq_p)
row("B08", rmu / pq_p)
row("B09", Rudf)
kap_u = row("B10", (ef / tf) ** (El / EnF))
row("B11", Rudf * kap_u ** 5)
koide = (1 + rmu + rmu * rtau) / (1 + sqrt(rmu) + sqrt(rmu * rtau)) ** 2
row("B03", koide)
row("L17", koide)
row("L01", me * rmu * rtau)
row("L04", 3)
row("L05", (1 / elf) ** 2.5 * me)
# the three pairings of the four directions other than h, on the ten symmetric states: U_h = (e_ab + e_cd, e_ac + e_bd, e_ad + e_bc)/sqrt2,
# read against the rooted inverse Gamma_P, the inverse of 5I - A with the singlet removed, on the ten
rest = [i for i in range(16) if rel[i] != 0]
symi = [i for i in range(16) if pc(rel[i]) == 2]
GamR = np.linalg.inv((5 * I16 - A)[np.ix_(rest, rest)])
GamP = GamR[np.ix_([rest.index(i) for i in symi], [rest.index(i) for i in symi])]
AP, J10 = A[np.ix_(symi, symi)], np.ones((10, 10))
okGP = (np.allclose(GamP, (7 * np.eye(10) + 7 * J10 + AP) / 32) and np.allclose(np.linalg.inv(GamP), (24 * np.eye(10) - 4 * AP - J10) / 5)
        and np.allclose(AP @ AP, 2 * np.eye(10) - AP + J10))
okUh, pair_spec = True, []
for hh_ in range(d):
    a1, b1, c1, d1 = [s for s in range(d) if s != hh_]
    Uh = np.zeros((10, 3))
    for col, pair_ in enumerate([((a1, b1), (c1, d1)), ((a1, c1), (b1, d1)), ((a1, d1), (b1, c1))]):
        for (p1, p2) in pair_:
            Uh[symi.index(ri[(1 << p1) | (1 << p2)]), col] = 1 / sqrt(2)
    Mh = 10 * Uh.T @ np.linalg.inv(GamP) @ Uh
    okUh &= (np.allclose(Uh.T @ Uh, np.eye(3)) and np.allclose(Uh.T @ AP @ Uh, np.eye(3)) and np.allclose(Uh.T @ J10 @ Uh, 2 * np.ones((3, 3)))
             and np.allclose(Mh, 40 * np.eye(3) - 4 * np.ones((3, 3))))
    pair_spec.append([float(x_) for x_ in np.round(np.linalg.eigvalsh(Mh), 9)])
Psi_ab = -Phz(4 * (-1 / 5)) / (16 * (-1 / 5) ** 2)
chk("(43) the three pairings of the four directions other than h: U_h = (e_ab + e_cd, e_ac + e_bd, e_ad + e_bc)/sqrt2 on the ten symmetric states; "
    "Gamma_P = [(5I - A) without the singlet]^-1 on the ten = (7I + 7J + A_P)/32, Gamma_P^-1 = (24I - 4A_P - J)/5; "
    "10 U_h^T Gamma_P^-1 U_h = 40 I_3 - 4 J_3 at every h, common mode 28 = 1/Psi@{a,b}: three families",
    okGP and okUh and all(sp == [28.0, 40.0, 40.0] for sp in pair_spec) and abs(1 / Psi_ab - 28) < 1e-12,
    "spectrum " + ", ".join("%g" % x_ for x_ in pair_spec[0]))
down = me * (1 / elf) ** 1.5 * np.array([1 / etaf, pq_p / etaf, pq_p * pq_q])
up = Rudf * down * np.array([1., kap_u ** 5, kap_u ** 7.5])

sec("7. The rest poles", "A world line at rest is a zero of its block; a mass is the zero's angle in the unit of the electron's phase on one directed edge.")
eq("the electron: arg 4u_c = θ/320 + O(θ³) per step as θ → 0, its rate d arg 4u_c/dθ = 1/320 at θ = 0", "One directed edge meeting itself at weight one: the unit.")
eq("m_p/m_e = Σ_transitions ⟨Ω, (L + γ_h ⊗ γ_s)Ω⟩ + log k₀(−1/4)/L(Ω) − a⁵ − ba⁶ = 6M + C_h + (1/6) log(5/2) − a⁵ − (7/16)a⁶ = %.9f;  m_p = %.8f MeV" % (rp, mp),
   "The proton: the self-interaction on the available transitions, the Gram-determinant term per unit of L(Ω), less the signed-volume terms on the five vector states "
   "and on the seven sets that avoid h.", ["J01", "B12", "M1"])
eq("m_n/m_p = k₀(−1/4)^(5a⁴ + 4a¹⁰ + 10c_L b a⁶) = %.11f;  m_n = %.9f MeV" % (rn, mn),
   "The neutral pole spread over the ten symmetric states: the nine Petersen contrasts 5a⁴ + 4a¹⁰ and the opened seven-volume on the ten symmetric states.", ["B13", "J02", "B14", "M2"])
eq("log ℒ(n, L*, P) = (n/2) log(1/e_ℓ) − (Ψ_P L*/4)(n − ε_P) + c_n(P),  Ψ₊ = 1/28,  Ψ₋ = 1/2,  ε_P = (1 + P)/2,  "
   "c₁₀(P) = (1/6) log M_Q(Pν),  c₅(P) = (5 − ε_P)Pν E_D/4",
   "One rule for the symmetric and the vector states: √3 per opened two-spinor state, Ψ_P with the comparison L* on those states, and the clock, at the two signs P = ±1.")
eq("m_μ/m_e = ℒ(10, 2, +) = 3⁵ e^(−9/56) M_Q(ν)^(1/6) = %.9f,  m_τ/m_μ = ℒ(5, −2, +) = 3^(5/2) e^(1/14 + 2ν) = %.10f" % (rmu, rtau),
   "The charged leptons: the symmetric states opened, then the vector states; three families from the three pairings of the four directions other than h, "
   "U_h = (e_ab + e_cd, e_ac + e_bd, e_ad + e_bc)/√2 on the ten symmetric states, with 10U_hᵀΓ_P⁻¹U_h = 40I₃ − 4J₃, spectrum 28, 40, 40, "
   "Γ_P = (7I + 7J + A_P)/32 the inverse of 5I − A without the singlet, on the ten, and 28 = 1/Ψ@{a,b}; "
   "3^(5/2) m_e with no rest pole; Koide %.8f." % koide, ["B01", "B02", "L01", "B03", "L17", "L04", "L05"])
eq("p_q = ℒ(10, 2, −) = %.6f,  q_q = ℒ(5, −2, −):  m_s/m_d = p_q,  m_b/m_s = q_q η = %.6f,  (m_d, m_s, m_b) = 3^(3/2) m_e (1/η, p_q/η, p_q q_q)" % (pq_p, pq_q * etaf),
   "The quarks: the same states at the odd sign; an open colour rest pole carries 1/η. At the Z pole d %.4f, s %.3f, b %.2f MeV." % tuple(down),
   ["B04", "B05", "B06", "B07", "B08"])
eq("m_u/m_d = R_ud = 17/37,  κ = (e/t)^(Eℓ/E n_F) = (3/2)^(8/5) = %.6f,  m_c/m_s = R_ud κ⁵" % kap_u,
   "The up-type levels: the edges whose state does not contain h, and the reflection over transmission per visit to a symmetric state. u %.4f, c %.2f MeV." % (up[0], up[1]),
   ["B09", "B10", "B11"])

# =====================================================================================================================
# 8. The direction h
v = row("D15", (sqrt(2) * GF) ** (-.5))
sw = row("D08", 3 * Nh)
row("L20", 3 * Nh1)
row("D09", 3 * Ncon)
osw = row("D10", sw / (1 + ff))
row("D14", ff)
mw = row("D11", v * sqrt(pi * alpha / ((1 - ff) * osw)))
row("L15", mw)
mz = row("D12", mw / sqrt(1 - osw))
row("D13", mw / mz)
lamH = pi * alpha / chihf
mh = row("D16", v * sqrt(2 * lamH))
mt = row("D17", v * sqrt(etaf / (2 * sigf)))
row("S07", mp * mp / (EnF * me) / 1000)

sec("8. The direction h", "The direction h held at its length v in the plane hk: the rotations it moves, its radial direction, its own count.")
eq("v = (√2 G_F)^(−1/2) = %.6f GeV" % v, "The length of h.", ["D15"])
eq("s² = 3N_h = %.7f,  s²_OS = 3N_h/(1 + f) = %.7f;  with h = 1:  3N_h = %.7f;  the contact's angle 3 Σ_k p̄_k = %.7f" % (sw, osw, 3 * Nh1, 3 * Ncon),
   "The weak angle: the repeated return along h once for each of the three directions outside the plane hk; on shell the plane's two-source response once more; "
   "p̄_k the even returns symmetrized.", ["D08", "D10", "L20", "D09", "D14"])
eq("M_W² = παv²/[(1 − f)s²_OS] :  M_W = %.5f GeV,  M_Z = M_W/(1 − s²_OS)^(1/2) = %.5f GeV" % (mw, mz),
   "The rotations h moves.", ["D11", "L15", "D12", "D13"])
eq("λ_H = πα/χ_h = %.6f,  m_H = v(2λ_H)^(1/2) = %.4f GeV" % (lamH, mh), "The radial direction of h: the electric coupling over the spread of the share of h.", ["D16"])
eq("m_t = v(η/2σ)^(1/2) = %.3f GeV;  m_p²/(E n_F m_e) = %.2f GeV" % (mt, ROWS["S07"]), "The top: the available transitions along another direction over those along h, as an amplitude.",
   ["D17", "S07"])

# =====================================================================================================================
# 9. Mixing and the neutral poles


def rot(i, j, s, phase=0.):
    out = np.eye(3, dtype=complex)
    out[i, i] = out[j, j] = sqrt(1 - s * s)
    out[i, j] = s * np.exp(-1j * phase)
    out[j, i] = -s * np.exp(1j * phase)
    return out


TrL2 = float(np.trace(L @ L).real)
dq = row("C04", atan2(16, 7))
s12, s23 = row("C01", (VarnF - Cov ** 2 / VarnL) / (El * float(K[0]))), row("C02", 4 / TrL2)
s13 = row("C03", s12 * tf * s23)
Vq = rot(1, 2, s23) @ rot(0, 2, s13, dq) @ rot(0, 1, s12)
row("C05", (Vq[0, 1] * Vq[1, 2] * Vq[0, 2].conjugate() * Vq[1, 1].conjugate()).imag * 1e5)
ang = [np.degrees(np.angle(-Vq[i, 0] * Vq[i, 2].conjugate() / (Vq[j, 0] * Vq[j, 2].conjugate()))) % 360 for i, j in [(2, 0), (1, 2), (0, 1)]]
row("C06", ang[0])
row("C07", ang[1])
row("C08", ang[2])
row("C09", float(np.sum(abs(Vq[:2]) ** 2)))
row("K05", float(sum(abs(np.diag(Vq)) ** 2)))
Ul = rot(0, 1, sqrt(2 * bf) * s12, pi / 2 - dq).conj().T @ rot(1, 2, 1 / sqrt(2)) @ rot(0, 1, sqrt(bf))
S13 = row("C11", abs(Ul[0, 2]) ** 2)
S12 = row("C10", abs(Ul[0, 1]) ** 2 / (1 - S13))
S23 = row("C13", abs(Ul[1, 2]) ** 2 / (1 - S13))
row("C12", 4 * S13 * (1 - S13))
jl = row("T06", (Ul[0, 0] * Ul[1, 1] * Ul[0, 1].conjugate() * Ul[1, 0].conjugate()).imag)
scale_ = sqrt(S12 * (1 - S12) * S23 * (1 - S23) * S13)
row("C14", np.degrees(atan2(jl / (scale_ * (1 - S13)), (abs(Ul[1, 0]) ** 2 - S12 * (1 - S23) - (1 - S12) * S23 * S13) / (2 * scale_))) % 360)
rho = tan(pi / 8) ** 2
y = sigf * v / (mp / 1000) * np.array([0., sqrt(rho), 1.]) / sqrt(2)
XR = elf ** 9 / W
neut = 2 * y * y / (XR + np.sqrt(XR * XR + 4 * y * y)) * mp * 1e6
row("E06", neut[2] * 1e3)
row("E01", neut[1] ** 2 * 1e5)
row("E02", neut[2] ** 2 * 1e3)
row("E03", (neut[2] ** 2 - neut[1] ** 2) * 1e3)
row("E04", neut[1] / neut[2])
row("E05", (neut[2] / neut[1]) ** 2)
row("E07", 3)
row("K02", float(sum(neut)))
row("K03", float(sum(neut)))
row("L03", rho ** -2)
row("T01", mpl * elf ** 9)
row("T02", mpl * elf ** 6)
# the heavy neutral exponent. C^5 = C (+) Ch (+) Ck, with colour C = {2, 3, 4}, h = 0, k = 1; the algebra kept by the split, the volume and h is
# k = {X(A) = diag(A, 0, -Tr A) : A in u(3)}; it acts on the sixteen even states by rho(X) = sum X_ab c_a^dag c_b, with the alternating signs


def cre_ann(a_, b_):
    out = np.zeros((16, 16))
    for S in rel:
        if (S >> b_) & 1:
            S1 = S & ~(1 << b_)
            if not (S1 >> a_) & 1:
                out[ri[S1 | (1 << a_)], ri[S]] += (-1) ** (pc(S & ((1 << b_) - 1)) + pc(S1 & ((1 << a_) - 1)))
    return out


rho_ext = lambda X: sum(X[a_, b_] * cre_ann(a_, b_) for a_ in range(d) for b_ in range(d) if X[a_, b_] != 0)
colour, hdir, kdir = [2, 3, 4], 0, 1
kept_alg = [1j * (Eu(ca_, ca_) - Eu(kdir, kdir)) for ca_ in colour]
for ca_, cb_ in itertools.combinations(colour, 2):
    kept_alg += [Eu(ca_, cb_) - Eu(cb_, ca_), 1j * (Eu(ca_, cb_) + Eu(cb_, ca_))]
in_k = all(np.allclose(X, -X.conj().T) and abs(np.trace(X)) < 1e-15 and np.allclose(X[hdir], 0) and np.allclose(X[:, hdir], 0)
           and np.allclose(X[np.ix_(colour, [kdir])], 0) and abs(X[kdir, kdir] + np.trace(X[np.ix_(colour, colour)])) < 1e-15 for X in kept_alg)
dim_k = int(np.linalg.matrix_rank(np.array([np.concatenate([X.real.ravel(), X.imag.ravel()]) for X in kept_alg])))
# the coherent comparison on the sixteen even states: L read through the paired vectors (g_S x 1) Omega, D_coh = |L|/L(Omega)
L_even = (Hp.conj().T @ L @ Hp).real
Dcoh = np.diag(np.abs(np.diag(L_even)) / LOm)
Rk = [rho_ext(X) for X in kept_alg]
Gk = np.array([[np.trace(P_.conj().T @ Q_).real for Q_ in Rk] for P_ in Rk])
Hk = np.array([[np.trace(P_.conj().T @ Dcoh @ Q_).real for Q_ in Rk] for P_ in Rk])
Gk_form = np.block([[4 * np.eye(3) + 4 * np.ones((3, 3)), np.zeros((3, 6))], [np.zeros((6, 3)), 8 * np.eye(6)]])
det_k = np.linalg.det(np.linalg.solve(Gk, Hk))
# the rotations across the split, Hom_C(F, C), F = {h, k}: six complex directions
across = [Eu(ca_, fa_) for ca_ in colour for fa_ in (hdir, kdir)]
Ro = [rho_ext(X) for X in across]
Go = np.array([[np.trace(P_.conj().T @ Q_) for Q_ in Ro] for P_ in Ro])
Ho = np.array([[np.trace(P_.conj().T @ Dcoh @ Q_) for Q_ in Ro] for P_ in Ro])
det_o = np.linalg.det(np.linalg.solve(Go, Ho))
MR_k, Moff_o = mpl * det_k, mpl * det_o.real
chk("(53) the heavy neutral exponent: k = {diag(A, 0, -Tr A) : A in u(3)} of real dimension 9 = 3 + 2 C(3, 2); rho(X) = sum X_ab c_a^dag c_b on the "
    "sixteen even states annihilates the singlet and never reaches it, so D_coh = |L|/L(Omega) = Pi_0 + (I - Pi_0)/3 gives D_coh rho(X) = rho(X)/3; "
    "G = [[8,4,4],[4,8,4],[4,4,8]] (+) 8 I_6, H = G/3, det(G^-1 H) = 3^-9 = e_l^9; on Hom_C(F, C), complex dimension 6, Gram 4 I_6, det_C = 3^-6 = e_l^6; "
    "M_R = M_Pl 3^-9 = T01, M_off = M_Pl 3^-6 = 27 M_R = T02",
    in_k and dim_k == 9 == 3 + 2 * comb(3, 2) and np.allclose(L_even, np.diag([6 - 2 * pc(S) for S in rel]))
    and np.allclose(Dcoh, np.diag([1.0] + [1 / 3] * 15)) and all(np.allclose(R_[ri[0]], 0) and np.allclose(R_[:, ri[0]], 0) for R_ in Rk + Ro)
    and all(np.allclose(Dcoh @ R_, R_ / 3) for R_ in Rk + Ro) and np.allclose(Gk, Gk_form) and np.allclose(Hk, Gk / 3)
    and abs(det_k / float(el_ ** dim_k) - 1) < 1e-12 and el_ ** dim_k == Fr(1, 3 ** 9)
    and len(across) == 6 == int(np.linalg.matrix_rank(np.array([X.ravel() for X in across]))) and np.allclose(Go, 4 * np.eye(6))
    and np.allclose(Ho, Go / 3) and abs(det_o / float(el_ ** len(across)) - 1) < 1e-12
    and abs(MR_k / ROWS["T01"] - 1) < 1e-12 and abs(Moff_o / ROWS["T02"] - 1) < 1e-12 and abs(Moff_o / MR_k - 27) < 1e-9,
    "M_R = %.11e GeV, M_off = %.11e GeV" % (MR_k, Moff_o))

sec("9. Mixing and the neutral poles", "Two closed world lines overlap; the neutral block of h feeds a heavy neutral pole.")
eq("s₁₂ = (Var n_F − Cov²/Var n_L)/(Eℓ · 5/2) = 9/40,  s₂₃ = 4/Tr L² = 1/24,  s₁₃ = s₁₂ t s₂₃ = 3/800,  δ_q = arg(b + i) = arg(7 + 16i):  "
   "V = R₂₃(s₂₃) R₁₃(s₁₃, δ_q) R₁₂(s₁₂)",
   "The quark mixing: the spread of the visits to the symmetric states left when the visits to the vector states are known, per mean return time and per inverse transmission; "
   "four over Tr L²; the far one through the transmission; the phase the complex weight b + i. J_q = %s, angles %.2f°, %.2f°, %.2f°." % (sci(ROWS["C05"] * 1e-5, 4), *ang),
   ["C01", "C02", "C03", "C04", "C05", "C06", "C07", "C08", "C09", "K05"])
eq("U = R₁₂(√(2b) s₁₂, π/2 − δ_q)† R₂₃(1/√2) R₁₂(√b)",
   "The lepton mixing, the same frame from the other end: s²₁₂ = %.5f, s²₁₃ = %.6f, s²₂₃ = %.5f, δ_l = %.1f°." % (S12, S13, S23, ROWS["C14"]),
   ["C10", "C11", "C12", "C13", "C14", "T06"])
eq("M_R = M_Pl e_ℓ⁹ = M_Pl det(G⁻¹H) = M_Pl 3⁻⁹ = %s GeV,  M_off = M_Pl e_ℓ⁶ = M_Pl det_ℂ(G_off⁻¹H_off) = M_Pl 3⁻⁶ = 27M_R = %s GeV;  "
   "y = σ(v/m_p)(0, ρ_ν^(1/2), 1)/√2,  ρ_ν = tan²(π/8);  m_i = 2y_i² m_p/[X_R + (X_R² + 4y_i²)^(1/2)],  X_R = e_ℓ⁹/W" % (sci(MR_k, 8), sci(Moff_o, 8)),
   "The heavy neutral pole: the algebra kept by the plane hk and the direction h, k = {diag(A, 0, −Tr A): A ∈ u(3)} on ℂ⁵ = C ⊕ ℂh ⊕ ℂk, of real "
   "dimension 3 + 2·C(3, 2) = 9, acts on the sixteen even states by ρ(X) = Σ X_ab c_a†c_b, which annihilates the singlet and never reaches it; "
   "the coherent comparison D_coh = |L|/L(Ω) = Π₀ + (I − Π₀)/3 therefore pulls back to H = G/3, G = [[8, 4, 4], [4, 8, 4], [4, 4, 8]] ⊕ 8I₆ in the "
   "three diagonal and six off-diagonal coordinates, one reflection at a single direction for each of the nine; on Hom_ℂ(F, C), of complex "
   "dimension six, G_off = 4I₆. The seesaw: m = 0, %.3f, %.3f meV, three light channels." % (neut[1] * 1e3, neut[2] * 1e3),
   ["E07", "E01", "E02", "E03", "E04", "E05", "E06", "K02", "K03", "L03", "T01", "T02"])

# =====================================================================================================================
# 10. The nucleon
sig3 = [sx, sy, sz]


def on3(r, X):
    mats = [I4, I4, I4]
    mats[r] = X
    return np.kron(np.kron(mats[0], mats[1]), mats[2])


def perm3(pm):
    Pm = np.zeros((64, 64))
    for i, j, l in itertools.product(range(4), repeat=3):
        ix = [i, j, l]
        nw = [ix[pm[0]], ix[pm[1]], ix[pm[2]]]
        Pm[nw[0] * 16 + nw[1] * 4 + nw[2], i * 16 + j * 4 + l] = 1
    return Pm


Psym = sum(perm3(pm) for pm in itertools.permutations(range(3))) / 6
Ssq = sum((sum(on3(r, np.kron(sg / 2, s0)) for r in range(3))) @ (sum(on3(r, np.kron(sg / 2, s0)) for r in range(3))) for sg in sig3)
PN = Psym @ (15 / 4 * np.eye(64) - Ssq) / 3
wv3, vv3 = np.linalg.eigh(PN @ (sum(on3(r, np.kron(sz / 2, s0)) for r in range(3)) + 10 * sum(on3(r, np.kron(s0, sz / 2)) for r in range(3))) @ PN)
pup = vv3[:, np.argmax(wv3)]
axial = float((pup.conj() @ sum(on3(r, np.kron(sz, sz)) for r in range(3)) @ pup).real)
chk("(54) the nucleon projected: P_N of rank 4 in the symmetric 20; <p up| sum sigma_z tau_z |p up> = 5/3",
    np.allclose(PN @ PN, PN) and round(np.trace(PN).real) == 4 and round(np.trace(Psym).real) == 20 and abs(axial - 5 / 3) < 1e-12)
gA = row("S01", axial * tf ** (2 * bf / 3))
lp = hbarc / mp
row("G01", 4 * lp)
row("S04", sqrt(EnF) * lp)
row("S02", (VarnF - Cov ** 2 / VarnL) * lp * lp)
row("S03", sqrt(VarnF - Cov ** 2 / VarnL) * lp)
row("S05", INPUTS["neutron_rate_normalization_s"] / (INPUTS["neutron_rate_factor"] * abs(Vq[0, 0]) ** 2 * (1 + 3 * gA * gA)))
eps2 = alpha ** 2 / (1 + alpha / N2)
mup = row("G03", sqrt(Varl / (2 * N2) * (1 - eps2 / (El ** 2 * bf))))
mun = row("G04", -4 * (1 + EnF) / 23 * sqrt(1 - eps2 / (El ** 2 * bf)))
row("G05", mun / mup)
Bd = mp * sqrt(chiAf) * af ** 3 * (1 - (1 + tf / El) * eps2)
row("G13", (16 * (mup + mun) + mn / (mp + mn)) / 17 - (Bd / mp) * ((mup + mun) - mn / (mp + mn)) / (20 + 13 * Bd / mp))
fpi = row("G08", etaf * mp * sqrt(2 * kC) / (2 * pi * mup))
row("G09", fpi * abs(Vq[0, 0]))
row("A002", 5 * mp / 36)
row("A003", 5 * mp / 36 * abs(Vq[0, 0]))

sec("10. The nucleon", "The three colour world lines close in the totally antisymmetric state, so their spin and isospin stand in the symmetric space; the nucleon is projected "
    "out of it before its currents are read.")
eq("P_N = P_sym(15/4 − S²)/3,  ⟨p↑| Σ_r σ_zτ_z |p↑⟩ = 5/3:  g_A = (5/3) t^(2b/3) = %.6f" % gA,
   "The axial coupling: the projected proton's axial current times the transmission to the power 2b/3; τ_n = %.2f s with |V_ud| and G_F; "
   "the axial radius² (Var n_F − Cov²/Var n_L)λ_p²." % ROWS["S05"], ["S01", "S05", "S02", "S03"])
eq("μ_p = [Var ℓ/(2N₂) · (1 − ε₂/(Eℓ²b))]^(1/2) = %.10f,  μ_n = −[4(1 + E n_F)/23] (1 − ε₂/(Eℓ²b))^(1/2) = %s,  ε₂ = α²/(1 + α/N₂)" % (mup, mn_("%.10f" % mun)),
   "The moments: the spread of the excursion's length over the twenty channels of the symmetric states, less the plane's own coupling once; the deuteron's from the two with "
   "its binding m_p χ_A^(1/2) a³[1 − (1 + t/Eℓ)ε₂].", ["G03", "G04", "G05", "G13"])
eq("λ_p = ħ/m_pc = %.10f fm:  r_p = (Eℓ)^(1/2) λ_p = 4λ_p = %.6f fm,  r_π = (E n_F)^(1/2) λ_p = %.5f fm" % (lp, 4 * lp, sqrt(EnF) * lp),
   "The step is the proton's reduced Compton length; a size is the root of a count of the excursion.", ["G01", "S04"])
eq("f_π = η m_p (2k_C)^(1/2)/(2πμ_p) = %.3f MeV,  5m_p/36 = %.3f MeV" % (fpi, 5 * mp / 36), "The pion's decay constant, two constructions.",
   ["G08", "G09", "A002", "A003"])

# =====================================================================================================================
# 11. Colour
row("K01", 0)
row("L16", 0)
row("L14", NC)
row("S16", mz * 1000 * exp(-2 * pi / ((23 / 3) * alphas)))
inv = 1 / np.array([Rudf, 1, pq_p])
low = np.linalg.eigvalsh([[Rudf + 1, (Rudf - 1) / sqrt(3)], [(Rudf - 1) / sqrt(3), (Rudf + 1 + 4 * pq_p) / 3]])[0]
row("I08", 1 / (low * sum(inv)))
row("I09", -sum(inv ** 3) / (12 * sum(inv) ** 3))
life_yr = 72 ** 2 * (INPUTS["planck_J_s"] / (2 * pi) / INPUTS["MeV_J"]) / (3 ** 24 * W ** 4 * mp) / (INPUTS["julian_year_days"] * 86400)
row("K06", life_yr)
row("L12", life_yr)
okpos = True
for _ in range(5):
    thr = rng.uniform(0, 2 * pi, 40)
    AU = np.zeros((16, 16), dtype=complex)
    for (x1, x2), j in lid.items():
        AU[ri[x2], ri[x1]] += np.exp(1j * thr[j])
        AU[ri[x1], ri[x2]] += np.exp(-1j * thr[j])
    for u in (0.05, 0.15, 0.24):
        okpos &= np.linalg.eigvalsh((1 + 4 * u * u) * I16 - u * AU).min() >= (1 - u) * (1 - 4 * u) - 1e-12
chk("(58) with any phases on the forty links the law stays positive below the zero, (1 + 4u^2) - u A_U >= (1 - u)(1 - 4u): theta-bar = 0", okpos)

sec("11. Colour", "Rotations within the sides with no centre and no clock of their own; colour always closes.")
eq("(1 + 4u²) − uA_U ⪰ (1 − u)(1 − 4u) for every unitary connection U, 0 ≤ u < 1/4;  with the reversal-paired positive sector sum:  θ̄ = 0", "For 0 ≤ u < 1/4 the sector weights a_q are positive and, the closed weights being real, paired, a_q = a_−q; with a₁ > 0 the sector sum is maximal only at θ = 0 modulo 2π, and the mass determinant carries no phase: no strong phase.", ["K01", "L16"])
eq("eight traceless rotations;  the one-loop scale M_Z e^(−2π/((23/3)α_s)) = %.1f MeV" % ROWS["S16"], "The colour term's components and its scale.", ["L14", "S16"])
eq("χ_top/(F_π² m_π⁰²) = 1/(λ_low Σ_j S_j⁻¹) = %.4f,  b₂ = −Σ_j S_j⁻³/[12(Σ_j S_j⁻¹)³] = %s,  S = (R_ud, 1, p)" % (ROWS["I08"], mn_("%.5f" % ROWS["I09"])),
   "The light levels' lowest mode and third moment: the strong curvature and its fourth cumulant.", ["I08", "I09"])
eq("τ/B(e⁺π⁰) = 72² ħ/(3²⁴ W⁴ m_p) = %s yr" % sci(life_yr, 3), "The proton's partial lifetime, through the six rotations that mix the three-plus-two split.",
   ["K06", "L12"])

# =====================================================================================================================
# 12. The stationary state
tau_ = 2 * pi / (El * rp)
s_sym = ef / N2
lam = row("D06", 3 * W ** 6 * tau_ * s_sym ** 3 * 1e122) * 1e-122
mpcfm = INPUTS["megaparsec_m"] * 1e15
ellR = row("T03", lp / (W ** 2 * sqrt(tau_ * s_sym ** 3)) / mpcfm)
row("T04", hbarc * 1e6 / (2 * pi * ellR * mpcfm))
row("L10", 3 * pi / lam)
row("L08", -1)
# one source for the 3 and the 12: the one positive volume a^11 on the eleven states of positive comparison value, with the connected
# return of the vector arrivals beyond the two compulsory ones, C(j) = a^11 log G(e^j) = -a^11 log(4 - 3e^j)
n_pos = sum(1 for x_ in specL if x_ > 0)
Csrc = lambda j: -af ** n_pos * log(4 - 3 * exp(j))
hj = 1e-4
C1n, C2n = (Csrc(hj) - Csrc(-hj)) / (2 * hj), (Csrc(hj) - 2 * Csrc(0) + Csrc(-hj)) / hj ** 2
chk("(62)-(63) one source for the 3 and the 12: the positive volume a^11 on the eleven states of positive comparison value and the vector return "
    "beyond its two compulsory arrivals, C(j) = a^11 log G(e^j) = -a^11 log(4 - 3e^j); C'(0) = a^11 E K = 3a^11 = eta_B, "
    "C''(0) = a^11 Var K = 12a^11, the coefficient of A_s = 12a^11 (0.05 l)^(-1/40)",
    n_pos == 11 and Csrc(0) == 0 and abs(C1n / (EKf * af ** 11) - 1) < 1e-6 and abs(C2n / (VarKf * af ** 11) - 1) < 1e-6
    and a ** 11 * EK == 3 * a ** 11 and a ** 11 * VarK == 12 * a ** 11,
    "C'(0) = %.10e, C''(0) = %.10e" % (EKf * af ** 11, VarKf * af ** 11))
row("F01", EKf * af ** 11 * 1e10)
row("C15", 1 - tf / El)
row("C16", 0)
row("L06", 0)
row("F03", log(1e10 * VarKf * af ** 11 * (INPUTS["primordial_pivot_Mpc_inv"] * ellR) ** (-1 / 40)))
row("S08", bf ** 24 * (INPUTS["primordial_pivot_Mpc_inv"] * ellR) ** (-1 / 40) * 1e9)
row("L11", 16 * lam / (3 * pi * VarKf * af ** 11))
row("F04", 3 * etaf * sigf ** (4 / 3))
row("F13", 0)
row("L07", 0)
row("S09", M / (M - 4 * Ch))
for rid_, v_ in [("D07", 0), ("L09", 0), ("H01", 2), ("H02", 1), ("H03", 1), ("L18", 15 * pi / 4)]:
    row(rid_, v_)
TkB = hbarc * 1e6 / (2 * pi * ellR * mpcfm)

sec("12. The stationary state", "The stationary weight on the states of the whole system.")
eq("C(j) = a¹¹ log G(e^j) = −a¹¹ log(4 − 3e^j):  η_B = C′(0) = a¹¹ E K = 3a¹¹ = %s" % sci(EKf * af ** 11, 4),
   "Baryons per photon: the signed return on the eleven states of positive comparison value, one exterior volume a¹¹, carried by the vector "
   "arrivals K of one return beyond its two compulsory ones; the first derivative of their connected source.", ["F01"])
eq("n_s = 1 − t/Eℓ = 39/40,  dn_s/d ln k = 0;  A_s = C″(0)(0.05ℓ)^(−1/40) = a¹¹ Var K (0.05ℓ)^(−1/40) = 12a¹¹(0.05ℓ)^(−1/40):  "
   "ln(10¹⁰A_s) = %.4f;  r = 16Λℓ_P²/(3π·12a¹¹)" % ROWS["F03"],
   "The primordial spectrum, the second derivative of the same source, its tilt and its tensor share; a second construction b²⁴(0.05ℓ)^(−1/40).",
   ["C15", "C16", "L06", "F03", "S08", "L11"])
eq("Λℓ_P² = 3W⁶τs³ = %s,  τ = 2π/(Eℓ m_p/m_e),  s = e/N₂ = 3/50;  ℓ = λ_p/[W²(τs³)^(1/2)] = %.2f Mpc,  k_BT = ħc/(2πℓ) = %s eV,  S = 3π/(Λℓ_P²)"
   % (sci(lam, 4), ellR, sci(TkB, 4)),
   "The constant term in the unit of the step: the angle τ, the electron's phase during 1/Eℓ of a proton Compton period, and one arrival at a symmetric state, "
   "each carried by the proton's three colour excursions; the de Sitter radius, temperature and entropy; w = −1.", ["D06", "T03", "T04", "L10", "L08"])
eq("N_eff = 3ησ^(4/3) = %.4f,  Ω_k = 0,  M/(M − 4C_h) = %.4f" % (ROWS["F04"], ROWS["S09"]),
   "The light species, the flat frame, the cold matter over the baryons by the available transitions.", ["F04", "F13", "L07", "S09"])
eq("d log α/d(Φ/c²) = 0,  1 + γ = 2,  geodetic drift / Einstein = 1,  second-order bending 15π/4,  the two orders in coherent superposition tell commuting and anticommuting pairs apart with certainty",
   "Gravitation's tests and the two orders: α the same at every location, light bent twice Newton's, the quantum switch.", ["D07", "L09", "H01", "H02", "L18", "H03"])

# =====================================================================================================================
# 13. The classical equation and the check of every row
sec("13. The classical equation with every number in front of every term",
    "Γ = ∫d⁴x √−g [ (R − 2Λ)/16πG − Σ_X F_X²/16πα_X + ψ̄iγ^μD_μψ − (ψ̄_L𝒴φψ_R + h.c.) − (D_μφ)†D^μφ − λ_H(φ†φ − v²/2)² ]")
MD.append("| term | its number | formula |")
MD.append("|---|---|---|")
tg = lambda *ks: ", ".join(TAG[k_] for k_ in ks)
for tm, num, fm in [("(R − 2Λ)/16πG", "Gm_p²/ħc = %s; Λℓ² = 3, Λℓ_P² = %s" % (sci(W * W, 6), sci(lam, 4)), tg("EC", "D04", "D06")),
                    ("F²/16πα", "1/α = %.9f" % (1 / alpha), tg("D02")),
                    ("F²/16πα_s", "α_s = %.9f" % alphas, tg("D01")),
                    ("the weak rotations", "s² = %.7f, on shell %.7f" % (sw, osw), tg("D08")),
                    ("ψ̄iγ^μD_μψ", "cos ω = cos μ cos k; c one step per step", tg("KG", "Dirac")),
                    ("lepton Yukawas", "m_μ/m_e = %.6f, m_τ/m_μ = %.6f" % (rmu, rtau), tg("B01")),
                    ("native quark roots", "d %.4f, s %.3f, b %.2f, u %.4f, c %.2f MeV; t %.3f GeV" % (*down, up[0], up[1], up[2] / 1000), tg("B04", "B09", "D17")),
                    ("quark mixing", "9/40, 1/24, 3/800, arg(7 + 16i)", tg("C01")),
                    ("lepton mixing", "%.5f, %.6f, %.5f, %.1f°" % (S12, S13, S23, ROWS["C14"]), tg("C10")),
                    ("neutrinos", "0, %.3f, %.3f meV" % (neut[1] * 1e3, neut[2] * 1e3), tg("E06")),
                    ("(D_μφ)†D^μφ − λ_H(φ†φ − v²/2)²", "v = %.6f GeV, λ_H = %.6f, m_H = %.4f GeV" % (v, lamH, mh), tg("D15", "D16")),
                    ("θ̄FF̃", "θ̄ = 0", tg("K01")),
                    ("the scale", "λ_p = %.10f fm, m_p/m_e = %.9f" % (lp, rp), tg("J01", "G01"))]:
    MD.append("| %s | %s | %s |" % (tm, num, fm))
MD.append("")

SPL = re.compile(r"(?<!\\)\|")
table = {}
with io.open(TABLE, encoding="utf-8") as fh:
    for l in fh:
        if l.startswith("| ") and not l.startswith("| row |") and not l.startswith("| variable"):
            cc = [x.strip() for x in SPL.split(l.strip()[1:-1])]
            if len(cc) == 7:
                table[cc[0]] = dict(name=cc[1], value=cc[4], record=cc[5])
MAIN = ("D04 D05 H01 H02 L18 D07 L08 D06 T03 T04 L10 D02 L19 L09 G03 G04 G05 G13 G01 S04 J01 B12 M1 B13 J02 B14 M2 B01 B02 L01 B03 L17 "
        "L05 L04 B04 B05 B06 B07 B08 B09 B10 B11 D03 D15 D11 D12 D13 D08 D09 D10 D14 D16 D17 L15 L20 S07 S01 S05 S02 S03 G08 G09 A002 "
        "A003 C01 C02 C03 C04 C05 C06 C07 C08 C09 K05 C10 C11 C12 C13 C14 T06 E07 E01 E02 E03 E04 E05 E06 K02 K03 L03 T01 T02 D01 L14 "
        "S16 K01 L16 I08 I09 K06 L12 F01 F03 S08 C15 C16 L06 L11 F04 F13 L07 S09 H03").split()
same, bad = 0, []
for rid in MAIN:
    val = ROWS[rid]
    tv = table[rid]["value"]
    try:
        tvf = float(tv)
    except Exception:
        bad.append((rid, "no float", tv))
        continue
    nd = len(tv.split(".")[1]) if "." in tv and "e" not in tv.lower() else 12
    if (abs((val - tvf) / tvf) < 1e-6 if tvf else abs(val) < 1e-9) or abs(val - tvf) <= 0.6 * 10 ** (-nd):
        same += 1
    else:
        bad.append((rid, val, tv))
chk("the formulas alone give all 113 rows of the main line, each agreeing with the table's value to a relative 1e-6 or within its printed digits",
    len(MAIN) == 113 and len(set(MAIN)) == 113 and set(MAIN) <= set(ROWS) and same == 113, bad[:6])

sec("14. Several world lines bound together",
    "The hadrons beyond the nucleon and the nuclei use joint closed walks of several world lines: 56 scalar records appear in "
    "programs/classical_experiments.py, experiments E3, E5 and F. The article_results.py calculation evaluates twelve further literal composite expressions; their results and the remaining equations appear in docs/NUMBERS.md.")

# =====================================================================================================================
# 15. The rules read out of the law
# (a) the one rule at every divided set: the six directions n, h, k, c1, c2, c3; a divided set S, k_S its directions among the five,
#     z_S = i^|S|, P = z_S^2, L_S = sum over the five directions of (P on S, 1 off S) = (5 - k_S) + k_S P, w_S = z_S/L_S. Psi_S is
#     the law's own signed first return, counted on B, read at the divided set: Psi_S = -Phi(4 w_S)/(16 w_S^2); the reflection
#     and the transmission e_S = 1 - 2|w_S|, t_S = 2|w_S|; the channels of a two-source response N(S) = |S|(6 - |S|) + [|S| odd].
RULE = {}
for S in range(64):
    nS, kS, size = S & 1, pc(S >> 1), pc(S)
    zS = 1j ** size
    PS = int(round((zS * zS).real))
    LS = (5 - kS) + kS * PS
    wS = zS / LS
    PsiS = -first_return(4 * wS, True) / (16 * wS * wS)
    RULE[S] = dict(P=PS, L=LS, w=wS, Psi=PsiS, e=1 - 2 * abs(wS), t=2 * abs(wS), N=size * (6 - size) + size % 2)
classes = {}
for S, r_ in RULE.items():
    classes.setdefault((r_["P"], abs(r_["L"])), []).append(S)
okrule = all(abs(RULE[S]["Psi"] - RULE[S]["P"] / (RULE[S]["L"] ** 2 + 3 * RULE[S]["P"])) < 1e-12 for S in RULE)
chk("(67) the rule over the 64 divided sets: Psi counted on B, -Phi(4w_S)/(16 w_S^2), equals P/(L_S^2 + 3P) at every divided set; "
    "classes 32, 2, 10, 20 with Psi = 1/28, -1/22, -1/6, 1/2",
    okrule and sorted((k_, len(v_)) for k_, v_ in classes.items()) == [((-1, 1), 20), ((-1, 3), 10), ((-1, 5), 2), ((1, 5), 32)])
bit = dict(n=1, h=2, k=4, c1=8, c2=16, c3=32)
sup = lambda *names: sum(bit[x] for x in names)
S_t, S_tn, S_hn, S_F, S_C, S_ab, S_abn, S_empty = sup("h"), sup("h", "n"), sup("h", "n"), sup("h", "k"), sup("c1", "c2", "c3"), \
    sup("c1", "c2"), sup("c1", "c2", "n"), 0
R_ = lambda S: RULE[S]
okread = (abs(R_(S_t)["e"] - elf) < 1e-15 and abs(R_(S_tn)["e"] - ef) < 1e-15 and abs(R_(S_empty)["t"] - tf) < 1e-15
          and abs(R_(S_ab)["Psi"] - 1 / 28) < 1e-12 and abs(R_(S_abn)["Psi"] - 1 / 2) < 1e-12 and R_(S_F)["N"] == 8 and R_(S_C)["N"] == 10
          and abs(R_(S_t)["e"] ** 2 / R_(S_F)["N"] - 1 / 72) < 1e-15 and abs(R_(S_tn)["e"] ** 2 / R_(S_C)["N"] - ff) < 1e-15
          and abs(R_(S_hn)["e"] ** 2 / (EnF * El) - nuf) < 1e-15)
chk("(68)-(69) read at their divided sets: e@{t} = 1/3, e@{t,n} = 3/5, t@{} = 2/5 (the kernel's ratios at chi = -10); alpha_s^2 = e@{t}^2/N(F) = 1/72, "
    "f = e@{t,n}^2/N(C) = 9/250, nu = e@{h,n}^2/(E n_F E l); Psi at the two signs of the plane: Psi@{a,b} = 1/28, Psi@{a,b,n} = 1/2", okread)
# (b) the clock as its tilt varies: the marks (0, 1, 2, 3, 1/|Phi@{h,n}|)/4, the tilt nu varied; -log h/nu^2 tends to (3/2) Var D,
#     and the clock's spread is the excursion's: Var D = [(Var n_F - Var n_L)^2 + 4 Cov^2]/(3 E l)^2, E_D = (Var n_F + Var n_L)/(3 E l)
Phi_hn = -1 / (16 + 3 * R_(S_hn)["P"])
marks_r = [0, 1, 2, 3, 1 / abs(Phi_hn)]
gaps_r = [abs(p_ - q_) for p_, q_ in itertools.combinations(marks_r, 2)]
MQr = lambda s: sum(exp(-s * D / 4) for D in gaps_r) / len(gaps_r)
hsw = [(nn, -log((MQr(nn) * MQr(-nn)) ** (-1.5)) / nn ** 2) for nn in (0.05, 0.02, 0.01, float(nu))]
VarD = sum((D / 4 - sum(gaps_r) / 40) ** 2 for D in gaps_r) / 10
exc_var = ((VarnF - VarnL) ** 2 + 4 * Cov ** 2) / (3 * El) ** 2
exc_mean = (VarnF + VarnL) / (3 * El)
chk("(70) the clock as nu varies: -log h/nu^2 -> (3/2) Var D, Var D = 61/16 = [(Var n_F - Var n_L)^2 + 4Cov^2]/(3 E l)^2, E_D = 2 = (Var n_F + Var n_L)/(3 E l); "
    "h = %.11f" % ((MQr(float(nu)) * MQr(-float(nu))) ** (-1.5)),
    abs(hsw[-1][1] - 1.5 * VarD) < 1e-4 and abs(VarD - 61 / 16) < 1e-14 and abs(exc_var - 61 / 16) < 1e-12 and abs(exc_mean - 2) < 1e-12
    and abs((MQr(float(nu)) * MQr(-float(nu))) ** (-1.5) - hov) < 1e-15, ", ".join("nu = %g: %.6f" % x for x in hsw))
# (c) the proton's own terms, each a computation of the law: the three pairings' Gram, the zero under a weight on every step,
#     the signed exterior volumes of the reversal a on the vector states and on the seven sets that avoid h
Xp = [I16.astype(complex), -Psw.astype(complex), -Ep]
Gp = np.array([[np.trace(Xi @ Xj).real / 16 for Xj in Xp] for Xi in Xp])
detF0 = np.linalg.det(4 / 5 * Gp)
zs = [(tt, log(4 / max(abs(np.linalg.eigvals(tt * B))))) for tt in (0.3, 0.4, 0.6, 0.9)]
sgnL = {x: (1 if pc(x) <= 2 else -1) for x in rel}
B_L = [x for x in rel if pc(x) == 4]
B_hbar = [x for x in rel if x != 0 and not (x >> h0) & 1]
vol = lambda a_, xs: np.prod([a_ * sgnL[x] for x in xs])
dvol = lambda a_, xs: (vol(a_ + 1e-7, xs) - vol(a_ - 1e-7, xs)) / 2e-7
rp_rule = sum(trans_weight[s] for (_, _, s) in avail_tr) - log(detF0) / LOm + vol(af, B_L) + dvol(af, B_hbar) / El
chk("(71) the proton's terms: det F0 = %.12f = t@{}; a weight t on every step moves the zero by log(1/t) exactly; det(a sgnL) on the five vector "
    "states = -a^5, on the seven sets avoiding h = -a^7, whose first variation per mean return time is -(7/16)a^6 = -ba^6; m_p/m_e rebuilt = %.9f"
    % (detF0, rp_rule),
    abs(detF0 - R_(S_empty)["t"]) < 1e-12 and all(abs(lz - log(1 / tt)) < 1e-12 for tt, lz in zs) and len(B_L) == 5 and len(B_hbar) == 7
    and abs(vol(af, B_L) + af ** 5) < 1e-18 and abs(dvol(af, B_hbar) / El + bf * af ** 6) < 1e-12 and abs(rp_rule - rp) < 1e-9)
# (d) the neutron's exponent: the symmetric states stepping to symmetric states along the directions outside them are the Petersen graph; its nine contrasts
Fc = [x for x in rel if pc(x) == 2]
Apet = np.array([[1.0 if (y in [x ^ g[s] for s in range(d)]) else 0.0 for y in Fc] for x in Fc])
lam_pet = sorted(np.round(np.linalg.eigvalsh(3 * np.eye(10) - Apet), 9))
contr = sum(af ** (2 * lv) for lv in lam_pet if lv > 1e-9)
rn_rule = (1 / R_(S_empty)["t"]) ** (contr + 10 * cLf * bf * af ** 6)
chk("(72) the neutron: the step graph of the symmetric states is the Petersen graph, Laplacian 0, 2^5, 5^4; sum over its nine contrasts a^(2 Delta) = 5a^4 + 4a^10; "
    "m_n/m_p rebuilt = %.11f" % rn_rule,
    lam_pet == [0.0] + [2.0] * 5 + [5.0] * 4 and abs(contr - (5 * af ** 4 + 4 * af ** 10)) < 1e-18 and abs(rn_rule - rn) < 1e-13)
# (e) gravity's three excursions: one mean excursion on each of the three directions outside the plane hk, as the minor on C
W_rule = np.linalg.det(np.diag([R_(sup("h", "n"))["t"] ** El * etaf ** EHf] * len([1 for x in ("c1", "c2", "c3")])))
# (f) the level factors rebuilt from the rule's values: sqrt3 = e@{t}^(-1/2) per two-spinor state, Psi at the plane's two signs, the clock
level_rule = lambda n, Ls, P: exp(n / 2 * log(1 / R_(S_t)["e"]) - (R_(S_ab)["Psi"] if P == 1 else R_(S_abn)["Psi"]).real * Ls * (n - (1 + P) / 2) / 4
                                  + (log(MQr(P * nuf)) / LOm if n == 10 else (n - (1 + P) / 2) * P * nuf * (sum(gaps_r) / 40) / 4))
chk("(73) gravity W = det_C(t^El eta^E_H) and the level factors rebuilt from the rule: m_mu/m_e, m_tau/m_mu, p_q, q_q equal the main formulas'",
    abs(W_rule - W) < 1e-30 * 0 + 1e-12 * W and abs(level_rule(10, 2, 1) - rmu) < 1e-9 and abs(level_rule(5, -2, 1) - rtau) < 1e-11
    and abs(level_rule(10, 2, -1) - pq_p) < 1e-10 and abs(level_rule(5, -2, -1) - pq_q) < 1e-11)

sec("15. The rules read out of the law",
    "Every number the compositions read is a function of the law at a divided set. Computed over the 64 divided sets, the clock's tilt, the "
    "weight on a step and the reversal, the rules come out as follows.")
MD.append("| P | \\|L_S\\| | divided sets | Ψ_S | e_S | t_S |")
MD.append("|---|---|---|---|---|---|")
for (P_, aL), Ss in sorted(classes.items(), key=lambda kv: (-kv[0][0], -kv[0][1])):
    r0 = RULE[Ss[0]]
    MD.append(mn_("| %+d | %d | %d | %s | %s | %s |" % (P_, aL, len(Ss), Fr(r0["Psi"].real).limit_denominator(100), Fr(r0["e"]).limit_denominator(100),
                                                  Fr(r0["t"]).limit_denominator(100))).replace("|---", "|---"))
MD.append("")
eq("z_S = i^|S|,  P = z_S²,  L_S = (5 − k_S) + k_S P,  w_S = z_S/L_S:  Ψ_S = −Φ(4w_S)/(16w_S²) = P/(L_S² + 3P),  e_S = 1 − 2|w_S|,  t_S = 2|w_S|,  "
   "N(S) = |S|(6 − |S|) + [|S| odd]",
   "The one rule at every divided set. Ψ_S is the law's own signed first return, counted on B, read at the step of the divided set; "
   "the values depend on P and |L_S| alone: 1/28 at the 32 even divided sets, 1/2 at the 20 divided sets of colour, −1/6 at a single direction and its "
   "complement, −1/22 at the singleton {n} and at the set of the five directions; the empty set {} is even, with 1/28.")
eq("α_s² = e@{t}²/N(F) = (1/3)²/8 = 1/72,  f = e@{t,n}²/N(C) = (3/5)²/10 = 9/250,  ν = e@{h,n}²/(E n_F Eℓ) = 9/4000",
   "Two sources meet where their divided sets meet, each bringing the reflection of its divided set, over the channels of the two-source response.")
eq("Ψ@{a,b} = 1/28,  Ψ@{a,b,n} = 1/2,  √3 = e@{t}^(−1/2)",
   "The level rule's Ψ at the two signs of the plane and its factor per two-spinor state: values of the one rule.")
eq("marks (0, 1, 2, 3, 1/|Φ@{h,n}|)/4:  −log h/ν² → (3/2) Var D,  Var D = [(Var n_F − Var n_L)² + 4Cov²]/(3Eℓ)² = 61/16,  E_D = (Var n_F + Var n_L)/(3Eℓ) = 2",
   "The clock along its tilt: the four quarter steps and the long return 19 along h; what stays is the spread of the clock's gaps, which "
   "is the spread of one excursion's visits to the symmetric and the vector states over 3Eℓ = 48, and the exponent −3/2 = −k_C s@{h}.")
eq("m_p/m_e = Σ_transitions ⟨Ω, (L + γ_h ⊗ γ_s)Ω⟩ − log det F₀/L(Ω) + det(a sgnL)|_(B_L) + ∂_a det(a sgnL)|_(B_h̄)/Eℓ,  det F₀ = t@{} = 2/5",
   "The proton's own terms, each a computation: F₀ = (4/5)G, G the Gram of the three pairings 1, −P, −E; a weight t on every step moves the "
   "zero by log(1/t) exactly, for every t; the reversal's signed volume on the five vector states is −a⁵, on the seven sets avoiding "
   "h −a⁷, whose first variation per mean return time is −(7/16)a⁶ = −ba⁶.")
eq("m_n/m_p = (1/t@{})^(Σ_(contrasts) a^(2Δ_F) + 10c_L b a⁶),  Σ_(contrasts) a^(2Δ_F) = 5a⁴ + 4a¹⁰",
   "The neutron: the symmetric states stepping to symmetric states along the directions outside them form the Petersen graph, Laplacian 0, 2⁵, 5⁴; the reversal squared "
   "for each unit of it, over the nine contrasts.")
eq("W = det_C(t@{h,n}^Eℓ η^(E_H)) = (2/5)⁴⁸(295/296)⁹",
   "Gravity's amplitude, the transmission factor: one mean excursion on each of the three directions outside the plane hk, the minor on C.")

head = ["# The main line in formulas", "",
        "Every formula below is computed by [main_line_formulas.py](../programs/main_line_formulas.py) from the comparison L and the step B alone; "
        "%d of %d checks ([main_line_formulas.out](main_line_formulas.out)). "
        "Together the formulas give all 113 rows of the main line that the law computes, each agreeing with the table's value to a relative "
        "10⁻⁶ or within its printed digits; the experiments that hold each classical quantity are in [classical_experiments.py](../programs/classical_experiments.py). "
        "The unit is m_e = 0.51099895069 MeV, the conversions ħc and the parsec are the SI's, and the measurements are the table's "
        "([constants_and_measurements.md](../data/constants_and_measurements.md))." % (sum(ok), len(ok))]
with io.open(OUTMD, "w", encoding="utf-8", newline="\n") as fh:
    fh.write("\n".join(head + MD).rstrip("\n") + "\n\n## Reproduction\n\n    python -I programs/main_line_formulas.py > outputs/main_line_formulas.out\n")
print()
print("formulas: %d; rows: %d" % (NUM[0], len(ROWS)))
print("checks: %d of %d ok" % (sum(ok), len(ok)))
