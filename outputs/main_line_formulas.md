# The main line in formulas

Every formula below is computed by [main_line_formulas.py](../programs/main_line_formulas.py) from the comparison L and the step B alone; 29 of 29 checks ([main_line_formulas.out](main_line_formulas.out)). Together the formulas give all 113 rows of the main line that the law computes, each agreeing with the table's value to a relative 10⁻⁶ or within its printed digits; the experiments that hold each classical quantity are in [classical_experiments.py](../programs/classical_experiments.py). The unit is m_e = 0.51099895069 MeV, the conversions ħc and the parsec are the SI's, and the measurements are the table's ([constants_and_measurements.md](../data/constants_and_measurements.md)).

## 1. The comparison

Two distinctions compared. No physical name is given in this section.

**(1)**  γ_aγ_b + γ_bγ_a = 2δ_ab on ℂ⁴,  γ₁γ₂γ₃γ₄γ₅ = ±1

Four amplitudes and five Dirac matrices.

**(2)**  L = I⊗I + Σ_t γ_t⊗γ_t = 2(P + E),  spec L = 6¹ ⊕ 2¹⁰ ⊕ (−2)⁵

The comparison: P the exchange, E the singlet channel pairing each amplitude with its conjugate; one comparison tells the singlet (6), one of the ten symmetric states (2) or one of the five vector states (−2).

**(3)**  L(Ω) = ⟨Ω, LΩ⟩ = 6

Ω pairs every amplitude with its conjugate: the singlet.

**(4)**  within C(d, 2) + C(6 − d, 2) = 15, 10, 7, 6;  mixing d(6 − d) = 0, 5, 8, 9;  a central rotation within the sides only at 2¦4

The four types of distinction of the six directions; the rotations each keeps within its two sides and the rotations mixing them.

**(5)**  T₁ = iγ_h,  T₂ = γ_hγ_k,  T₃ = iγ_k:  H_kT₁H_k† = T₂,  H_k = (1 + iγ_k)/√2,  T_a² = −1,  T₁T₂ = T₃

The central rotation of the plane {n, h} and that of the plane hk, one quaternion triple with the change between them.

**(6)**  Y = |S ∩ F|/2 − |S ∩ C|/3,  Q = N_k − N_C/3:  ΣY = ΣY³ = 0

The sixteen two-spinor states seen from the plane hk (F = {h, k}): one generation; the five directions carry the charges (0, 1, −1/3, −1/3, −1/3).

**(7)**  Gram of the twelve rotations keeping 2 + 3, moved by h: (1/2, 1/2, 4/5) and nine zeros

Three moved, nine kept; M_W²/M_Z² = 5/8 and sin²θ = 3/8 at the source.

**(8)**  the null directions of the distinction of the plane hk: signature (1, 3), negative directions first

One time and three space.


## 2. One world line persists: the law

A world line's state is a two-spinor state and its last change; each step keeps the last change and never undoes it at once.

**(9)**  B:  (x, t) → (x △ g_s, s),  s ≠ t,  g_s the four Dirac matrices other than s

The step: 80 directed edges, 320 transitions.

**(10)**  det(I − uB) = (1 − u²)²⁴ u¹⁶ det[(6I − L) + χ(u)I],  χ(u) = 1/u + 4u − 5 = (1 − u)(1 − 4u)/u

The law is the comparison with one movable spectral parameter χ: T = HWᵀ, with the paired vectors (γ_S ⊗ 1)Ω and the characters W_xS = (1/4)(−1)^|x∩S|, is unitary and T†(6I − L)T = 5I − A.

**(11)**  k_N(u) = u(2N + χ(u)) = 1 + 4u² − u(5 − 2N):  det(I − uB) = (1 − u²)²⁴ k₀ k₂¹⁰ k₄⁵

The grade factors: the spectral parameter read through 6 − L = 0, 4, 8.

**(12)**  u = i^d/4:  χ = 0, −5 − 3i, −10, −5 + 3i

The breaking puts the spectral parameter at the singlet (the one zero), the direction h, the plane hk and colour.

**(13)**  k_N(−1/4) = (5 − N)/2 = 5/2, 3/2, 1/2:  t = 1/k₀ = 2/5,  e = k₂/k₀ = 3/5,  t_ℓ = 1/k₂ = 2/3,  e_ℓ = k₄/k₂ = 1/3

The transmission and the reflection, at the symmetric states and at a single direction: values of the one kernel at χ = −10.


## 3. The equations

Near the one zero, many steps summed: the law at each breaking is a classical field equation.

**(14)**  u = 1/4 − ε²m²/24:  χ = ε²m²/2 + O(ε⁴),  (1 + 4u²) − uA_ε = (ε²/8)(m² − Δ) + O(ε³)

Klein–Gordon in the long-wave limit: χ = ε²m²/2 + O(ε⁴); on the resolved two-sheet chart exactly ε²M_ε² = 2χ + χ²/5, so M_ε → m; the rest frequency tends to the mass, E = mc².

**(15)**  U = e^(−ikγ_j) e^(−iμγ_h):  U + U† = 2 cos k cos μ,  cos ω = cos μ cos k

Dirac's first-order step; c one step per step, ħ energy over phase per step.

**(16)**  G(k) = 1/[V₃(M² + L₃(k)/5)],  V₃ = 1/2;  the long-wave continuum response G_cont(r) = e^(−Mr)/(4πr)

Two sources held at rest on the law's own chart: 1/(4πr) at the zero, its coefficient 0.99304 to 0.99989 in four directions; Yukawa below it (programs/classical_experiments.py, F4).

**(17)**  log det(I − wA₋[e^(iθ)]) = log det(I − wA₋) − ½κ‖Cθ‖² + O(θ⁴),  w = 1/(χ + 5),  κ(χ) = 2/[(χ + 5)² − 5]²

Maxwell and Yang–Mills: the squared curvature around the square cells, unchanged by a gauge transformation; κ = 1/200 at the singlet and the plane hk, 1/98 at h and colour.

**(18)**  log 4u_c = ‖θ_cyc‖²/48 + O(θ⁴),  48 = 3Eℓ = 2(40 − 16)

A circulation carried around the cells moves the leading zero.

**(19)**  ε_abcd(𝓕^ab∧𝓕^cd − R^ab∧R^cd) = −(4/ℓ²)(R − 6/ℓ²) vol,  𝓕 = R − e∧e/ℓ²:  Λℓ² = 3

Einstein–Cartan with the constant term, in the epsilon contraction.

**(20)**  K_X(E, N) = K_X(E/N, 1)  ⟹  K_N = −(E/N) K_E,  dE_X/dN = E_X(N)/N (N > 0);  at N = 1 these are −E K_E and E_X(1)

A lapse on the clock that measures energy couples to the rest energy: the gravitational charge is the mass, the same share for every world line.


## 4. One first-return excursion

From leaving the singlet to coming back to it: the walk of one world line, counted on B.

**(21)**  F(z) = z⁴(1 + z)/(16 − 8z − 3z² − 3z³):  F(1) = 1,  Eℓ = F′(1) = 16,  Var ℓ = 156

Every excursion closes, after sixteen steps on average: the mean return time.

**(22)**  Φ(z) = −z⁴/(16 + 3z²):  Φ(±1) = −1/19,  Φ(±i) = −1/13

The same excursions with the Clifford sign of every loop.

**(23)**  E n_F = 10,  E n_L = 5,  Var n_F = 84,  Var n_L = 12,  Cov(n_F, n_L) = 30;  x(1 + x)/(16 − 11x − 3x²),  x_c = (√313 − 11)/6;  F(z; x, y) = z⁴x²y(1 + zy)/(16 − 8zy − 3z²xy − 3z³xy²),  F(1; x, 1) = x²/(4 − 3x):  K = n_L − 2,  G(x) = 1/(4 − 3x),  Pr(K = k) = (1/4)(3/4)^k,  E K = 3,  Var K = 12

The symmetric states and the vector states one excursion visits, their spreads, and the pole of its visits to the symmetric states. With x marking each arrival at a vector state and y each arrival at a symmetric state, every return has two compulsory vector arrivals; the arrivals K beyond them have G(x) = 1/(4 − 3x), whose cumulants are 3, 12, 84, 876.

**(24)**  74 directed edges,  M = 296 transitions,  C_h = 60 along h,  C_j = 59 along each other direction,  34 edges whose state does not contain h

The available transitions, uniform under the stationary measure on these edges (not the transitions of one excursion): c_L = C_h/M = 15/74, η = 5C_j/M = 295/296, σ = 5C_h/M = 75/74, R_ud = 34/74 = 17/37, E_H = Eℓ C_h/320 = 3 transitions along h per mean return time.

**(25)**  b = G₀₀ + G_ff − 2G₀f,  G = (5I − A)⁺ = (7I + A)/32 − 3J/128:  b = 7/16

The effective resistance between the singlet and a symmetric state at the critical step.

**(26)**  a = (1 − Φ(1))/8 = 5/38,  χ_A = 1/(1 + Φ(i)) = 13/12,  w_h = 1/(4χ_A) = 3/13,  χ_h = w_h(1 − w_h) = 30/169

The signed returns at the even and the odd points, the share of h and its spread.

**(27)**  J_DE/C_W = (|D||E| − 5 tr P_DP_E)/72 at regular χ, and by rational continuation:  g² = 1/72 = −Φ(1)/[4(1 + Φ(1))] = −Φ(i)/[6(1 + Φ(i))] = e_ℓ²/8

The response of two sets of directions against the clock that moves with it, as χ varies: 1/72 for a pair of directions on opposite sides, 1/18 for one direction against the other four, 1/12 for the plane hk against the three directions outside it; the walk's first returns and the comparison's response are one number.

**(28)**  ⟨Ω, (L + γ_h ⊗ γ_s)Ω⟩ = 6 + [s = h]

The weight of one transition: the moment compared with itself, once more along the world line's own time.

**(29)**  D_θ(u) = D(u) + (e^(−iθ) − 1) u D′(u)/320:  arg 4u_c = θ/320 + O(θ³) per step as θ → 0, its rate d arg 4u_c/dθ = 1/320 at θ = 0

One transition marked, exactly: every transition has the same cofactor. The phase on one directed edge: the unit rate.


## 5. The clock and the contact interaction

The world line's clock and the contact interaction of two sources, from the same excursion.

**(30)**  f = e²/N₂ = 9/250,  ν = f/Eℓ = 9/4000

Two sources leaving the plane hk meet on one of the ten symmetric states; per mean return time.

**(31)**  M_Q(s) = (1/10) Σ_D e^(−sD),  D the ten gaps of the marks (0, 1, 2, 3, −1/Φ(1))/4:  E_D = 2,  h = [M_Q(ν)M_Q(−ν)]^(−3/2) = 0.99997104933

The clock's five marks: a quarter step for each of the four directions other than h and the long return 19/4 along h; the Bhattacharyya overlap of its two tilted distributions.

**(32)**  N_h = Re Σ_(k≥1) h^k p_k,  p_k = −Φ(4(i/4)^k) for odd k,  F(4(i/4)^k) for even k:  N_h = 0.0770858406

The repeated return along h: the excursions as the steps of the law one level up.

**(33)**  x = νh/(M + 1 + N_h) = 7.573573 × 10⁻⁶

The contact interaction, closed once.

**(34)**  W_W = F(h) h⁻⁴ (1 − 2b + 2bh) = 0.9996273896

The weak contact interaction's retained excursion.


## 6. The four strengths

Two sources meet at the distinction where they meet; each brings what its divided set asks, over the channels where they can meet.

**(35)**  α_s = [e_ℓ²/(k_C² − 1)]^(1/2) = 72^(−1/2) = 0.117851130

Colour: each source its reflection at a single direction, over the eight traceless rotations, as an amplitude.  Rows: D01.

**(36)**  α = c_L f/(1 − x):  1/α = 137.035999177;  with h = 1:  137.035999147

The plane hk: the share of transitions along h, which give off no charge, times the two-source response at the plane, the contact closed once.  Rows: D02, L19.

**(37)**  G_F m_p² = (1 − 1/N₂) W_W/M²:  G_F = 1.16637886 × 10⁻⁵ GeV⁻²

The plane of h and the singlet direction: one particular transition of each excursion, on the nine symmetric states other than the photon's.  Rows: D03.

**(38)**  W = t^(3Eℓ) η^(3E_H) = (2/5)⁴⁸(295/296)⁹,  α_G = Gm_p²/ħc = W² = 5.906152 × 10⁻³⁹,  M_Pl = m_p/W = 1.22088981 × 10¹⁹ GeV

The singlet: each source its whole excursion on the three colour directions, three excursions of sixteen steps at the transmission, nine transitions along h at η; one channel.  Rows: D04, D05.


## 7. The rest poles

A world line at rest is a zero of its block; a mass is the zero's angle in the unit of the electron's phase on one directed edge.

**(39)**  the electron: arg 4u_c = θ/320 + O(θ³) per step as θ → 0, its rate d arg 4u_c/dθ = 1/320 at θ = 0

One directed edge meeting itself at weight one: the unit.

**(40)**  m_p/m_e = Σ_transitions ⟨Ω, (L + γ_h ⊗ γ_s)Ω⟩ + log k₀(−1/4)/L(Ω) − a⁵ − ba⁶ = 6M + C_h + (1/6) log(5/2) − a⁵ − (7/16)a⁶ = 1836.152673412;  m_p = 938.27208942 MeV

The proton: the self-interaction on the available transitions, the Gram-determinant term per unit of L(Ω), less the signed-volume terms on the five vector states and on the seven sets that avoid h.  Rows: J01, B12, M1.

**(41)**  m_n/m_p = k₀(−1/4)^(5a⁴ + 4a¹⁰ + 10c_L b a⁶) = 1.00137841956;  m_n = 939.565422025 MeV

The neutral pole spread over the ten symmetric states: the nine Petersen contrasts 5a⁴ + 4a¹⁰ and the opened seven-volume on the ten symmetric states.  Rows: B13, J02, B14, M2.

**(42)**  log ℒ(n, L*, P) = (n/2) log(1/e_ℓ) − (Ψ_P L*/4)(n − ε_P) + c_n(P),  Ψ₊ = 1/28,  Ψ₋ = 1/2,  ε_P = (1 + P)/2,  c₁₀(P) = (1/6) log M_Q(Pν),  c₅(P) = (5 − ε_P)Pν E_D/4

One rule for the symmetric and the vector states: √3 per opened two-spinor state, Ψ_P with the comparison L* on those states, and the clock, at the two signs P = ±1.

**(43)**  m_μ/m_e = ℒ(10, 2, +) = 3⁵ e^(−9/56) M_Q(ν)^(1/6) = 206.768283945,  m_τ/m_μ = ℒ(5, −2, +) = 3^(5/2) e^(1/14 + 2ν) = 16.8181606411

The charged leptons: the symmetric states opened, then the vector states; three families from the three pairings of the four directions other than h, U_h = (e_ab + e_cd, e_ac + e_bd, e_ad + e_bc)/√2 on the ten symmetric states, with 10U_hᵀΓ_P⁻¹U_h = 40I₃ − 4J₃, spectrum 28, 40, 40, Γ_P = (7I + 7J + A_P)/32 the inverse of 5I − A without the singlet, on the ten, and 28 = 1/Ψ@{a,b}; 3^(5/2) m_e with no rest pole; Koide 0.66666726.  Rows: B01, B02, L01, B03, L17, L04, L05.

**(44)**  p_q = ℒ(10, 2, −) = 19.961652,  q_q = ℒ(5, −2, −):  m_s/m_d = p_q,  m_b/m_s = q_q η = 53.921087,  (m_d, m_s, m_b) = 3^(3/2) m_e (1/η, p_q/η, p_q q_q)

The quarks: the same states at the odd sign; an open colour rest pole carries 1/η. At the Z pole d 2.6642, s 53.182, b 2867.65 MeV.  Rows: B04, B05, B06, B07, B08.

**(45)**  m_u/m_d = R_ud = 17/37,  κ = (e/t)^(Eℓ/E n_F) = (3/2)^(8/5) = 1.913137,  m_c/m_s = R_ud κ⁵

The up-type levels: the edges whose state does not contain h, and the reflection over transmission per visit to a symmetric state. u 1.2241, c 626.25 MeV.  Rows: B09, B10, B11.


## 8. The direction h

The direction h held at its length v in the plane hk: the rotations it moves, its radial direction, its own count.

**(46)**  v = (√2 G_F)^(−1/2) = 246.219634 GeV

The length of h.  Rows: D15.

**(47)**  s² = 3N_h = 0.2312575,  s²_OS = 3N_h/(1 + f) = 0.2232215;  with h = 1:  3N_h = 0.2312642;  the contact's angle 3 Σ_k p̄_k = 0.2315502

The weak angle: the repeated return along h once for each of the three directions outside the plane hk; on shell the plane's two-source response once more; p̄_k the even returns symmetrized.  Rows: D08, D10, L20, D09, D14.

**(48)**  M_W² = παv²/[(1 − f)s²_OS] :  M_W = 80.36625 GeV,  M_Z = M_W/(1 − s²_OS)^(1/2) = 91.18536 GeV

The rotations h moves.  Rows: D11, L15, D12, D13.

**(49)**  λ_H = πα/χ_h = 0.129146,  m_H = v(2λ_H)^(1/2) = 125.1348 GeV

The radial direction of h: the electric coupling over the spread of the share of h.  Rows: D16.

**(50)**  m_t = v(η/2σ)^(1/2) = 172.647 GeV;  m_p²/(E n_F m_e) = 172.28 GeV

The top: the available transitions along another direction over those along h, as an amplitude.  Rows: D17, S07.


## 9. Mixing and the neutral poles

Two closed world lines overlap; the neutral block of h feeds a heavy neutral pole.

**(51)**  s₁₂ = (Var n_F − Cov²/Var n_L)/(Eℓ · 5/2) = 9/40,  s₂₃ = 4/Tr L² = 1/24,  s₁₃ = s₁₂ t s₂₃ = 3/800,  δ_q = arg(b + i) = arg(7 + 16i):  V = R₂₃(s₂₃) R₁₃(s₁₃, δ_q) R₁₂(s₁₂)

The quark mixing: the spread of the visits to the symmetric states left when the visits to the vector states are known, per mean return time and per inverse transmission; four over Tr L²; the far one through the transmission; the phase the complex weight b + i. J_q = 3.1355 × 10⁻⁵, angles 90.71°, 22.95°, 66.34°.  Rows: C01, C02, C03, C04, C05, C06, C07, C08, C09, K05.

**(52)**  U = R₁₂(√(2b) s₁₂, π/2 − δ_q)† R₂₃(1/√2) R₁₂(√b)

The lepton mixing, the same frame from the other end: s²₁₂ = 0.30509, s²₁₃ = 0.022148, s²₂₃ = 0.48867, δ_l = 205.6°.  Rows: C10, C11, C12, C13, C14, T06.

**(53)**  M_R = M_Pl e_ℓ⁹ = M_Pl det(G⁻¹H) = M_Pl 3⁻⁹ = 6.20276285 × 10¹⁴ GeV,  M_off = M_Pl e_ℓ⁶ = M_Pl det_ℂ(G_off⁻¹H_off) = M_Pl 3⁻⁶ = 27M_R = 1.67474597 × 10¹⁶ GeV;  y = σ(v/m_p)(0, ρ_ν^(1/2), 1)/√2,  ρ_ν = tan²(π/8);  m_i = 2y_i² m_p/[X_R + (X_R² + 4y_i²)^(1/2)],  X_R = e_ℓ⁹/W

The heavy neutral pole: the algebra kept by the plane hk and the direction h, k = {diag(A, 0, −Tr A): A ∈ u(3)} on ℂ⁵ = C ⊕ ℂh ⊕ ℂk, of real dimension 3 + 2·C(3, 2) = 9, acts on the sixteen even states by ρ(X) = Σ X_ab c_a†c_b, which annihilates the singlet and never reaches it; the coherent comparison D_coh = |L|/L(Ω) = Π₀ + (I − Π₀)/3 therefore pulls back to H = G/3, G = [[8, 4, 4], [4, 8, 4], [4, 4, 8]] ⊕ 8I₆ in the three diagonal and six off-diagonal coordinates, one reflection at a single direction for each of the nine; on Hom_ℂ(F, C), of complex dimension six, G_off = 4I₆. The seesaw: m = 0, 8.613, 50.198 meV, three light channels.  Rows: E07, E01, E02, E03, E04, E05, E06, K02, K03, L03, T01, T02.


## 10. The nucleon

The three colour world lines close in the totally antisymmetric state, so their spin and isospin stand in the symmetric space; the nucleon is projected out of it before its currents are read.

**(54)**  P_N = P_sym(15/4 − S²)/3,  ⟨p↑| Σ_r σ_zτ_z |p↑⟩ = 5/3:  g_A = (5/3) t^(2b/3) = 1.275801

The axial coupling: the projected proton's axial current times the transmission to the power 2b/3; τ_n = 878.05 s with |V_ud| and G_F; the axial radius² (Var n_F − Cov²/Var n_L)λ_p².  Rows: S01, S05, S02, S03.

**(55)**  μ_p = [Var ℓ/(2N₂) · (1 − ε₂/(Eℓ²b))]^(1/2) = 2.7928473453,  μ_n = −[4(1 + E n_F)/23] (1 − ε₂/(Eℓ²b))^(1/2) = −1.9130430238,  ε₂ = α²/(1 + α/N₂)

The moments: the spread of the excursion's length over the twenty channels of the symmetric states, less the plane's own coupling once; the deuteron's from the two with its binding m_p χ_A^(1/2) a³[1 − (1 + t/Eℓ)ε₂].  Rows: G03, G04, G05, G13.

**(56)**  λ_p = ħ/m_pc = 0.2103089101 fm:  r_p = (Eℓ)^(1/2) λ_p = 4λ_p = 0.841236 fm,  r_π = (E n_F)^(1/2) λ_p = 0.66506 fm

The step is the proton's reduced Compton length; a size is the root of a count of the excursion.  Rows: G01, S04.

**(57)**  f_π = η m_p (2k_C)^(1/2)/(2πμ_p) = 130.529 MeV,  5m_p/36 = 130.316 MeV

The pion's decay constant, two constructions.  Rows: G08, G09, A002, A003.


## 11. Colour

Rotations within the sides with no centre and no clock of their own; colour always closes.

**(58)**  (1 + 4u²) − uA_U ⪰ (1 − u)(1 − 4u) for every unitary connection U, 0 ≤ u < 1/4;  with the reversal-paired positive sector sum:  θ̄ = 0

For 0 ≤ u < 1/4 the sector weights a_q are positive and, the closed weights being real, paired, a_q = a_−q; with a₁ > 0 the sector sum is maximal only at θ = 0 modulo 2π, and the mass determinant carries no phase: no strong phase.  Rows: K01, L16.

**(59)**  eight traceless rotations;  the one-loop scale M_Z e^(−2π/((23/3)α_s)) = 87.1 MeV

The colour term's components and its scale.  Rows: L14, S16.

**(60)**  χ_top/(F_π² m_π⁰²) = 1/(λ_low Σ_j S_j⁻¹) = 0.2129,  b₂ = −Σ_j S_j⁻³/[12(Σ_j S_j⁻¹)³] = −0.02806,  S = (R_ud, 1, p)

The light levels' lowest mode and third moment: the strong curvature and its fourth cumulant.  Rows: I08, I09.

**(61)**  τ/B(e⁺π⁰) = 72² ħ/(3²⁴ W⁴ m_p) = 1.170 × 10³⁷ yr

The proton's partial lifetime, through the six rotations that mix the three-plus-two split.  Rows: K06, L12.


## 12. The stationary state

The stationary weight on the states of the whole system.

**(62)**  C(j) = a¹¹ log G(e^j) = −a¹¹ log(4 − 3e^j):  η_B = C′(0) = a¹¹ E K = 3a¹¹ = 6.1400 × 10⁻¹⁰

Baryons per photon: the signed return on the eleven states of positive comparison value, one exterior volume a¹¹, carried by the vector arrivals K of one return beyond its two compulsory ones; the first derivative of their connected source.  Rows: F01.

**(63)**  n_s = 1 − t/Eℓ = 39/40,  dn_s/d ln k = 0;  A_s = C″(0)(0.05ℓ)^(−1/40) = a¹¹ Var K (0.05ℓ)^(−1/40) = 12a¹¹(0.05ℓ)^(−1/40):  ln(10¹⁰A_s) = 3.0613;  r = 16Λℓ_P²/(3π·12a¹¹)

The primordial spectrum, the second derivative of the same source, its tilt and its tensor share; a second construction b²⁴(0.05ℓ)^(−1/40).  Rows: C15, C16, L06, F03, S08, L11.

**(64)**  Λℓ_P² = 3W⁶τs³ = 2.8552 × 10⁻¹²²,  τ = 2π/(Eℓ m_p/m_e),  s = e/N₂ = 3/50;  ℓ = λ_p/[W²(τs³)^(1/2)] = 5369.08 Mpc,  k_BT = ħc/(2πℓ) = 1.8956 × 10⁻³⁴ eV,  S = 3π/(Λℓ_P²)

The constant term in the unit of the step: the angle τ, the electron's phase during 1/Eℓ of a proton Compton period, and one arrival at a symmetric state, each carried by the proton's three colour excursions; the de Sitter radius, temperature and entropy; w = −1.  Rows: D06, T03, T04, L10, L08.

**(65)**  N_eff = 3ησ^(4/3) = 3.0439,  Ω_k = 0,  M/(M − 4C_h) = 5.2857

The light species, the flat frame, the cold matter over the baryons by the available transitions.  Rows: F04, F13, L07, S09.

**(66)**  d log α/d(Φ/c²) = 0,  1 + γ = 2,  geodetic drift / Einstein = 1,  second-order bending 15π/4,  the two orders in coherent superposition tell commuting and anticommuting pairs apart with certainty

Gravitation's tests and the two orders: α the same at every location, light bent twice Newton's, the quantum switch.  Rows: D07, L09, H01, H02, L18, H03.


## 13. The classical equation with every number in front of every term

Γ = ∫d⁴x √−g [ (R − 2Λ)/16πG − Σ_X F_X²/16πα_X + ψ̄iγ^μD_μψ − (ψ̄_L𝒴φψ_R + h.c.) − (D_μφ)†D^μφ − λ_H(φ†φ − v²/2)² ]

| term | its number | formula |
|---|---|---|
| (R − 2Λ)/16πG | Gm_p²/ħc = 5.906152 × 10⁻³⁹; Λℓ² = 3, Λℓ_P² = 2.8552 × 10⁻¹²² | (19), (38), (64) |
| F²/16πα | 1/α = 137.035999177 | (36) |
| F²/16πα_s | α_s = 0.117851130 | (35) |
| the weak rotations | s² = 0.2312575, on shell 0.2232215 | (47) |
| ψ̄iγ^μD_μψ | cos ω = cos μ cos k; c one step per step | (14), (15) |
| lepton Yukawas | m_μ/m_e = 206.768284, m_τ/m_μ = 16.818161 | (43) |
| native quark roots | d 2.6642, s 53.182, b 2867.65, u 1.2241, c 626.25 MeV; t 170.950 GeV | (44), (45), (50) |
| quark mixing | 9/40, 1/24, 3/800, arg(7 + 16i) | (51) |
| lepton mixing | 0.30509, 0.022148, 0.48867, 205.6° | (52) |
| neutrinos | 0, 8.613, 50.198 meV | (53) |
| (D_μφ)†D^μφ − λ_H(φ†φ − v²/2)² | v = 246.219634 GeV, λ_H = 0.129146, m_H = 125.1348 GeV | (46), (49) |
| θ̄FF̃ | θ̄ = 0 | (58) |
| the scale | λ_p = 0.2103089101 fm, m_p/m_e = 1836.152673412 | (40), (56) |


## 14. Several world lines bound together

The hadrons beyond the nucleon and the nuclei use joint closed walks of several world lines: 56 scalar records appear in programs/classical_experiments.py, experiments E3, E5 and F. The article_results.py calculation evaluates twelve further literal composite expressions; their results and the remaining equations appear in docs/NUMBERS.md.


## 15. The rules read out of the law

Every number the compositions read is a function of the law at a divided set. Computed over the 64 divided sets, the clock's tilt, the weight on a step and the reversal, the rules come out as follows.

| P | \|L_S\| | divided sets | Ψ_S | e_S | t_S |
|---|---|---|---|---|---|
| +1 | 5 | 32 | 1/28 | 3/5 | 2/5 |
| −1 | 5 | 2 | −1/22 | 3/5 | 2/5 |
| −1 | 3 | 10 | −1/6 | 1/3 | 2/3 |
| −1 | 1 | 20 | 1/2 | −1 | 2 |

**(67)**  z_S = i^|S|,  P = z_S²,  L_S = (5 − k_S) + k_S P,  w_S = z_S/L_S:  Ψ_S = −Φ(4w_S)/(16w_S²) = P/(L_S² + 3P),  e_S = 1 − 2|w_S|,  t_S = 2|w_S|,  N(S) = |S|(6 − |S|) + [|S| odd]

The one rule at every divided set. Ψ_S is the law's own signed first return, counted on B, read at the step of the divided set; the values depend on P and |L_S| alone: 1/28 at the 32 even divided sets, 1/2 at the 20 divided sets of colour, −1/6 at a single direction and its complement, −1/22 at the singleton {n} and at the set of the five directions; the empty set {} is even, with 1/28.

**(68)**  α_s² = e@{t}²/N(F) = (1/3)²/8 = 1/72,  f = e@{t,n}²/N(C) = (3/5)²/10 = 9/250,  ν = e@{h,n}²/(E n_F Eℓ) = 9/4000

Two sources meet where their divided sets meet, each bringing the reflection of its divided set, over the channels of the two-source response.

**(69)**  Ψ@{a,b} = 1/28,  Ψ@{a,b,n} = 1/2,  √3 = e@{t}^(−1/2)

The level rule's Ψ at the two signs of the plane and its factor per two-spinor state: values of the one rule.

**(70)**  marks (0, 1, 2, 3, 1/|Φ@{h,n}|)/4:  −log h/ν² → (3/2) Var D,  Var D = [(Var n_F − Var n_L)² + 4Cov²]/(3Eℓ)² = 61/16,  E_D = (Var n_F + Var n_L)/(3Eℓ) = 2

The clock along its tilt: the four quarter steps and the long return 19 along h; what stays is the spread of the clock's gaps, which is the spread of one excursion's visits to the symmetric and the vector states over 3Eℓ = 48, and the exponent −3/2 = −k_C s@{h}.

**(71)**  m_p/m_e = Σ_transitions ⟨Ω, (L + γ_h ⊗ γ_s)Ω⟩ − log det F₀/L(Ω) + det(a sgnL)|_(B_L) + ∂_a det(a sgnL)|_(B_h̄)/Eℓ,  det F₀ = t@{} = 2/5

The proton's own terms, each a computation: F₀ = (4/5)G, G the Gram of the three pairings 1, −P, −E; a weight t on every step moves the zero by log(1/t) exactly, for every t; the reversal's signed volume on the five vector states is −a⁵, on the seven sets avoiding h −a⁷, whose first variation per mean return time is −(7/16)a⁶ = −ba⁶.

**(72)**  m_n/m_p = (1/t@{})^(Σ_(contrasts) a^(2Δ_F) + 10c_L b a⁶),  Σ_(contrasts) a^(2Δ_F) = 5a⁴ + 4a¹⁰

The neutron: the symmetric states stepping to symmetric states along the directions outside them form the Petersen graph, Laplacian 0, 2⁵, 5⁴; the reversal squared for each unit of it, over the nine contrasts.

**(73)**  W = det_C(t@{h,n}^Eℓ η^(E_H)) = (2/5)⁴⁸(295/296)⁹

Gravity's amplitude, the transmission factor: one mean excursion on each of the three directions outside the plane hk, the minor on C.

## Reproduction

    python -I programs/main_line_formulas.py > outputs/main_line_formulas.out
