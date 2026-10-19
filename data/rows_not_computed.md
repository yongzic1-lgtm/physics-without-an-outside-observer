# Conventional coordinates and composite systems

This catalogue supplies the 42 conventional records and 38 composite expressions read by `classical_experiments.py`. The values retain their stated calculation and measurement conventions. The complete Supplemental ledger in `outputs/article_results.json` also contains the muon-frequency record Q12, the explicit QCD transport, and the twelve composite expressions now evaluated by `article_results.py`.

### Classical maps of the computed numbers (42 rows)

Each record states the running, transport or solver convention used to carry a finite result into an experimental coordinate. The values below are the recorded calculations. `article_results.py` prints the newly specified QCD and composition calculations beside these records. The last column is the recorded difference from measurement in standard deviations.

| row | constant | the term and its map | value | standard deviations |
|---|---|---|---:|---:|
| A001 | induced pseudoscalar coupling at Q^2=0.88 m_mu^2 | the whole axial shape w/(4 − 3w) with its Ward partner at Q² = 0.88 m_μ² | 8.36259039416189 | -1.002 |
| F02 | cold/baryon omega_c/omega_b | stationary: stationary weight on all sixteen states with the heavy pole: a¹⁶M_R/m_p, then C[κ_B] (the epoch with the nucleosynthesis network's κ_B) | 5.34277169492503 | -0.333 |
| F05 | photon temperature at the 24:11 epoch | stationary: the present, ρ_Λ/ρ_m = 24/11, then C[thermal history: T] (the epoch with the nucleosynthesis network's κ_B) | 2.72549728670312 | +0.030 |
| F06 | Hubble rate H_comp | stationary: the present, 24/11, then C[thermal history: H_comp] (the epoch with the nucleosynthesis network's κ_B) | 67.4316192077386 | -0.377 |
| F07 | age t_age | stationary: the present, 24/11, then C[thermal history: t_age] (the epoch with the nucleosynthesis network's κ_B) | 13.7944222597347 | +0.301 |
| F08 | matter share Omega_m | stationary: the present, 24/11, then C[thermal history: Ω_m] (the epoch with the nucleosynthesis network's κ_B) | 0.314264682713255 | +0.375 |
| F09 | the Λ share Omega_Lambda | stationary: the present, 24/11, then C[thermal history: Ω_Λ] (the epoch with the nucleosynthesis network's κ_B) | 0.685668398647101 | +0.133 |
| F10 | helium mass fraction Y_p | stationary: the nucleosynthesis network on the computed coefficients, Y_p = 4y/(1 + 4y) in the measurements' convention | 0.24694744653623 | +0.883 |
| F11 | baryon density omega_b | stationary: the present, 24/11, then C[thermal history: ω_b] (the epoch with the nucleosynthesis network's κ_B) | 0.0224294823835265 | -0.641 |
| F12 | cold density omega_c | stationary: the present, 24/11, then C[thermal history: ω_c] (the epoch with the nucleosynthesis network's κ_B) | 0.119835603610525 | +0.446 |
| I01 | up mass m_u(2 GeV) | pole: C[four-loop running and matching to 2 GeV] of the up pole at M_Z (the open levels carry 1/η) | 2.11478 | -1.13 |
| I02 | down mass m_d(2 GeV) | pole: C[four-loop running and matching to 2 GeV] of the down pole at M_Z (the open levels carry 1/η) | 4.60275 | -2.43 |
| I03 | strange mass m_s(2 GeV) | pole: C[four-loop running and matching to 2 GeV] of the strange pole at M_Z (the open levels carry 1/η) | 91.8786 | -2.55 |
| I04 | charm mass m_c(m_c) | pole: C[four-loop running and matching to m_c] of the charm pole at M_Z (the open levels carry 1/η) | 1.26243 | -3.88 |
| I05 | bottom mass m_b(m_b) | pole: C[four-loop running and matching to m_b] of the bottom pole at M_Z | 4.18248214152943 | -1.005 |
| I06 | strong coupling at the proton | coefficient: C[four-loop running to m_p] of the colour two-source coefficient α_s | 0.505523057661309 | -0.176 |
| I07 | top pole mass | pole: C[four-loop matching to the pole mass] of the top pole at M_Z | 172.76121248356 | +1.102 |
| I10 | electron anomaly a_e | residue: C[the electron vertex to five loops] of the residue α and the charged poles; with the computed hadronic share | 0.00115965218050222 | -0.675 |
| I11 | hydrogen binding | residue: C[the hydrogen series] of the residue α and the pole m_p/m_e; with the computed hadronic term; compared at the spectral lines | 13.5984345996929 |  |
| L21 | clock-independent lower bound on the light neutral mass sum | pole: sum of the light poles at the clock endpoint h = 1 | 0.0587890893281977 |  |
| Q01 | electric running 1/alpha(M_Z) | C[dispersion] of the computed vector current | 128.937243 | -0.197 |
| Q04 | muon hadronic polarization | the computed vector current's leading polarization of the muon | 711.1437 | -0.337 |
| Q05 | acoustic angle 100 theta_* (common-area convention) | stationary: C[CAMB transfer, common-area convention] of the populations at the present | 1.04094999030065 | +0.040 |
| Q06 | acoustic angle at optical depth one 100 theta | C[CAMB transport with the nucleosynthesis network's helium] of the populations | 1.04098061206 | +0.162 |
| Q07 | acoustic angle at visibility peak 100 theta | C[CAMB transport with the nucleosynthesis network's helium] of the populations | 1.041686318178 | +0.332 |
| Q08 | matter fluctuation sigma_8 | C[CAMB transport with the nucleosynthesis network's helium] of the populations | 0.8213353983338 | +1.021 |
| Q09 | S_8 | σ₈(Ω_m/0.3)^(1/2) of the carried σ₈ | 0.840635453047808 | +0.760 |
| Q10 | drag ruler r_d | C[CAMB transport with the nucleosynthesis network's helium] of the populations | 147.0826558961 | -0.198 |
| Q11 | proton decay matrix element | pole: C[continuous four-loop operator transport, computed bottom threshold] of the poles m_p and m_π0 | 0.134483885087514 | +0.256 |
| S017 | five-flavour scale at the reporting M_Z = 91.1876 GeV | coefficient: C[the four-loop length at M_Z = 91.1876 GeV] of α_s | 206.895282667594 |  |
| S018 | Lambda_5, four-loop convention at M_Z = 91.188 GeV | coefficient: C[the four-loop length at M_Z = 91.188 GeV] of α_s | 206.896190226441 |  |
| S06 | muonic-hydrogen singlet capture | the whole axial shape w/(4 − 3w) with its Ward partner, through C[the capture map] | 717.110240723118 | +0.204 |
| S10 | coloured/lepton Cd | pole: C[the coloured/lepton statistic] of the down pole (the open levels carry 1/η) | 10.4618 | -1.30 |
| S11 | coloured/lepton Cs | pole: C[the coloured/lepton statistic] of the strange pole (the open levels carry 1/η) | 10.4697 | -1.25 |
| S12 | coloured/lepton Cb | pole: C[the coloured/lepton statistic] of the bottom pole | 10.3757734611098 | -0.211 |
| S14 | five-flavour four-loop scale | coefficient: C[the four-loop length at the constructed M_Z] of α_s | 206.890203783025 |  |
| S15 | pion electronic/muonic decay ratio | residue: C[inclusive point-pseudoscalar QED through O(α)] of the charged poles m_e, m_μ, m_π± | 0.000123292613490236 | +0.098 |
| T08 | running top and Yukawa | pole: C[running to m_t(m_t), y_t = √2 m_t/v] of the top pole | [162.984094960692, 0.936132971038294] |  |
| T09 | alpha_s at bottom and charm thresholds | coefficient: C[running to m_b and m_c] of α_s | [0.224009369316102, 0.385356820505129] |  |
| T10 | coloured/lepton C_d | pole: C[the coloured/lepton statistic] of the down pole (the open levels carry 1/η) | 10.4618 |  |
| T11 | coloured/lepton C_s | pole: C[the coloured/lepton statistic] of the strange pole (the open levels carry 1/η) | 10.4697 |  |
| T12 | coloured/lepton C_b | pole: C[the coloured/lepton statistic] of the bottom pole | 10.3757734611098 |  |

### Composites of several world lines (38 rows)

These rows specify hadron, deuteron and nuclear-matter calculations on several coupled world lines. The sixth program evaluates twelve literal light-flavour and vector expressions. The remaining entries specify the retained response or source to calculate.

| row | constant | the term | value | standard deviations |
|---|---|---|---:|---:|
| G14 | deuteron asymptotic S normalization A_S | residue: the S normalization of the two-nucleon pole's residue, the two-nucleon kernel | not computed |  |
| G15 | deuteron D/S ratio eta | eigenvector: the D/S direction of the two-nucleon pole's residue | not computed |  |
| G16 | deuteron effective range at the pole rho_d | residue: 1/γ − 2/N_p² of the two-nucleon pole | not computed |  |
| G17 | triplet scattering length a_t | the two-nucleon kernel at zero energy | not computed |  |
| G18 | triplet effective range r_t | the two-nucleon kernel at zero energy | not computed |  |
| G19 | deuteron point matter radius r_m | residue: (1/2)⟨r²⟩^(1/2) of the two-nucleon pole's wave | not computed |  |
| G20 | deuteron quadrupole moment, impulse part Q_d | residue: (1/20)∫r²w(√8u − w) of the two-nucleon pole | not computed |  |
| G21 | deuteron electric polarizability alpha_E | the two-nucleon pole's E1 response with the free P and F waves | not computed |  |
| G19a | deuteron structure radius r_str (the 1S–2S number) | residue: √(r_m² + the two-body and spin–orbit monopoles) of the two-nucleon pole | not computed |  |
| J10 | π⁰ by its world lines (MeV) | √[(P(S_u,S_u)² + P(S_d,S_d)²)/2] | not computed |  |
| J11 | η (MeV) | P(S_d,S_d); no join term | not computed |  |
| J12 | η′ (MeV) | P(S_s,S_s); no join term | not computed |  |
| J13 | D (mean) (MeV) | P(S_c,(S_u + S_d)/2) | not computed |  |
| J14 | D_s (MeV) | P(S_c,S_s) | not computed |  |
| J15 | B (mean) (MeV) | P(S_b,(S_u + S_d)/2) | not computed |  |
| J16 | B_s (MeV) | P(S_b,S_s) | not computed |  |
| J19 | ω (MeV) | √s_ρ; no shift | not computed |  |
| J20 | K*± (MeV) | √(s_ρ + m_K±²) | not computed |  |
| J21 | K*⁰ (MeV) | √(s_ρ + m_K0²) | not computed |  |
| J22 | φ (MeV) | √[s_ρ + P(S_s,S_s)²] | not computed |  |
| J23 | J/ψ (MeV) | open: the c c̄ source is not yet constructed | not computed |  |
| J24 | Υ(1S) (MeV) | open: the b b̄ source is not yet constructed | not computed |  |
| J25 | Σ⁺ (MeV) | open: the charge assignment is not yet constructed | not computed |  |
| J26 | Σ⁰ (MeV) | m_n(5/2)^(59/320) | not computed |  |
| J27 | Σ⁻ (MeV) | open: the charge assignment is not yet constructed | not computed |  |
| J28 | Ξ⁰ (MeV) | m_n(5/2)^(118/320) | not computed |  |
| J29 | Ξ⁻ (MeV) | open: the charge assignment is not yet constructed | not computed |  |
| J30 | Σ* (mean) (MeV) | 3bm_p(5/2)^(20/320) | not computed |  |
| J31 | Ξ* (mean) (MeV) | 3bm_p(5/2)^(40/320) | not computed |  |
| J32 | Ω⁻ (MeV) | 3bm_p(5/2)^(60/320) | not computed |  |
| J33 | Λ_c (MeV) | open: the c source is not yet constructed | not computed |  |
| J34 | Λ_b (MeV) | open: the b source is not yet constructed | not computed |  |
| N23 | incompressibility K_0 | C[one two-source response with both Pauli blockings at the saturation point]: 9n₀²e″(n₀), the scalar and vector strengths carrying R_σ(n)²(1 − f(n)) | not computed |  |
| N24 | symmetry energy J | coefficient: the kinetic part, the isospin-charge two-source response C_τn/2, the T = 0 iterated pion of neutron matter carried by the response's m*, and the one-pion Fock term, at n₀ | not computed |  |
| N25 | symmetry slope L | 3n₀S₂′(n₀) of the same | not computed |  |
| S19 | nucleon scalar residue sigma_piN | residue: the scalar insertion at the nucleon pole: its π, K, η₈ and Δ cloud, Σ_φ (m̂∂M_φ²/∂m̂)∂Σ_φ/∂M_φ² = 45.315 MeV, and its core, the levels of the three light world lines at one depth, 3Z_l m̂(1 + 2A/u), with the light world line's depth Z_l = 1.678 from its share λ = m_p/3 moving around a world line at rest | not computed |  |
| S20 | nucleon strange scalar residue sigma_s | residue: the strange scalar insertion at the nucleon pole through its K and η₈ cloud | not computed |  |
| S21 | B_c* minus B_c | pole difference: the colour kernel's contact with one mass for the motion and the spin, the rest energy | not computed |  |
