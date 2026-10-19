# Inputs and conventions

The finite calculation begins with the five Clifford matrices, the comparison $L$, and the step $B$. The programs form the sixteen comparison states and eighty directed states, then count the allowed transitions and first returns. The formulas below identify the quantities given as units or conventional coordinates.

## Geometry calculated by the programs

The first signed return gives $\Phi_s(1)=-1/19$. The clock marks are $(0,1,2,3,19)/4$, and their ten pairwise gaps give $M_Q(s)$ and $h_\nu$. The plane $F=\{h,k\}$ and its three complementary directions give the charges $(0,1,-1/3,-1/3,-1/3)$, with $Y=N_F/2-N_C/3$. The values $\Psi_+=1/28$ and $\Psi_-=1/2$ are read from $\Psi_S=p_S/(L_S^2+3p_S)$. `main_line_formulas.py` calculates these values over all sixty-four divided sets.

The quantities $296,60,59,34$, the ratios $15/74,295/296,75/74,17/37$, the resistance $7/16$, and the source coefficients 3 and 12 are calculated from the step. Their formulas and printed addresses are in [NUMBERS.md](NUMBERS.md).

## Symbols in the calculations

The reader notation follows the article and Supplemental Material:

| Symbol | Meaning |
|---|---|
| `m_d` | Down-quark mass |
| `m_deut` | Deuteron mass |
| `p_D` | Deuteron D-state probability |
| `P_D` | Projector onto the divided subspace D |
| `p_q`, `q_q` | The two coloured family-root factors |
| `rho_nu` | Neutral-root ratio parameter tan²(pi/8) |
| `H_comp`, `t_age` | Expansion rate and age at the stated comparison surface |
| `lambda_10^log`, `lambda_5^log` | Logarithmic increments on the ten- and five-dimensional comparison blocks |
| `ell` | Curvature length |

The Python identifiers use the local ASCII names stated beside their definitions. The proof concordance retains each Lean declaration’s exact identifier and statement.

## Declared numerical inputs

Every entry below is stored with its meaning and source in [inputs.json](../data/inputs.json). The five finite programs use the same values that accompanied the article.

| Entry | Value | Meaning and source |
|---|---:|---|
| Electron rest energy | 0.51099895069 MeV | Mass unit, CODATA 2022 electron rest energy quoted in the article |
| Planck constant $h$ | $6.62607015\times10^{-34}$ J s | Exact SI definition |
| Speed of light $c$ | 299792458 m/s | Exact SI definition |
| MeV to joules | $1.602176634\times10^{-13}$ J/MeV | Exact SI elementary-charge definition |
| Megaparsec | $3.0856775814913673\times10^{22}$ m | Parsec convention used in the article |
| Julian year | 365.25 days | Unit conversion |
| Scalar-spectrum pivot $k_*$ | 0.05 Mpc$^{-1}$ | P–ACT reporting coordinate in the article |
| Neutron-rate normalization | 5099.33 s | Conventional rate normalization, including the measured Fermi constant, in Supplemental Part III |
| Neutron-rate factor | 1.03983 | Conventional correction in the same rate formula |
| Network composition $\kappa_B$ | 0.998785632760614 | Recorded mass per counted baryon in proton units, used for the article's thermal-composition calculation |
| Hydrogen binding | 13.5984345996929 eV | Recorded atomic calculation I11, used to form the neutral hydrogen mass |
| Helium-4 atomic rest energy | 3.72839931079 GeV | Atomic mass quoted in the Supplemental composition equation |
| Light-quark reporting scale | 2 GeV | Table II $\overline{\rm MS}$ coordinate |
| Alternate $M_Z$ coordinate, S017 | 91.1876 GeV | Reporting scale for the four-loop $\Lambda_5$ integral |
| Alternate $M_Z$ coordinate, S018 | 91.188 GeV | Second reporting scale for the same integral |

The neutron lifetime is calculated as

$$
\tau_n=\frac{5099.33\ {\rm s}}{1.03983|V_{ud}|^2(1+3g_A^2)}.
$$

Its $g_A$ and $V_{ud}$ come from the finite calculation. Its normalization is a measured conventional input. The electron unit and the SI conversions also enter the reported lengths, masses and lifetimes.

## Mass transport

`article_results.py` evaluates a stated QCD coordinate prescription using [CRunDec 3.1](https://www.ttp.kit.edu/Progdata/ttp17/ttp17-011/) through the [rundec 0.7 Python binding](https://github.com/DavidMStraub/rundec-python). The perturbative conventions are described in [arXiv:1703.03751](https://arxiv.org/abs/1703.03751).

The starting coupling is the finite value $\alpha_s(M_Z)=1/\sqrt{72}$, at the calculated $M_Z$. Native quark roots are treated as $\overline{\rm MS}$ masses at that scale. Five-flavour running determines $\overline m_b(\overline m_b)$. Coupling and light-quark masses are matched to four flavours at that scale. The up, down and strange masses are evaluated at 2 GeV; the charm is evaluated at its own running mass. Four-loop running and matching are used throughout.

The top calculation follows the explicit Supplemental prescription: five-flavour running to $\overline m_t(\overline m_t)$, followed by the pole conversion with five massless light flavours. CRunDec expresses the latter by `nf=6` in `mMS2mOS`. The program prints orders one through four and every input coordinate. The result table in [NUMBERS.md](NUMBERS.md) gives the explicit transport beside each article record.

The finite four-loop beta-function integral is also evaluated directly, with $a=\alpha_s/(4\pi)$, and with the coefficients $\beta_0=23/3$, $\beta_1=116/3$, $\beta_2=9769/54$ and $\beta_3=-598391/1458+(352864/81)\zeta(3)$. It gives $\Lambda_5$ in each of the three stated reporting coordinates.

## Thermal composition

The finite calculation gives the cold mass per counted baryon,

$$
R_c=a^{16}M_R/m_p=5.33628360801120.
$$

For the analytic composition, $X_n=1-2b=1/8$, $M_H=m_p+m_e-B_H$, and

$$
\kappa_B=(1-2X_n)\frac{M_H}{m_p}
 +\frac{X_n}{2}\frac{M_{\rm He}}{m_p}.
$$

The program prints this composition and the recorded network composition separately. Dividing $R_c$ by the network entry gives the article's cold-to-baryon density ratio. Generating the network composition itself requires its abundance calculation. That generating network is not part of this repository; its numerical record and its role in the density conversion are explicit here.

## Comparison records and further calculations

[constants_and_measurements.md](../data/constants_and_measurements.md) contains the 214 comparison records and their cited sources. The comparison data are read after the finite values have been calculated. The main article has its own measurement records in [article_table_records.json](../data/article_table_records.json); this includes the CODATA $G_F$ record used for both $G_F$ and $v$.

Supplemental D15 uses the Supplemental comparison $v=246.219650794\pm0.0000633293$ GeV, transcribed in [supplemental_records.json](../data/supplemental_records.json). Table I uses its separately rounded comparison $246.2196508\pm0.0000633$ GeV. The original 214-record catalogue and the first five outputs retain their older PDG comparison $246.21964024\pm0.0000633$ GeV. Each deviation is calculated with the centre and width of its stated comparison.

The 43 conventional records include QCD coordinates, atomic and radiative calculations, thermal history, nucleosynthesis, and acoustic transport. The program now calculates the explicit QCD prescription, the four-loop scale integral and the conversion $R_c/\kappa_B$. The other conventional values retain their recorded provenance in [conventional_records.json](../data/conventional_records.json). The original 38 composite records specify equations for several coupled world lines. The sixth program evaluates twelve of their literal expressions; the other 26 retain their analytic expressions. The additional Q12 record gives the conversion of the complete muon anomaly to the measured frequency ratio, including proton shielding.

The continuum field equation supplies the bending and drift factors H01, H02 and L18. The constant equation of state, spatial curvature, index running and electric drift follow from the stated continuum form. The pion factor $5/36$ in A002 and A003 is a numerical ansatz; its choice and the other factors selected with measurements in view are discussed in Supplemental Part III.
