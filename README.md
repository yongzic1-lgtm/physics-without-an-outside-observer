# Physics without an outside observer

This is the long-term repository of this work, by Yongzi CHEN. Its release 1.0 accompanies the article **Physics Without an Outside Observer: A Finite Geometry, Broken and Completed**. A world line compares its successive states through the same operator with which two systems compare each other. The comparison is

$$
L=I\otimes I+\sum_{t=1}^5\gamma_t\otimes\gamma_t,
\qquad \operatorname{spec}L=\{6^{(1)},2^{(10)},-2^{(5)}\}.
$$

The five possible changes join sixteen comparison states. A directed state records the comparison state and the last change. The step $B$ has eighty directed states and four continuations of each. Its law has one variable, the complex weight $u$ of one step:

$$
Z(u)=\det(I-uB)^{-1},\qquad
\det(I-uB)=(1-u^2)^{24}u^{16}
\det[(6I-L)+\chi(u)I],
\qquad \chi(u)=u^{-1}+4u-5.
$$

The divisions put this variable at $1/4,i/4,-1/4,-i/4$. The first return, the transport round a closed path, and the response to a source give the quantities used in the article. The programs construct the matrices, count the transitions and returns, and evaluate those quantities. The Lean development gives the mathematical statements and their proofs. The electron mass sets the laboratory mass unit.

## Start with the article

The final main text is [ARTICLE.pdf](docs/ARTICLE.pdf), with its exact source [ARTICLE.tex](docs/ARTICLE.tex). The organized Supplemental Material is [SUPPLEMENTAL.pdf](docs/SUPPLEMENTAL.pdf), with the complete REVTeX source [SUPPLEMENTAL.tex](docs/SUPPLEMENTAL.tex).

[ARTICLE_CONCORDANCE.md](docs/ARTICLE_CONCORDANCE.md) follows all 153 numbered displays and all 84 numerical addresses in the two main tables. Each entry gives its Supplemental section, its program and printed line, and its Lean theorem with the precise scope of the proof. [NUMBERS.md](docs/NUMBERS.md) also includes the 252 Supplemental records, including the original 214 comparison records, with formulas, calculated values, measurements, sources and deviations.

Read the Supplemental Material in this order:

1. **Derivations.** The five postulates and finite geometry, followed by the eight steps of the article.
2. **One variable and its physical quantities.** The readings and changes of $u$ that give the classical quantities.
3. **Attempts.** Conventional mass coordinates, thermal composition, and calculations of coupled world lines. Each assumed numerical factor has its source beside it.
4. **The full comparison table.** Formula, calculation, measurement, deviation, program, output and theorem.

The route through the repository is the same:

| Article | Calculation | Printed address |
|---|---|---|
| Postulates and finite geometry, equations 1–15 | `main_line_formulas.py`; `whole_picture.py`; `article_results.py` | main-line formulas 1–4; `AR eq:four-five`, `AR eq:spectrum`, `AR CHECK.crossing` |
| Step 1: one step, equations 16–21 | `main_line_formulas.py`; `article_results.py` | formulas 9–11; `AR eq:B`, `AR eq:polynomial.coefficients`, `AR CHECK.encounter.N0`, `N2`, `N4`, `product` |
| Step 2: two steps, equations 22–24 | `main_line_formulas.py`; `classical_experiments.py` | formulas 5 and 8; classical control F1, the common clock and null metric |
| Step 3: all directions, equations 25–32 | `main_line_formulas.py`; `whole_picture.py`; `article_results.py` | formula 1 and whole-picture Clifford checks; formulas 12–13, 21–27; `AR eq:division_values`, `AR eq:signed_first_return`, `AR eq:grade_amplitudes` |
| Step 4: the critical step, equations 33–44 | `classical_experiments.py`; `whole_picture.py` | classical controls F1–F10; whole-picture section 5, the long-wavelength and source calculations |
| Step 5: the plane, equations 45–55 | `main_line_formulas.py`; `article_results.py` | formulas 24–36; `AR eq:return_numbers` through `AR eq:alpha` |
| Step 6: the three outside directions, equations 56–58 | `main_line_formulas.py`; `article_results.py` | formulas 35, 58–59; `AR eq:strong`, `AR CHECK.instanton` |
| Step 7: the last direction, equations 59–71 | `main_line_formulas.py`; `article_results.py` | formulas 39–50; `AR eq:electron_mark` through `AR eq:higgs_top.masses` |
| Step 8: the whole system, equations 72–95 | `main_line_formulas.py`; `article_results.py` | gravity, neutral roots, mixing and populations; `AR eq:W` through `AR eq:epoch`, all `AR T2.*`, `AR CHECK.source.positive` |
| The action, equation 96 | `classical_experiments.py`; `article_results.py` | classical Part 3; `AR eq:weak_coefficients` and Table I coefficient addresses |

The detailed concordance gives the exact physical line numbers. The `AR` addresses stay attached to their quantities as the surrounding explanation grows.

## Run the programs

Use Python 3.12.14. The files in `outputs/` were produced with NumPy 2.3.5, SciPy 1.17.0 and the `rundec` 0.7 binding of CRunDec 3.1. Install them in a Python environment:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r programs/requirements.txt
export OPENBLAS_NUM_THREADS=1
```

From the repository root:

```sh
python -I programs/main_line_formulas.py > outputs/main_line_formulas.out
python -I programs/classical_experiments.py > outputs/classical_experiments.out
python -I programs/table_from_the_step.py > outputs/table_from_the_step.out
python -I programs/geometry_law_and_rows.py > outputs/geometry_law_and_rows.out
python -I programs/whole_picture.py > outputs/whole_picture.out
python -I programs/article_results.py > outputs/article_results.out
```

| Program | What it calculates and prints | Checks it passes |
|---|---|---:|
| `main_line_formulas.py` | The finite comparison and step, 73 formulas, 113 main-line catalogue rows. It also writes `outputs/main_line_formulas.md`. | 29/29 |
| `classical_experiments.py` | The response to a wavelength, source, link phase, circulation, frame curvature or clock; the associated experimental comparisons; the action coefficients. | 25/25 |
| `table_from_the_step.py` | The counts and return statistics on $B$, then the complete finite numerical catalogue. | 16/16 |
| `geometry_law_and_rows.py` | The geometric constructions, each primitive quantity and the numerical rows that use it. | 28/28 |
| `whole_picture.py` | Matrix checks from the Clifford relation through the field equations, masses, mixings and populations. | 73/73 |
| `article_results.py` | Local determinant polynomials with integer coefficients, the matrix crossing identity, the unit-instanton density, the permutation projector for mixing, positive source weights, the main article's numerical results and tables, explicit QCD transport, and all 73 main-line formulas. It also writes `outputs/article_results.json`. | 15/15 |

The first five programs use NumPy. The sixth reuses the finite objects calculated by `main_line_formulas.py`, then uses SciPy for the beta-function integral and CRunDec for mass transport. Its final line is

```text
AR SUMMARY | checks passed,total checks,table addresses,main-line formulas = [15, 15, 84, 73] [count]
```

`outputs/verification.json` gives each command, its exit status and its checks. Matrix diagnostic remainders depend on floating-point evaluation; the physical row values are printed separately. The long-wavelength momentum probe uses an explicit orthonormal frame so that its direction is fixed.

## Units, coordinates and comparisons

[INPUTS.md](docs/INPUTS.md) gives every dimensional input and reporting convention. The values are stored in `data/inputs.json`. The mass ratios, couplings, transition counts, first returns and population coefficients are calculated before measurement records are read for comparison.

Table II reports both native quark roots and conventional QCD coordinates. The sixth program uses the native roots as $\overline{\rm MS}$ coordinates at the calculated $M_Z$, runs with five flavours to the bottom threshold, matches to four flavours there, and evaluates the specified low-energy coordinates. The complete calls and the values are in [NUMBERS.md](docs/NUMBERS.md). The original conventional values remain in `data/conventional_records.json`; the program prints them beside the new explicit transport and their differences. For the top, the four-loop prescription printed in the Supplemental Material gives 172.802744094651 GeV; the article's conventional record is 172.76121248356 GeV.

The cold ratio is $R_c=a^{16}M_R/m_p$. Dividing by the recorded nucleosynthesis composition $\kappa_B=0.998785632760614$ gives the article's 5.34277169492503. The analytic hydrogen–helium composition uses $X_n=1-2b=1/8$ and gives $\kappa_B=0.998763869852295$, hence 5.3428881130836. Both operations are printed. The source and physical meaning of each composition input are in `INPUTS.md`.

The full catalogue contains finite calculations, continuum consequences, conventional calculation records, and equations for coupled systems. These are identified row by row. In particular, the neutron-rate normalization includes a measured Fermi constant, and the factor $5/36$ in two pion rows is an ansatz discussed in Supplemental Part III.

## Build the Lean development

The project pins Lean 4.35.0 and the original Mathlib revision in `lean/lean-toolchain`, `lean/lakefile.toml` and `lean/lake-manifest.json`. With Elan and Lake available, run from `lean/`:

```sh
python tools/check_sources.py
lake exe cache get
LEAN_NUM_THREADS=1 lake build Comparison.System
LEAN_NUM_THREADS=1 lake build
LEAN_NUM_THREADS=1 xargs lake build < verification/additional_roots.txt
lake env lean Comparison/System/Audit/Axioms.lean
```

[PROOFS.md](docs/PROOFS.md) gives the complete build and declaration checks, the imports that precede each theorem, and its statement. `lean/theorems.json` and `lean/modules.json` provide the same addresses as data.

## Files

| Path | Contents |
|---|---|
| `docs/ARTICLE.tex`, `docs/ARTICLE.pdf` | The final article, its source and PDF |
| `docs/SUPPLEMENTAL.tex`, `docs/SUPPLEMENTAL.pdf` | The organized Supplemental Material and its complete source |
| `programs/` | Six calculations and their Python dependency versions |
| `data/inputs.json` | Units, normalizations and conventional reporting coordinates |
| `data/constants_and_measurements.md` | The complete 214-row comparison catalogue |
| `data/rows_not_computed.md` | Conventional calculation records and equations for composite systems |
| `data/conventional_records.json` | The 43 conventional records as data |
| `data/supplemental_records.json` | The 252 Supplemental comparison and structural records |
| `data/article_table_records.json` | The values of the article's two tables and their measurement records |
| `outputs/` | Program output, the 73 formulas, numerical result records and the verification record |
| `docs/ARTICLE_CONCORDANCE.md` | Every article display and table address, in article order |
| `docs/NUMBERS.md` | Numerical formulas, values, comparisons, printed lines and theorem addresses |
| `docs/INPUTS.md` | Input values and sources; finite quantities and conventions |
| `docs/PROOFS.md` | Proof statements, scope and dependencies |
| `lean/` | The complete Lean development |
| `CITATION.cff` | How to cite this repository |
| `LICENSE`, `LICENSE-CC-BY-4.0.md` | MIT for the programs and the Lean development; CC BY 4.0 for the article, documents, data and outputs |

For a further calculation, place the source on the existing step, keep its full clock norm when eliminating other states, and state the response being measured. The return, matrix kernel and theorem immediately preceding that calculation are the starting point.

## Cite

Cite the article, Physics Without an Outside Observer: A Finite Geometry, Broken and Completed, by Yongzi CHEN, and this repository through `CITATION.cff`. The release that accompanies the article is 1.0, archived on Zenodo as [doi:10.5281/zenodo.23484200](https://doi.org/10.5281/zenodo.23484200); all versions are under [doi:10.5281/zenodo.23484199](https://doi.org/10.5281/zenodo.23484199).

## License

The programs and the Lean development are under the MIT License (`LICENSE`). The article, its Supplemental Material, the documents, the data and the outputs are under CC BY 4.0 (`LICENSE-CC-BY-4.0.md`).
