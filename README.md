# Refined BMV Conjecture

Research on the refined Bessis–Moussa–Villani (BMV) lower bound, focusing on the full (m=3) family in arbitrary finite matrix dimension, using positive-semidefinite kernel decompositions and computer-assisted interval certificates.

## Manuscripts and Lean development — 2026-11-27

- [Consolidated manuscript](manuscripts/refined_bmv_m3_m4_arxiv.pdf) and [TeX source](manuscripts/refined_bmv_m3_m4_arxiv.tex). They include the cubic family, the quartic cases with n in {1, 2, 3, 4, 5, 6, 8}, and an obstruction for odd-order polynomial certificates.
- [Quartic Gram certificate verifier](verify_m4_family_integer_gram.py). Run `python verify_m4_family_integer_gram.py` for exact symbolic checks and the included matrix experiments.
- [Lean project](lean/README.md) and [build and dependency audit](lean/verification.txt). The unconditional proofs cover the cubic cases with n from 1 to 6 and the seven quartic cases above. The larger cubic cases and the Duhamel lower bound depend on the stated scalar sign condition in Lean.
- [Cubic manuscript](manuscripts/refined_bmv_m3_arxiv.pdf), [earlier cubic and (4,4) manuscript](manuscripts/refined_bmv_m3_and_44_arxiv.pdf), and supplementary notes on [(3,3)](manuscripts/refined_bmv_33_all_d.tex) and [(n,3)](manuscripts/refined_bmv_n3_all_d.tex). The [exploratory scripts](experiments/) provide numerical checks.

## Uniform m = 3 interval certificate

The new uniform certification code targets all integers n >= 7 and the third-order Duhamel limit simultaneously, by studying a scalar mixed-derivative kernel on the continuous parameter domain:

- s > 0, v > 0, 0 <= epsilon <= 1/7, where epsilon = 1/n.
- The Python driver covers the small-argument region and analytic tails using interval arithmetic.
- The C++ verifier handles the compact three-dimensional region; the coefficient enclosures are supplied in cp_table.h.

Together with the earlier finite-order results for n = 1,...,6, this is a proposed computer-assisted route to the entire m = 3 family in all finite dimensions. The new certification and its analytic assumptions require independent verification; the consolidated manuscript above describes this update. No claim is made that the full refined BMV conjecture (arbitrary n and m) has been resolved.

## Files

| File | Purpose |
| --- | --- |
| [refined_bmv_complete_paper.pdf](refined_bmv_complete_paper.pdf) | Earlier manuscript: finite-order PSD kernels, logarithmic and Duhamel limits |
| [refined_bmv_complete_paper.tex](refined_bmv_complete_paper.tex) | Manuscript source |
| [certify_all_n_m3.py](certify_all_n_m3.py) | Uniform certification driver for n >= 7 and the infinite limit |
| [certify_region4.cpp](certify_region4.cpp) | Compact-domain 3D interval verifier |
| [cp_table.h](cp_table.h) | Coefficient interval table |
| [certify_duhamel_rho.py](certify_duhamel_rho.py) | Third-order Duhamel certification |
| [verify_all_d_346.py](verify_all_d_346.py) | Symbolic and numerical checks for (3,3), (4,3), (6,3) |
| [verify_bmv_33_proof.py](verify_bmv_33_proof.py) | Independent checks for (3,3) |

## Reproduction

Requires Python 3, SymPy, mpmath, NumPy, SciPy, and a C++ compiler (g++).

```sh
python -m pip install sympy mpmath numpy scipy
python verify_bmv_33_proof.py
python verify_all_d_346.py
python certify_duhamel_rho.py
python certify_all_n_m3.py
```

The last command compiles and runs the C++ verifier with directed-rounding flags. Its rigor depends on the validity of the analytic reductions, remainder bounds, interval arithmetic implementation, and platform-specific exp/sqrt error enclosures. Successful program output is not by itself a formal proof.

Reference: [Open Quantum Problems M14](https://openquantumproblems.com/p/M14).
