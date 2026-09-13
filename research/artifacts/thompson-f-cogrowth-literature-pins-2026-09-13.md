# Thompson F cogrowth: literature pins (2026-09-13)

Lane solve-thompson-f. Sources fetched as arXiv e-print sources on MSI
(`/scratch.global/sauer354/thompson-f-lit/`) and read from the TeX. Line numbers refer to
those TeX files.

## Haagerup–Haagerup–Ramirez-Solano, arXiv:1409.1486 (IJAC 25 (2015) 381–432)

`ThompsonF.tex`:
- l.112–119 (abstract): amenability of `F` is equivalent to `||I+A+B|| = 3` and to
  `||A+A^{-1}+B+B^{-1}|| = 4`. "By extensive numerical computations, we obtain precise lower bounds
  for the norms in (i) and (ii) ... Our computational results suggest, that ||I+A+B||≈ 2.95,
  ||A+A^{-1}+B+B^{-1}||≈ 3.87. It is however hard to obtain precise upper bounds for the norms,
  and our methods cannot be used to prove non-amenability of F."
- l.233–236: "||I+A+B||≥ 2.86759" and "||A+A^{-1}+B+B^{-1}||≥ 3.60613", from orthogonal
  polynomials applied to moment calculations (l.233).
- l.237: moments for `n <= 37` (Case 1) and `n <= 24` (Case 2).
- l.254: Elder, Rechnitzer and Wong computed the first 22 cogrowth coefficients for
  `{A, A^{-1}, B, B^{-1}}`.
- Table "The series of numbers for h=A+B+A^{-1}+B^{-1} (Case 2)": the column `m_n(h^*h)` is
  `c_{2n}`. Rows `n = 1..15` equal this repository's `out15.json` exactly, checked by
  `experiments/thompson-f/hhr_certify.py`.

Consequence for this graph: `thompson-f-random-walk-norm-certified-lower-bound` (`||P|| > 0.880541`)
is weaker than the published HHR bound (`||P|| >= 0.90153`). The exact re-derivation is
`thompson-f-norm-bound-from-hhr-exact-moments`.

## Elder–Rechnitzer–Janse van Rensburg, arXiv:1312.5722

`rand_dec20.tex` l.1499–1550 (Thompson's group section): estimated dominant singularities
"β_c = 0.395±0.005, 0.172±0.002 and 0.134±0.004" for three presentations, implying "cogrowths of
approximately 2.53±0.03, 5.81±0.07 and 7.4±0.2, all of which are well below the amenable values of
3,7 and 9". Then: "these estimates do not constitute a proof that Thompson's group is non-amenable."

## Elder–Rogers, arXiv:1608.06703

`ElderRogersSubDominant_nocomments.tex`:
- l.106–107: they analyse the ERR method and "identify two potential sources of error".
- l.298–301: HHR "Precise lower bounds of certain norms of elements in the group ring of F are
  computed, and coefficients of the first 48 terms of the cogrowth series are computed exactly."

## Guba survey, arXiv:2305.07113v4

`jgcc-template.tex` l.791: Kesten's criterion, `limsup P_n^{1/n} = 2m`, and Grigorchuk's criterion
for reduced words.

## What this lane did not do

- It did not recompute `c_{32}..c_{48}`. A job computing `c_{32}, c_{34}` independently (MSI
  707964) was cancelled once the HHR table was found, because it would only re-verify two
  published rows.
- It edited no amenability root. Both roots were edited within the previous 6 hours by
  another session.
