---
rg: 2
id: computable-group-factor-presentation-proof
kind: route
title: The canonical unitaries with computable group law give a computable presentation of L(U)
target: computable-groups-have-no-locally-universal-group-factor
requires:
  - locally-universal-tracial-vna-no-computable-presentation
---

**Presentation.**  Take special points `a_n = u_(g_n)`, the canonical unitaries
of the enumeration.  They generate the group algebra `C[U]`, which is
`||.||_2`-dense in `L(U)` (it contains the canonical basis of `l^2(U)` acting
on `delta_e`, and `L(U)` is the strong closure of `C[U]`; on a tracial von
Neumann algebra strong-operator density of a unital *-subalgebra gives
`||.||_2`-density by Kaplansky's density theorem).

**Algorithm.**  A rational point is a formal *-polynomial `p` with coefficients
in `Q(i)` in finitely many special points.
1. Expand `p` as a formal sum of monomials, each a finite word in the letters
   `u_(g_n)` and `u_(g_n)* = u_(g_n^(-1))`, with coefficients in `Q(i)`.
2. For each monomial compute the group element it represents, using computable
   multiplication and inversion.
3. Group the monomials by equality of these elements, using computable
   equality, obtaining `p = sum_(h in F) c_h u_h` with `F` finite and
   `c_h in Q(i)`.
4. Since `tau(u_h* u_h') = delta_(h,h')`, `||p||_2^2 = sum_(h in F) |c_h|^2`,
   a nonnegative rational number.
5. Compute a rational `q` with `|q - sqrt(||p||_2^2)| < 2^(-k)`, e.g. by
   bisection on rationals.

This is exactly the algorithm required by the definition pinned on
`locally-universal-tracial-vna-no-computable-presentation`, so the
presentation `(L(U), (u_(g_n)))` is computable.  By that theorem `L(U)` is not
locally universal.

For a finitely generated group with solvable word problem, enumerate reduced
words in a finite generating set and keep the first word representing each new
element; the word problem makes equality, hence the enumeration, multiplication
and inversion, computable.
