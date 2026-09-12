---
rg: 2
id: kt-coset-bernoulli-essentially-free-proof
kind: route
title: Grade by the SL_d(Z) quotient, spread monomial supports, and shear constant matrices
target: kt-coset-bernoulli-essentially-free
requires: []
---

Write `G = E rtimes S` with `S = SL_d(Z)` acting on `R` by invertible monomial
substitutions, so `s e s^(-1)` is entrywise substitution and a substitution
maps the monomial basis of `R` bijectively to itself (no cancellation:
`Supp(s.f) = s.Supp(f)` for a linear action of `S` on `Z^d`).  A coset `h Gamma`
is fixed by `g` iff `h^(-1) g h in Gamma`.  Note `Gamma <= E`, `Gamma` has
entries in `R_+`, and `Gamma cap S = 1`.

**(1) `g notin E`.**  The quotient `G -> S` kills `E` and is nontrivial on `g`;
every conjugate `h^(-1) g h` has nontrivial image, so it is not in `E`, hence not
in `Gamma`.  No fixed coset.

**(2a) `g in E` with a non-constant entry.**  Some entry has a monomial `x^v`,
`v != 0`.  Use the cosets `s Gamma`, `s in S`, which are pairwise distinct since
`Gamma cap S = 1`.  Here `s^(-1) g s = s^(-1).g` has support `s^(-1).Supp`.  For
`d >= 2`, `S` is transitive on primitive vectors, so the orbit of `v = c v_0`
contains `c(-1,m,0,...,0)` for every `m in Z`.  Choosing `s_m` with
`s_m^(-1) v = c(-1,m,0,...)` gives infinitely many distinct cosets `s_m Gamma`,
each with `s_m^(-1).g` having a negative exponent in some entry, so not in
`M_r(R_+) >= Gamma`.  Infinitely many moved cosets.

**(2b) `g in E` constant but not scalar.**  Then `g in SL_r(F_q)`, and a matrix
commuting with every `E_ij` (`i != j`) is scalar, so `C = g E_ij - E_ij g != 0`
for some `i != j`, with a nonzero entry `c in F_q`.  For `a_n = x_1^(-n)` and
the elementary `e_n = I + a_n E_ij in E`,

```text
e_n^(-1) g e_n = g + a_n C - a_n^2 g_ji E_ij.
```

The `x_1^(-n)` coefficient of that entry is `c != 0`, since `n >= 1` separates
`1`, `x_1^(-n)` and `x_1^(-2n)`.  So `e_n^(-1) g e_n notin Gamma` and `g` moves
`e_n Gamma`.  The cosets are distinct:
`e_n^(-1) e_m = I + (x_1^(-m) - x_1^(-n)) E_ij notin M_r(R_+)` for `m != n`.

**(3) scalars.**  `lambda I` with `lambda^r = 1` lies in
`SL_r(F_q) = EL_r(F_q) <= Gamma`.  It is central in `GL_r(R)` and fixed by
every substitution, so it is central in `G`, lies in every conjugate of
`Gamma`, and fixes every coset.  Cases (1)--(3) give `core_G(Gamma) = Z_q`,
and `F_q^x` cyclic of order `q-1` gives `|Z_q| = gcd(r,q-1)`.

**(4) measure.**  If `g` moves infinitely many points of `I`, then `Fix_X(g)`
(configurations constant on `<g>`-orbits) is null.  Either some orbit is
infinite, and infinitely many independent coordinates must agree, or
infinitely many finite orbits of size at least two give independent
constancy events of probability at most `1/2`.  **Ergodicity:** Walsh
characters `chi_F` (`F` finite, nonempty) are permuted by `G`, and `G.F` is
infinite, since otherwise `union G.F` would be a finite invariant subset of the
infinite transitive `G`-set `I`.  A square-summable invariant coefficient
family therefore vanishes off `F = empty`.  With `Z_q` acting trivially, this
gives essential freeness of `G/Z_q` and ergodicity.
