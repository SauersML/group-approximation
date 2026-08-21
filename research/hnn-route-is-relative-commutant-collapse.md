---
rg: 2
id: hnn-route-is-relative-commutant-collapse
kind: claim
title: In the matrix ultraproduct the co-dense Kazhdan HNN route is exactly a relative-commutant collapse, the same problem as Kun-Thom approximate normalization
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that is the finite-dimensional theorem consuming flexible HS-stability of the base; this shows its sharp ultraproduct form is a relative-commutant identity that does NOT reference stability, unifying it with the Kun-Thom lane.
  approximate-collapse-for-kt-compressor: that is the (AC) wall for EL_r(F_q[x])'s compressed Kazhdan copy; this is the same wall for the explicit arithmetic pair SL_2(Z) <= SL_2(Z[1/2]), where co-density replaces the compressor and the arithmetic may be more tractable.
---

Let `A` be finitely generated with a co-dense subgroup `C` (every
finite-dimensional representation of `A` restricts on `C` to one with the
same commutant: `rho(C)' = rho(A)'`), and form the HNN extension
`G = <A, t | [t, C] = 1>`.  Pass to the tracial matrix ultraproduct
`M = prod_U M_(d_n)` carrying the canonical trace of `G`, with
`pi = prod pi_n : A -> M` the restriction (trace = the regular trace
`tau_A`), and `k = [t] in U(M)`.

**Reduction.**  `G` is not hyperlinear as soon as the following holds:

```text
pi(C)' cap M  =  pi(A)' cap M.                                          (RC1)
```

Indeed, low defect of `[t, c] = 1` gives `k in pi(C)' cap M`; by `(RC1)`
`k in pi(A)' cap M`, so `k` commutes with `pi(a_1)`, forcing the marked
word `[t, a_1]` to have trace `1` while it is a nontrivial group element
with regular trace `0` -- contradiction.  The inclusion
`pi(A)' cap M subseteq pi(C)' cap M` is automatic (`C subseteq A`); the
content of `(RC1)` is the reverse.

**This is the Kun--Thom wall.**  `(RC1)` is exactly
`approximate-collapse-for-kt-compressor` for the pair `C subseteq A`: the
relative commutant of a subgroup inside a matrix ultraproduct must not be
larger than that of the whole group.  There the pair is the compressed
Kazhdan copy `Lambda = t Gamma t^(-1) subseteq Gamma = EL_r(F_q[x])`; here
it is `SL_2(Z) subseteq SL_2(Z[1/2])`, with co-density (equal finite
quotients, from the congruence subgroup property) playing the role of
E-normality.  So the two routes to the goal -- the co-dense Kazhdan HNN
route and the Kun--Thom centralizer-normalization route -- are, at the
ultraproduct level, one relative-commutant collapse.

**Consequence: flexible stability is a sufficient but not necessary route.**
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear` obtains `(RC1)` from
flexible HS-stability of `A` (correct the whole restriction to an exact
`rho`, then use `(tau)` and co-density).  But `(RC1)` can also be attacked
directly: it is a statement about ONE inclusion of II_1 factors
`L(SL_2(Z)) subseteq L(SL_2(Z[1/2]))` realized in a matrix ultraproduct,
and the arithmetic pair is far more explicit than `EL_r(F_q[x])`.  In
particular the Peterson--Thom character rigidity of `SL_2(Z[1/2])`
(arXiv:1303.4007) and the resulting hyperfinite HS-stability (Dogon--
Vigdorovich Thm 6.2 + Prop 8.3, using char rigidity) are available here and
not there, so the residual gap is exactly the NON-hyperfinite asymptotic
representations, i.e. those whose limit algebra is the non-amenable
`L(SL_2(Z[1/2]))` -- which is the algebra in `(RC1)` itself.

## Attempts

- **Spectral-gap attack on `(RC1)`.**  `x in pi(C)' cap M`, `A = <C, g_0>`
  with `g_0 = ` the half-parabolic `[[1,1/2],[0,1]]` (or `h = diag(2,1/2)`).
  It suffices that `x` commute with `pi(g_0)`.  Property `(tau)` of `C` on
  the congruence quotients gives a spectral gap for the `C`-conjugation
  action; the missing step is that `g_0` normalizes the `C`-isotypic
  decomposition so that `x`, already `C`-central, is forced `g_0`-central.
  This is the same one-generator-normalization step as
  `hs-normalization-via-robust-spectral-gap`, now for an explicit
  arithmetic pair.
- **Why hyperfinite stability is not enough (recorded).**  The regular
  trace of `SL_2(Z[1/2])` generates the non-amenable `L(SL_2(Z[1/2]))`, so
  the restricted microstates are not hyperfinite and the known hyperfinite
  HS-stability does not correct them; this is exactly the gap flexible
  stability would fill and the reason `(RC1)` is open.
- **Charmenability.**  Bader--Boutonnet--Houdayer--Peterson charmenability
  of `SL_2(Z[1/2])` controls its characters (they are vN-amenable off the
  center); a quantitative/ultraproduct form of charmenability, if it
  controlled relative commutants of co-dense subgroups, would give `(RC1)`.
