---
rg: 2
id: stw27-frobenius-fails-to-localize-proof
kind: route
title: Pinch the ranks, round the constant strata by an eigenvalue gap, and pin the exact failure of the stratified Frobenius step
target: stw27-frobenius-obstruction-fails-to-localize-to-rank-strata
requires:
  - stw27-coordinate-euler-slack-obstructs-compact-dividers
artifacts:
  - research/artifacts/stw27-soft-divider-stratified-attack-audit-2026-08-30.md
---

(1) `[E]` is compact and `(ell+1)[b]=sup_epsilon (ell+1)[(b-epsilon)_+]`
is a supremum of an increasing sequence, so `[E]<=(ell+1)[(b-epsilon_0)_+]`
for some `epsilon_0`.  Cuntz subequivalence dominates pointwise ranks, so
for `epsilon<=epsilon_0`,

```text
M <= (ell+1) rank((b-epsilon)_+(x)),
ell rank((b-epsilon)_+(x)) <= ell rank(b(x)) <= M.
```

(2) Write `c=(b-epsilon)_+` and suppose `rank(c(x))=r` for all `x`.  The
`r`-th largest eigenvalue `lambda_r(c(x))` is continuous in `x` and
strictly positive, so it is bounded below by some `delta>0` on the
compact space `X`.  The spectrum of `c` is then contained in
`{0} union [delta,||b||]`, the indicator of `[delta/2,infinity)` is
continuous on it, and functional calculus produces a projection `p` with
`c ~ p` in the Cuntz semigroup.  The two inequalities `(C)` become
`ell[p] <= [E] <= (ell+1)[p]`; over a finite-dimensional compact space,
Cuntz comparison of projections is Murray-von Neumann subequivalence, so
both are subbundle relations, and the required claim gives
`(ell+1)N_ell<=M`.  Over a coordinate-heavy block (`(ell+1)N_ell>M`)
this is absurd, so no cutdown has constant rank; since all cutdown
ranks lie in the window of (1), the window contains two integers.

(3) The stratified relations do hold.  On the closed set
`C={x : rank(c(x))=r_min}` the eigenvalue argument of (2) runs verbatim
and the support of `c` is a bundle `F_C` over `C`.  From
`ell[c]<=[E]`, the Rordam characterization gives `t` with
`t^*t=(c'-eta)_+^{oplus ell}` (a slightly deeper cutdown `c'`) and
`tt^* in her(E)`; on the locus where the deeper cutdown still has
locally constant rank, `t` times the continuous local inverse of
`|t|` is a continuous partial isometry, so `ell F_C` embeds as a
subbundle of `E|_C` and `E|_C ~ ell F_C oplus G_C`.  The compact no-go
would now need

```text
c(F_C)^ell = 1  in H^*(C;F_ell),
```

which over `X` itself follows from Frobenius plus `e_i^2=0`.  Over `C`
it fails: `H^*(C;F_ell)` is the Cech cohomology of an arbitrary closed
subset of a `2N`-manifold, and for `N` large `C` can contain an
embedded copy of `CP^ell`, whose generator `alpha` has
`alpha^ell != 0`.  A bundle `F_C` with `c_1(F_C)` restricting to
`alpha` breaks the vanishing step, so the mod-`ell` argument proves
nothing on strata.  A cup-product patch also fails to globalize: even
if every stratum killed all coordinate monomials of size above
`M/(ell+1)`, the covering argument needs disjoint monomial supports of
total size at most `N`, while the strata count times the monomial size
is of order `M^2/ell(ell+1)^2`, which exceeds `N=M` for
`M>ell(ell+1)^2`.
