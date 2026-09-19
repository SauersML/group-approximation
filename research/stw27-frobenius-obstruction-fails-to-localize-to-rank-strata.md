---
rg: 2
id: stw27-frobenius-obstruction-fails-to-localize-to-rank-strata
kind: claim
title: Constant-rank cutdowns of Villadsen dividers are compact, but the Frobenius wall does not follow soft ranks onto strata
distinct_from:
  stw27-low-rank-soft-divider-rounding: that claim rounds dividers of total rank below ell(ell+1) to compact classes; this claim rounds constant-rank cutdowns at EVERY rank and then shows the mod-prime obstruction cannot be restricted to the rank strata of a genuinely soft divider.
artifacts:
  - research/artifacts/stw27-soft-divider-stratified-attack-audit-2026-08-30.md
---

Let `ell` be prime, let `E` be a coordinate-heavy multiplicity-free
Villadsen block over `X=(S^2)^N` of total rank `M`, and let `b` be a
positive element with

```text
ell [b] <= [E] <= (ell+1)[b]                             (C)
```

in the Cuntz semigroup.  Then:

1. (Pinching at every scale.)  There is `epsilon_0>0` so that for all
   `epsilon<=epsilon_0` and every point `x`,

```text
M/(ell+1) <= rank((b-epsilon)_+(x)) <= M/ell.
```

2. (Constant-rank rounding at every rank.)  If some cutdown
   `(b-epsilon)_+` with `epsilon<=epsilon_0` has constant rank on `X`,
   then that cutdown is Cuntz-equivalent to a projection, the sandwich
   `(C)` becomes a compact sandwich, and the coordinate Euler no-go
   `(ell+1)N_ell<=M` applies.  So over a coordinate-heavy block every
   cutdown of a divider has non-constant rank, and the rank window must
   contain at least two integers.

3. (Non-localization of the wall.)  The mod-`ell` Frobenius vanishing
   `c(F)^ell=1` used in the compact no-go is a property of the
   square-free ring `H^*((S^2)^N;F_ell)` and does not restrict to rank
   strata: on the closed minimal-rank stratum `C` of a cutdown the
   support IS a bundle `F_C` and the subbundle sandwich DOES restrict,
   but `c(F_C)` lives in `H^*(C;F_ell)`, where `ell`-th powers of
   degree-two classes need not vanish (a stratum can contain an
   embedded `CP^ell`).  No stratified Chern contradiction follows.

Consequently the soft half of Problem XXVII(2) for Villadsen blocks is
constrained ONLY by rank arithmetic once `M>=ell(ell+1)`: cohomology
fences the compact and constant-rank witnesses and nothing else.  The
kill-shot experiment for the hinge is now a construction problem, not
an obstruction problem.
