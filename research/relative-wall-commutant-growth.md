---
rg: 2
id: relative-wall-commutant-growth
kind: claim
title: A relative wall is exactly compressor growth of the relative commutant
distinct_from:
  commutant-no-growth: That claim is the finite-dimensional collapse for a genuine representation, proved by counting the linear dimension of a fixed space; this one is an exact equivalence, valid in every finite tracial von Neumann algebra, between existence of a wall and properness of one inclusion of relative commutants.
  finite-normal-compression-obstruction: That claim kills a finite normal subgroup in operator-norm corona representations using Kazhdan transport; this one is an algebraic normal form for the wall with no approximation, no property (T), and no finiteness hypothesis.
  invariant-size-collapse: That is the general collapse principle for a conjugation-invariant strictly monotone size; this identifies what the collapsing inclusion actually decides, namely existence of the relative wall, and supplies the equivalence in both directions including the case where no such size exists.
  corona-commutant-no-growth: That asks whether the same inclusion is an equality in an operator-norm corona for the affine non-MF pair, where no trace exists at all; this is an equivalence rather than a question, holds in every target group, and its consequences are drawn in the tracial category for the Kun--Thom pair.
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

Let `Gamma<G`, `t Gamma t^(-1)<=Gamma`, and `pi:G->U` a homomorphism into an
**arbitrary group** `U`.  Put

```text
N=C_U(pi(Gamma)),     N_t=C_U(pi(t Gamma t^(-1))).
```

For `U=U(M)` with `M` finite tracial these are the relative commutants
`M cap pi(Gamma)'` and `M cap pi(t Gamma t^(-1))'`.

Then `Ad pi(t)(N)=N_t>=N`, and a relative wall -- a unitary `v in N` with
`[v,pi(t^(-1) gamma t)]!=0` for some `gamma in Gamma` -- exists **iff**
`N!=N_t`.  The marked predecessor `h` is not data.

Involutive form: a Clifford wall exists iff there are `gamma in Gamma` and a
self-adjoint involution `w in N_t` with
`w (pi(gamma) w pi(gamma)^*)+(pi(gamma) w pi(gamma)^*) w=0`.

**Invariance form.**  If `Gamma` is infranormal, a wall exists for *some*
compressor iff `N` is not `Ad pi(G)`-invariant.  This is the exact
noncommutative counterpart of Kun--Thom Theorem C, which asserts that
`L^infinity(X)^Gamma` *is* `G`-invariant for sofic p.m.p. actions: the wall
is precisely the failure of that theorem when "sofic action" is weakened to
"Connes-embeddable model".  A construction that untwists the extension --
producing a `G`-invariant complement or an invariant lamp algebra -- makes
`N` invariant and so destroys its own conclusion.

Because the argument is purely group-theoretic, `N=N_t` -- hence no wall --
follows in every target carrying a conjugation-invariant strictly monotone
size: finite groups by order, genuine finite-dimensional representations by
linear dimension (`commutant-no-growth`), compact targets by recurrence
(`infranormal-compact-closure-normal`).  A II_1 target has no such size, and
`kun-thom-clifford-cover-weakly-sofic` shows the wall is genuinely realized
in a metric ultraproduct of finite groups.
