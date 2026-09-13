---
rg: 2
id: bernoulli-expansion-iff-ultrapower-cocycle-superrigidity
kind: claim
title: For a w-rigid group, degree-one cocycle expansion of its Bernoulli shift is equivalent to cocycle superrigidity into finite abelian groups for the Bernoulli ultrapower
distinct_from:
  popa-bernoulli-cocycle-superrigidity: that is superrigidity for cocycles on the Bernoulli shift itself; this shows that superrigidity for the metric ultrapower is exactly the quantitative degree-one stability needed downstream.
  bernoulli-shifts-have-degree-one-cocycle-expansion: that is the open expansion property for Sp_4(Z); this proves its equivalence with an ultrapower rigidity statement, for every finitely presented w-rigid group.
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-degree-one-reduction-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `bernoulli-expansion-iff-ultrapower-cocycle-superrigidity-proof`.

Let `Gamma` be finitely presented and w-rigid, `A` finite abelian, and `P_𝒰` the metric ultrapower of the measure
algebra of `[0,1]^Gamma`. The following are equivalent:
1. there is a rate `rho` (`rho(eps) -> 0`) such that every `c : S x [0,1]^Gamma -> A` with relator defects on measure at
   most `eps` agrees, off measure `rho(eps)` per generator, with an exact 1-cocycle;
2. for every non-principal ultrafilter `𝒰`, every 1-cocycle `Gamma -> P_𝒰(A)` has the form `delta f + chi` with
   `f in P_𝒰(A)` and `chi in Hom(Gamma, A)`.

**Consequence.** By `degree-one-bernoulli-expansion-excludes-weak-lifts`, statement 2 for `Gamma` excludes liftable
weakly Bernoulli actions across every nonsplit finite central extension of `Gamma`. So the central case of
`weakly-bernoulli-liftable-actions-force-virtual-splitting` over `Gamma` reduces to Popa superrigidity surviving
the ultrapower, for finite abelian targets.

**Model test.** Hypothesis side: on free groups both statements hold (no relators, and every cocycle on `F_n` is
determined freely, hence approximable). Free groups are not w-rigid, so this only checks the compactness direction.
Conclusion side: at `𝒰`-constant sequences, statement 2 contains Popa's theorem for `[0,1]^Gamma`.
