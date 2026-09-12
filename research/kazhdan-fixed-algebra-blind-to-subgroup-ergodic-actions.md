---
rg: 2
id: kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions
kind: claim
title: The fixed diagonal algebra of a Kazhdan subgroup sees nothing of a sofic action on which that subgroup acts ergodically
distinct_from:
  kun-thom-nonsofic-wreath: that imports Theorem C, which derives nonsoficity from a non-invariant fixed algebra; this proves that the same fixed algebra carries no information at all once the subgroup acts ergodically
  kazhdan-projection-is-norm-limit-of-finite-averages: that is the approximation fact for the Kazhdan projection; this applies it to a sofic embedding of a crossed product
artifacts:
  - research/artifacts/free-nonsofic-action-sources-verified-2026-09-11.md
---

**ESTABLISHED.** Let `G ↷ (X,μ)` be a sofic p.m.p. action with sofic embedding
`Θ : L^∞(X) ⋊ G → Π_(n→𝒰) M_(|Y_n|)(C)` (Kun--Thom Definition 2.2), put
`σ(g) = Θ(u_g)`, and let `Γ <= G` have property (T). If `Γ` acts ergodically on
`(X,μ)`, then for every `f ∈ L^∞(X)`

```text
E_(D_𝒰^(σ(Γ))) ( Θ(f) ) = ( ∫ f dμ ) · 1,
```

where `D_𝒰^(σ(Γ))` is the algebra of diagonal elements fixed by `σ(Γ)` and `E`
its trace-preserving conditional expectation. Consequently:

1. `Θ(L^∞(X)) ∩ D_𝒰^(σ(Γ)) = C·1`, and `Θ(L²_0(X))` is orthogonal to
   `L²(D_𝒰^(σ(Γ)))`.
2. The conclusion of Kun--Thom Theorem C ("`L^∞(X)^Γ` is `G`-invariant") holds
   trivially, and Proposition 3.1 (normalization of `D_𝒰^(σ(Γ))` by `σ(G)`) is a
   statement about `σ` that meets the embedded action only in the constants.
   Neither can produce a contradiction for such an action.
3. **Mixing actions are invisible to the mechanism.** For a mixing action of an
   infinite group every infinite subgroup acts ergodically. Mixing passes to
   factors and to restrictions to infinite subgroups. So no Theorem-C argument,
   applied to the action, to a factor of it, or to a restriction of it, can prove
   a mixing action nonsofic.

Proof in `kazhdan-fixed-algebra-blindness-proof`.

**Scope.** This covers the fixed diagonal algebra `D_𝒰^(σ(Γ))` and everything
derived from it. It does not cover Kun--Thom Theorem 4.1 (normalization of the
permutation centralizer `C_(𝒮_𝒰)(σ(Γ))`), which is not a subalgebra of the
diagonal; see the Attempts of `mixing-free-nonsofic-action-of-sofic-group`.
