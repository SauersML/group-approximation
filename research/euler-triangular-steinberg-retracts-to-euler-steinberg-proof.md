---
rg: 2
id: euler-triangular-steinberg-retracts-to-euler-steinberg-proof
kind: route
title: Functoriality of Steinberg groups for the corner inclusion and the unital projection
target: euler-triangular-steinberg-retracts-to-euler-steinberg
requires:
  - euler-triangular-ring-is-fp-rf
  - steinberg-groups-of-fp-rings-are-fp-in-rank-five
---

**1.**
- The Steinberg relations use only addition and multiplication, so every ring homomorphism, unital or not,
  induces a homomorphism of Steinberg groups on the generators `x_ij(r)`.
- `π ∘ ι = id_D`, hence `St(π) ∘ St(ι) = id`. So `St(ι)` is injective and `St_N(D)` is a retract.
- The matrix map `A -> ι(A) + diag(0,1) ⊗ I_N` from `GL_N(D)` to `GL_N(T_l)` is a homomorphism, because
  `ι(A)ι(B) = ι(AB)` and `ι(A)(1-e) = 0` with `e = [[1,0],[0,0]]`. On elementary generators it agrees with
  `St(ι)` followed by `St_N(T_l) -> E_N(T_l)`.
- So an element of `St_N(D)` with trivial image in `E_N(D)` has trivial image in `E_N(T_l)`.

**2.**
- *If it survives in `St_N(T_l)`.* A finite quotient `ρ` of `St_N(T_l)` restricts to a finite quotient
  `ρ ∘ St(ι)` of `St_N(D)`.
- *If it survives in `St_N(D)`.* A finite quotient `ρ'` of `St_N(D)` gives the finite quotient `ρ' ∘ St(π)`
  of `St_N(T_l)`, and `ρ' ∘ St(π) ∘ St(ι) = ρ'`.
- The intersection statement follows.

**3.** Let `N >= 5`. `D` is a finitely presented unital ring, with generators `u, x, x', B` and four relations
(Step 1 of `resolvent-ring-has-path-normal-form-proof`). So `St_N(D)` is finitely presented
(`steinberg-groups-of-fp-rings-are-fp-in-rank-five`), as is `St_N(T_l)`.
- *The quotients.* Put `Λ_T = St_N(T_l)/St_N(T_l)_rf` and `Λ_D = St_N(D)/St_N(D)_rf`.
- *`St(π)` descends.* The image of `St_N(T_l)_rf` lies in `St_N(D)_rf`, because the preimage of a
  finite-index normal subgroup has finite index. So `St(π)` induces `Λ_T -> Λ_D`.
- *`St(ι)` descends.* By 2, `St(ι)` induces an injection `Λ_D -> Λ_T`. The composite is the identity, so
  `Λ_D` is a retract of `Λ_T`.
- *Retracts of finitely presented groups are finitely presented.* If `r : G -> H` is a retraction with
  section `s`, then `H ≅ G / <<g^(-1) s(r(g)) : g in S>>` for a finite generating set `S` of `G`.
- *Conclusion.* If `St_N(T_l)_rf` is finitely normally generated, `Λ_T` is finitely presented. So `Λ_D` is,
  and hence `St_N(D)_rf` is finitely normally generated in the finitely presented group `St_N(D)`.

**4.** The symbols `{π_0, π_q}` are Steinberg symbols of commuting units of `D`, so they lie in `St_N(D)`. ∎
