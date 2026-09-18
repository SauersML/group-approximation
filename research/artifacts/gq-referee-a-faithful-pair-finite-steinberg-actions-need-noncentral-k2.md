# Referee report (gq-referee-a, proof-gap lens): faithful pair-finite Steinberg actions need non-central K_2

**Reviewed:** lane gq-typeA-design, 05eb02b9f, read on origin/main.
- `faithful-pair-finite-steinberg-actions-need-noncentral-k2` and its route `-proof`;
- its input `type-a-actors-have-no-infinite-virtually-central-subgroup` and its `-proof`.

**Verdict: PASS for both.** No gaps found. The trust surface of Step 1 can be removed (see Step 1 below).

## The four steps the author named
- **Step 1, scalars.** It suffices to cite `leavitt-tuples-make-rational-scalar-powers-elementary`, whose proof-gap
  review is PASS at 223b354f1. With `d = 2` it gives `q I_m ∈ E_m(S)` for all `m ≥ 3` and all `q ∈ Q^×`.
  - This is exactly the Step 1 input, and it replaces the unreviewed `ibn-failure-makes-rational-scalars-elementary`.
  - Centrality and injectivity of `λ ↦ λI_N` are correct.
- **The perfect-central lemma.** `φ(gh) = g·φ(h)·g^{-1}·φ(g)`, and `φ(h) ∈ K` is central, so this equals
  `φ(h)φ(g)`. So `φ` is a homomorphism into the abelian group `K`. `Γ` is perfect, so `φ = 1`.
  - Hence `Z(Γ) = π^{-1}(Z(E_N(R)))`. `π` is onto, so `π(Z(Γ)) = Z(E_N(R)) ⊇ Q^× I_N`.
  - `Q^×` is not finitely generated, and subgroups of finitely generated abelian groups are finitely generated. So
    `Z(Γ)` is not finitely generated.
- **Corollary 1 of the virtually-central lemma.** I read the lemma's proof, and it is correct.
  - There are finitely many point orbits, then finitely many orbits on ordered pairs, and these pass to the
    finite-index centralizer `C`.
  - `zZ_i ↦ C·(s_i, z s_i)` is well defined and injective, so `[Z : Z_i] < ∞`.
  - Each `Z_i` fixes its orbit pointwise, so faithfulness gives `∩ Z_i = 1` and hence `Z` is finite.
  - Applied to the faithful quotient `Γ/M`, the image of `Z(Γ)` is central, hence finite, so `[Z(Γ) : M ∩ Z(Γ)] < ∞`.
  - For `M = 1` this contradicts Step 4.
- **Group lemma 0** (PASS at 58d536cf7).
  - `M ≤ Z(Γ) = Z(Γ) ∩ [Γ,Γ]`, because `Γ` is perfect.
  - `M` is not finitely generated: `M` has finite index in `Z(Γ)`, and a finite extension of a finitely generated group is
    finitely generated.
  - Applying the lemma with `C_0 = C = M` gives that `Γ/M` is not finitely presented.

## Scope
Correctly limited. It constrains `St_N(R)` only as the actor. It is conditional on `K_2(N,R)` being central, which is OPEN
for `R_L`.
