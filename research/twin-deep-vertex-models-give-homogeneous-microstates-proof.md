---
rg: 2
id: twin-deep-vertex-models-give-homogeneous-microstates-proof
kind: route
title: Deep stabilizers absorb the frame coordinate, induction from the deep edge subgroup matches the two frame systems, and the normal subgroup theorem kills exact models
target: twin-deep-vertex-models-give-homogeneous-microstates
requires:
  - sl2-s-arithmetic-noncentral-normal-subgroups-have-finite-index
---

Put `L = PSL_2(Q_2)`, `A = PSL_2(Z[1/2])`, `K = Stab_L(v_0)`, `K_1 = Stab_L(v_1) = gKg^(-1)`,
`K_B = K ∩ K_1`. `K(2^j) = ker(K → PSL_2(Z/2^j))` is the principal congruence subgroup of `K`.
It is normal in `K` and fixes `B_j(v_0)` pointwise. Put `K_1(2^j) = gK(2^j)g^(-1)`. Then
`C_0 = A ∩ K`, `C_1 = A ∩ K_1`, `B = A ∩ K_B`, `Γ(2^j) = A ∩ K(2^j)` (principal congruence), and
`Γ_1(2^j) = A ∩ K_1(2^j)`.

**(TD0).** Entrywise,
`K_1(2^j) = {a ≡ d ≡ 1 mod 2^j, b ∈ 2^(j−1)Z_2, c ∈ 2^(j+1)Z_2}`, so `K(2^R) ⊆ K_1(2^(R−1))`,
`K_1(2^R) ⊆ K(2^(R−1))` and `K_1(2^(R−1)) ⊆ K(2^(R−2))`. So
`N_0, N_1 ⊆ Δ_R`. `Γ(2^(R−1))` is normal in `C_0 ⊇ B`, and `Γ_1(2^(R−1))` is normal in
`C_1 ⊇ B`, so `Δ_R ◁ B`. The Atkin--Lehner element `w = [[0,1],[2,0]]` normalizes `A`, `B` and
`K_B`, swaps `K ↔ K_1`, `K(2^j) ↔ K_1(2^j)`, and therefore swaps `N_0 ↔ N_1` and fixes `Δ_R`. So
the two indices agree.

**(b).** Let `W` be exact with all stabilizers deep and `ρ_0|Δ_R = ρ_1|Δ_R`. For `w ∈ W`,
`S_0(w) = Stab_(ρ_0(C_0))(w) ⊆ N_0 ⊆ Δ_R`, so `S_0(w) = Stab_(ρ_0(Δ_R))(w)`. Similarly for the
other side. Since `ρ_0|Δ_R = ρ_1|Δ_R`, we get `S_0(w) = S_1(w) =: S(w)`, a subgroup of
`N_0 ∩ N_1`. Exactness gives `S(ρ_0(c)w) = cS(w)c^(-1)` for `c ∈ C_0` and similarly for `C_1`, so
the law of `S(w)` under uniform `w` is invariant under conjugation by `⟨C_0, C_1⟩ = A`. The group
`A` is countable and `S(aw') ⊆ N_0 ∩ N_1` holds for every point, so almost surely
`S(w) ⊆ ∩_(a∈A) a^(-1)(N_0 ∩ N_1)a`. This core is normal in `A` and has infinite index, since it
lies in `C_0`. By `sl2-s-arithmetic-noncentral-normal-subgroups-have-finite-index` it is central,
hence trivial in `PSL_2`. But `S(w)` has finite index in `C_0` because `W` is finite. This is a
contradiction. ∎

**(a), Step 1: frame spaces.** Fix `Λ`, and put `X_Λ = L/Λ` with the left `A`-action. For a
compact open `U <= L`, write `Z_U = U\X_Λ` for the finite set of left `U`-cells. `Λ` is torsion
free, so it meets every conjugate of the compact `K_B` trivially, and every `K_B`-orbit on `X_Λ` is
a free copy of `K_B`. The group `C_0` normalizes `K(2^R)`, so it permutes
`Fr^0 := Z_(K(2^R))` exactly. Each `K`-orbit in `X_Λ` contributes a copy of
`K(2^R)\K ≅ PSL_2(Z/2^R)` with stabilizer `N_0`. Likewise `C_1` permutes `Fr^1 := Z_(K_1(2^R))`,
with stabilizers `N_1`. Both refine the common cells `Z := Z_U`, `U = K(2^(R−1)) ∩ K_1(2^(R−1))`,
and `B` permutes all three systems compatibly. On a `K_B`-orbit, `B` is dense in `K_B` and
`B ∩ U = Δ_R`, so `B` acts transitively on its `Z`-cells with stabilizer `Δ_R`. The fibre of `Fr^0`
over a `Z`-cell is `Δ_R/N_0`, and that of `Fr^1` is `Δ_R/N_1`.

**Step 2: absorption.** Put `V_0 = Fr^0 × W` with diagonal `C_0`-action `ρ_0`, and
`V_1 = Fr^1 × W` with diagonal `C_1`-action `ρ_1`. Over each `K_B`-orbit both are `B`-sets over a
transitive `B/Δ_R`, hence induced from their fibres:

```text
V_0 ≅ Ind_(Δ_R)^B ((Δ_R/N_0) × (W, ρ_0|Δ_R)),     V_1 ≅ Ind_(Δ_R)^B ((Δ_R/N_1) × (W, ρ_1|Δ_R)).
```

*Lemma F.* Let `N ◁ Δ` and let `W` be a finite `Δ`-set whose stabilizers lie in `N`. Then
`(Δ/N) × W ≅ [Δ:N]·W`, explicitly.

*Proof.* The orbit of `(qN, w)` has stabilizer `N ∩ Stab(w) = Stab(w)`, so the projection to `W`
is injective on it and maps it onto the orbit of `w`. Choosing representatives `q_1, …, q_k` of
`Δ/N`, the map `(q_iN·δ, w) ↦ (i, …)` is well defined orbitwise and bijective. Concretely, send
`(qN, w)` to `(j, w)`, where `j` indexes the orbit of `(qN, w)` among the `k` lifts of the orbit of
`w`. ∎

The deep points form a `ρ_0(C_0)`-invariant set, because `N_0` is normal. Apply Lemma F to the
`ρ_0`-deep part, and its `ρ_1` analogue to the other side. This gives `B`-isomorphisms over `B/Δ_R`
from `V_0` and `V_1` to `Ind_(Δ_R)^B([Δ_R:N_0]·W)`, computed with `ρ_0|Δ_R` and with `ρ_1|Δ_R`
respectively, apart from `O(ε)|V|` exceptional points. Compose the first isomorphism, the identity
of `W` (defect `<= ε` per generator of `Δ_R`), and the inverse of the second. The result is a
bijection `τ : V_0 → V_1` over `Z`. For `s ∈ S_B` write `s·b_i = b_j δ` with fixed coset
representatives `b_i`; the `δ ∈ Δ_R` have bounded length `ℓ_R`. So `τ` has `B`-defect at most
`c_R ε |V_0|` on `S_B`.

**Step 3: microstates.** On `V_0` let `σ(c) = ρ_0(c)` for `c ∈ C_0` and `σ(c') = τ^(-1)ρ_1(c')τ`
for `c' ∈ C_1`, and extend `σ` to `A = C_0 *_B C_1` through fixed normal forms. The only relations
of `A` beyond those of `C_0` and `C_1` identify generators of `B`. By a union bound over the edge
identifications used by a finite word window `F`, `σ` is `(F, O_(F,R)(ε))`-multiplicative.
Choose the mark `y(v)` to be any point of the `Fr^0`-cell of `v`.
* For `c ∈ C_0` the marks are exactly equivariant at level `R`.
* For `c' ∈ C_1`, `τ` preserves `Z`-cells, and every `Z`-cell lies in a single
  `K_1(2^(R−1))`-cell, which `c'` permutes. Since `ρ_1` is exact on `Fr^1`, the points
  `y(σ(c')v)` and `c'·y(v)` lie in one `K_1(2^(R−1))`-cell, hence in one `K(2^(R−2))`-cell.

A word of length `ℓ` loses at most `ℓ` further levels. Given `F` and a target scale, choose `R` so
that `K(2^(R−2−ℓ_F))`-cells have small diameter, and then `ε` small. This produces `(HV1)` of
`homogeneous-quotient-soficity-gives-vertex-soficity`. ∎
