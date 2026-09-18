---
rg: 2
id: tarski-monster-tori-evade-compression-and-stage-lifts-proof
kind: route
title: Simplicity and a trivial centralizer pin every Kazhdan subgroup of a monster torus to Q, and the increasing stage kernels feed the stage-lift criterion
target: tarski-monster-tori-evade-compression-and-stage-lifts
requires:
  - hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan
  - lef-mapping-torus-iff-stage-liftable-automorphism
  - finite-outer-order-mapping-torus-is-virtually-product
  - normal-kazhdan-defect-non-mf
  - compression-defects-need-strict-kernel-centralizer-towers
  - lef-implies-operator-mf
artifacts:
  - research/lef-mapping-torus-iff-stage-liftable-automorphism.md
  - research/finite-outer-order-mapping-torus-is-virtually-product.md
  - research/normal-kazhdan-defect-non-mf.md
  - research/compression-defects-need-strict-kernel-centralizer-towers.md
---

## 0. Imports

From `hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan` and its route:
- **(M1)** every stage `G(j)` is torsion-free hyperbolic;
- **(M2)** `N_0 ⊆ N_1 ⊆ ...` and `N = ∪ N_j`;
- **(M3)** `Q` is infinite, non-abelian and torsion-free, and every proper subgroup is cyclic;
- **(M4)** `Q` is Kazhdan;
- **(Q0)** `Q` has no nontrivial finite quotient (route, section 1, unconditional);
- **(Q1)** under `(RF_Γ)`, `Q` is LEF (route, section 2).

Standard facts:
- **(H)** a torsion-free hyperbolic group that is not cyclic has trivial centre;
- **(T0)** an infinite cyclic group is not Kazhdan, and quotients of Kazhdan groups are Kazhdan;
- **(So)** an extension of a sofic group by an amenable group is sofic (Elek--Szabó), and LEF
  groups are sofic.

## 1. (i) Q is centreless and simple

**Centre.** Let `c ∈ Z(Q)` be represented by a word `x`. The finitely many words `[x, s]`,
`s ∈ S`, lie in `N`, so by (M2) they lie in some `N_j`. Then `x` is central in `G(j)`. The stage
`G(j)` maps onto `Q`, which is not cyclic by (M3), so `G(j)` is not cyclic. By (M1) and (H),
`x = 1` in `G(j)`, hence `c = 1`.

**Simplicity.** Let `1 ≠ M ◁ Q` be proper. By (M3), `M = ⟨m⟩` is infinite cyclic. Conjugation
gives `Q → Aut(M) ≅ Z/2`. By (Q0) this map is trivial, so `m ∈ Z(Q) = 1`, a contradiction.

## 2. (ii) The radical dichotomy

Assume `[ψ]` has infinite order in `Out(Q)`.

1. **`C_P(Q) = 1`.** Let `q t^e` centralize `Q`. Then `Ad(q) ∘ ψ^e = id` on `Q`, so `ψ^e` is
   inner, and `e = 0`. Then `q ∈ Z(Q) = 1` by (i).
2. **Normal subgroups.** Let `M ◁ P`. Then `M ∩ Q ◁ Q`, so `M ∩ Q ∈ {1, Q}` by (i). If
   `M ∩ Q = 1`, then `[M, Q] ⊆ M ∩ Q = 1`, so `M ≤ C_P(Q) = 1`.
3. **Homomorphisms.** Let `Θ` be a homomorphism of `P` with `Θ|_Q ≠ 1`. Then `ker Θ` does not
   contain `Q`, so `ker Θ = 1` by step 2.
4. **The radical.** `Rad_MF(P)` is the intersection of `ker Θ` over homomorphisms `Θ` to unitary
   groups of matrix coronas. The map `P → Z → U(1)`, `t ↦ e^(2πiθ)` with `θ` irrational, composed
   with scalars in a corona, has kernel `Q`. So `Rad_MF(P) ⊆ Q`. By step 3, either every `Θ` kills
   `Q` and `Rad_MF(P) = Q`, or some `Θ` is injective and `P` is operator MF with `Rad_MF(P) = 1`.

**Finite outer order.** By `finite-outer-order-mapping-torus-is-virtually-product`, `P` is
virtually `Q × Z`, and it is MF when `Q` is MF. Under `(RF_Γ)`, `Q` is LEF by (Q1), hence MF by
`lef-implies-operator-mf`, and `Rad_MF(P) = 1`.

## 3. (iii) Compression certificates are vacuous

**Kazhdan subgroups.** Let `L ≤ P` be Kazhdan. Its image in `P/Q ≅ Z` is Kazhdan by (T0), hence
finite, hence trivial. So `L ≤ Q`. If `L ≠ Q`, then `L` is cyclic by (M3), and torsion-free, so
`L = 1` by (T0). Thus `L ∈ {1, Q}`. This uses no hypothesis on `ψ`.

Now assume `[ψ]` has infinite outer order, so `C_P(Q) = 1` by section 2.

- **Lean core.** Let `ι : Λ → P` with `Λ` Kazhdan, `t` compressing `ι(Λ)` and `c` centralizing
  `ι(Λ)`. The image `ι(Λ)` is Kazhdan, so it is `1` or `Q`. If it is `1`, every commutator
  `[t c t^-1, ι λ]` is trivial. If it is `Q`, then `c ∈ C_P(Q) = 1`, and again every commutator is
  trivial. So `defectNormal = 1`, and it contains no nontrivial normal Kazhdan subgroup. The
  hypothesis of `normal-kazhdan-defect-non-mf` is never met in `P`.
- **Intrinsic defect.** In the notation of `compression-defects-need-strict-kernel-centralizer-towers`,
  `D_P(1) = 1` trivially. For `L = Q`, the generators `[g z g^-1, l]` have `z ∈ C_P(Q) = 1`, so
  `D_P(Q) = 1`. (The exact criterion there agrees: `M = C_Q(Q) = Z(Q) = 1` is normalized by every
  compressor.)
- **Tracial shadow.** Under `(RF_Γ)`, `Q` is LEF by (Q1), hence sofic, and `P` is sofic by (So).
  A sofic group embeds in the unitary group of a tracial ultraproduct of matrix algebras. So no
  homomorphism-level tracial argument can kill `Q ≠ 1` in all hyperlinear representations of `P`.

## 4. (iv) Stage lifts

Assume `(RF_Γ)`, and let `J` be an infinite set of stages carrying lifts `α_j ∈ Aut(G(j))` with
`α_j(π_j s) = π_j(w_s)`, where `π_j : F(S) → G(j)`.

1. **Convergence.** Let `u ∈ F(S)`. If `u ∈ N`, then `u ∈ N_j` for all large `j` by (M2). If
   `u ∉ N`, then `u ∉ N_j` for every `j`, since `N_j ⊆ N`. So `(G(j), S) → (Q, S)` along `J`.
2. **Residual finiteness.** Each `G(j)` is a torsion-free hyperbolic quotient of `Γ` by (M1). So it
   is residually finite by `(RF_Γ)`, and it is finitely generated.
3. **Conclusion.** Clause (c) of `lef-mapping-torus-iff-stage-liftable-automorphism` holds, so `P`
   is LEF, hence operator MF by `lef-implies-operator-mf`, and `Rad_MF(P) = 1 ≠ Q`.

The last sentence of (iv), about arbitrary residually finite approximants, is clause (c) itself.

## 5. The Paulin remark

This is cited from memory and used nowhere above: Paulin's theorem on hyperbolic groups with
infinite `Out`, plus the fact that Kazhdan groups fix a point in every isometric action on an
`R`-tree. It says only that each stage lift has finite outer order *in its stage*. It does not bound
the outer order of `ψ`, since the stage lifts may have unbounded orders.

## Checked against

- **Is `C_P(Q) = 1` automatic?** No. It uses infinite outer order, and it fails for inner `ψ`.
  That case is covered by the finite-order paragraph of section 2.
- **Does soficity of `P` need `(RF_Γ)`?** As stated, yes. Unconditionally, (iii) holds whenever
  `Q` is hyperlinear.
