---
rg: 2
id: diagonal-cone-covered-actors-leavitt-commutant-proof
kind: route
title: Split the Cantor module along the prefix code; equivariance kills the cross blocks through vanishing coinvariants and makes the diagonal blocks scalars
target: diagonal-cone-covered-actors-lie-in-binary-leavitt-unit-group
requires:
  - leavitt-algebras-l-k-1-n-are-simple
  - binary-leavitt-unit-word-problem-decidable
  - thompson-steinberg-presentation-of-leavitt-unit-group
  - complexity-bounded-host-classes-are-not-universal
---

Notation as in the target. Additive maps `M → M` are `F_2`-linear, since `M` has exponent 2.

## Lemma 1: invariants, coinvariants and commutant of a clopen-rigid group

Let `H <= V` be clopen-rigid.

- **(a) `M^H = F_2·1`.** If `f` is `H`-invariant, the clopen set `f^(-1)(1)` is invariant. By
  (H1) a proper nonempty clopen set is carried to every other one, e.g. `[0]` to `[00]`, so an
  invariant clopen set is `∅` or `C`, and `f` is constant.
- **(b) `M_H = 0`, i.e. `span{h f - f} = M`.** By (H1), `χ_A - χ_B` lies in the span for all
  proper nonempty clopen `A, B`. So `χ_[0] ≡ χ_[00] ≡ χ_[01]`, and
  `χ_[0] = χ_[00] + χ_[01] ≡ 2χ_[0] = 0`. Hence every proper indicator is `≡ 0`, and
  `1 = χ_[0] + χ_[1] ≡ 0`. These span `M`.
- **(c) `End_H(M) = F_2·id`.** Let `T` commute with `H`.
  - For `h ∈ Stab_H([0])`, `h·Tχ_[0] = T χ_(h[0]) = Tχ_[0]`, so the clopen set where
    `Tχ_[0] = 1` is `Stab_H([0])`-invariant. By (H2), `Tχ_[0] = a χ_[0] + b χ_[1]` for some
    `a, b ∈ F_2`.
  - For proper nonempty clopen `A`, choose `h ∈ H` with `h[0] = A` by (H1). Then
    `Tχ_A = h·Tχ_[0] = a χ_A + b χ_(C∖A)`.
  - Apply this to `[00]` and `[01]`, using `χ_(C∖A) = 1 + χ_A`:
    `Tχ_[0] = Tχ_[00] + Tχ_[01] = aχ_[0] + b(χ_[00] + χ_[01]) = (a+b)χ_[0]`. Comparing with
    `aχ_[0] + bχ_[1]` gives `b(χ_[0] + χ_[1]) = 0`, so `b = 0`.
  - Then `T 1 = T(χ_[0] + χ_[1]) = a·1`, and `T = a·id` on the spanning set of indicators.

**`V` is clopen-rigid.**
- (H1): write proper nonempty clopen `A, B` and their complements as disjoint unions of cones.
  Splitting a cone into its two children raises the count by one, so both pairs can be brought
  to equal numbers of cones. A bijection of the pieces is a prefix replacement taking `A` to `B`.
- (H2): `Stab_V([0])` contains the prefix replacements acting by an arbitrary element of `V` on
  the tails of `[0]` and trivially on `[1]`, and symmetrically. If `B` is invariant, `B ∩ [0]`
  is a clopen subset of `[0] ≅ C` invariant under a copy of `V`, hence `∅` or `[0]` by (H1) for
  `V`. Likewise for `B ∩ [1]`.

## Lemma 2: the commutant of a diagonal cone subgroup

Keep the notation of the target: `α_1..α_k, β_1..β_m` a complete prefix code, `γ_1..γ_m` a
complete prefix code, `S_β = Σ_l s_(β_l) t_(γ_l)`, `T_β = Σ_l s_(γ_l) t_(β_l)`, and
`c(h,k) = Σ_i s_(α_i) h t_(α_i) + S_β k T_β`.

**Relations.** Distinct words of a prefix code satisfy `t_a s_b = 0`, and `t_a s_a = 1`. So
- `t_(α_i) s_(α_j) = δ_ij`, `t_(α_i) S_β = 0`, `T_β s_(α_j) = 0`, `T_β S_β = Σ_l s_(γ_l) t_(γ_l) = 1`;
- for a complete prefix code, `Σ_i s_(α_i) t_(α_i) + Σ_l s_(β_l) t_(β_l) = 1` (expand `1` with
  `s_0 t_0 + s_1 t_1 = 1` down the tree), and `S_β T_β = Σ_l s_(β_l) t_(β_l)`. Hence
  `1 = Σ_i s_(α_i) t_(α_i) + S_β T_β`.

**`c(h,k)` lies in `V`.** It is the prefix replacement acting as `h` on the tails of each `[α_i]`
and as `ι k ι^(-1)` on `R_β`, where `ι(γ_l w) = β_l w`. From the relations,
`t_(α_i) c = h t_(α_i)`, `c s_(α_j) = s_(α_j) h`, `T_β c = k T_β`, `c S_β = S_β k`.

**Blocks.** For additive `T : M → M` put `T_(ij) = t_(α_i) T s_(α_j)`,
`T_(iβ) = t_(α_i) T S_β`, `T_(βj) = T_β T s_(α_j)`, `T_(ββ) = T_β T S_β`. Writing `T = 1·T·1`
with the decomposition of `1`,

`T = Σ_(i,j) s_(α_i) T_(ij) t_(α_j) + Σ_i s_(α_i) T_(iβ) T_β + Σ_j S_β T_(βj) t_(α_j) + S_β T_(ββ) T_β`.

**Equivariance.** Suppose `T c(h,k) = c(h,k) T` for all `h ∈ H`, `k ∈ K`. Multiply on the left
by `t_(α_i)` or `T_β` and on the right by `s_(α_j)` or `S_β`:

1. `h T_(ij) = T_(ij) h`, so `T_(ij) = λ_(ij)·id` by Lemma 1(c) for `H`.
2. `h T_(iβ) = T_(iβ) k` for all `h, k`.
   - `k = 1` puts the image in `M^H = F_2·1`.
   - `h = 1` gives `T_(iβ)(k f - f) = 0`, and these span `M` by Lemma 1(b) for `K`.
   - So `T_(iβ) = 0`.
3. `k T_(βj) = T_(βj) h`. Symmetrically, `h = 1` and Lemma 1(b) for `H` give `T_(βj) = 0`.
4. `k T_(ββ) = T_(ββ) k`, so `T_(ββ) = μ·id` by Lemma 1(c) for `K`.

So `T = Σ λ_(ij) s_(α_i) t_(α_j) + μ S_β T_β = Σ λ_(ij) s_(α_i) t_(α_j) + μ Σ_l s_(β_l) t_(β_l)`.
Conversely every such map commutes with `D`, by the same relations.

**Invertible elements.**
- If `λ c = 0` for a nonzero column `c`, then `T(Σ_j c_j s_(α_j) g) = 0` for every `g`, so `T`
  is not injective. If `m >= 1` and `μ = 0`, `T` kills `s_(β_1) g`.
- So invertibility forces `λ ∈ GL_k(F_2)` and `μ = 1`. Then
  `a = Σ λ_(ij) s_(α_i) t_(α_j) + Σ_l s_(β_l) t_(β_l)` and
  `a' = Σ (λ^(-1))_(ij) s_(α_i) t_(α_j) + Σ_l s_(β_l) t_(β_l)` are inverse units of `R`, by the
  relations, and `T` is the action of `a`.

**Conjugates.** If `C_j ⊇ θ D θ^(-1)` with `θ ∈ V`, then `θ^(-1) x_j θ` commutes with `D`, so it
is the action of a unit `a`, and `x_j` is the action of `θ a θ^(-1) ∈ U`. This proves item 1.

## Item 2

Each generator of `W` is the action of a unit of `R`: the elements of `V` by definition, the
`x_j` by Lemma 2. Let `Φ : R → End(M)` be the action. It is a nonzero ring homomorphism, since
`Φ(1) = id`, and `R` is simple (`leavitt-algebras-l-k-1-n-are-simple`), so `Φ` is injective.
Hence `Φ` restricts to an injective group homomorphism on `U`. `W` lies in `Φ(U)`, and
`Φ^(-1)(W)` is a finitely generated subgroup of `U` isomorphic to `W`.

## Item 3

- `U` is finitely generated (`thompson-steinberg-presentation-of-leavitt-unit-group`: `V`
  together with one transvection) and has decidable word problem
  (`binary-leavitt-unit-word-problem-decidable`).
- Fix a finite generating set and a total algorithm for the word problem. Let `T(l)` be the
  largest number of steps it takes on words of length at most `l`. `T` is recursive: run the
  algorithm on the finitely many such words, all of which halt.
- The class `K = {U}` then satisfies the hypothesis of
  `complexity-bounded-host-classes-are-not-universal` with `C_U = 1`. So some two-generated
  group with solvable word problem embeds in no subgroup of `U`, hence in no `W` as in item 2.

`∎`

## Scope

- Only covering subgroups containing a diagonal cone subgroup are treated. A subgroup such as
  `Stab_V(0^∞) ∩ Stab_V(1^∞)` covers `M` yet contains none: its elements fix `0^∞`, while a
  diagonal cone subgroup moves every point, because clopen-rigid groups have no fixed point.
  Its commutant contains automorphisms outside `Φ(R)`; see the Attempts of
  `decidable-groups-embed-in-covered-cantor-module-actors`.
- No finite presentation hypothesis on `W` is used, so the conclusion holds for every
  finitely generated `W` of this kind.
