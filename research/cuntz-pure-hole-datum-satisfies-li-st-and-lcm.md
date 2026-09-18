---
rg: 2
id: cuntz-pure-hole-datum-satisfies-li-st-and-lcm
kind: route
title: Full check that the pure-hole datum on the product of a Li-Garside category with the free monoid on two letters satisfies Li's conditions (St) and (LCM), so that its bisection component admits lcms and its isotropy is the full group
target: cuntz-stabilized-garside-full-groups-are-f-infinity
requires:
  - pointed-cube-categories-are-li-garside-categories
---

**Lane proof, written out for referee cross-check (requested 2026-09-18); not independently
reviewed.** This expands §1–§2 of `cuntz-stabilized-garside-full-groups-f-infinity-proof`. All
labels are X. Li's (arXiv:2110.04505v2, §§`s:CatBisGar`–`s:GarsCat-TFG`, read at source).
Notation:
- `𝔠` satisfies `intro:Gars` with trivial units, and `M = ⟨x,y⟩`.
- `𝔠₂ = 𝔠 × M`, and `𝔖₂ = (𝔖^♯ × {1,x,y}) ∖ {units}`.
- `X₂ = X × {x,y}^ℕ`, with `X ⊆ Ω_∞(𝔠)` closed and invariant.

## A. The product category

- **(A1) Lattice hypotheses.** Here `(a,w)𝔠₂ ∩ (b,w')𝔠₂ = (a𝔠 ∩ b𝔠) × (wM ∩ w'M)`.
  - `wM ∩ w'M` is `∅` or principal (prefix order).
  - So mcms are pairs of mcms. `𝔠₂` is finitely aligned with disjoint mcms (with lcms if
    `𝔠` has them).
  - `𝔠₂` is right Noetherian, being a product of right Noetherian categories.
  - It is cancellative up to `=*`, has trivial units, and satisfies (F).
- **(A2) Garside family.** Li's criterion (Dehornoy IV.2.25, for right Noetherian
  categories with mcms) needs:
  - generation, which is clear;
  - `𝔖₂^♯ = 𝔖^♯ × {1,x,y}` closed under right divisors, which holds componentwise;
  - `𝔖₂^♯` closed under mcms: `mcm((q,t),(q',t')) = mcm(q,q') × lcm(t,t')`, with
    `lcm(t,t') ∈ {1,x,y}` when it exists.

  Local finiteness and `=*`-transversality are clear.
- **(A3) Norm.** Padding the shorter of the two normal forms with identities gives a
  normal form. So `‖(a,w)‖ = max(‖a‖,|w|)`, and
  `(𝔖₂^{≤L})^♯ = (𝔖^{≤L})^♯ × M_{≤L}` is closed under left divisors.
- **(A4) Boundary.** Constructible ideals of `𝔠₂` are finite disjoint unions of products.
  So `Ω(𝔠₂) = Ω(𝔠) × Ω(M)`, `X₂ ⊆ Ω_∞(𝔠₂)` is closed and invariant, and
  `I_l(𝔠₂) ⋉ X₂ ≅ (I_l(𝔠) ⋉ X) × G_2`.

## B. The datum

- A type `X₂(v;e)` (`e ⊆ v𝔖₂`) is **pure** if `e ⊆ 𝔖 × {1}`. Then
  `X₂(v;e) = (X(v;e_𝔠) ∩ X) × {x,y}^ℕ`.
- `𝔛` is the set of nonempty pure types, and `𝐗` is the ⊔-closure of `𝔛`.
- `𝚪` is the set of elements of Li's one-layer set
  `𝐒 = {(a_i X(𝐝(a_i); f_i))_i : a_i ∈ 𝔖₂^♯, ‖a_i f‖ ≤ 1}` all of whose target and domain
  pieces are pure. `Γ ⊆ 𝚪` consists of those with a single target.

**On the choice of `𝚪`.** Li's `lem:maxXG:allCOND` takes `𝚪 = 𝐒`, which contains
multi-target elements. We follow that, taking finite disjoint unions of single-target moves
plus identities. The smaller ⊔_𝔛-closure of `Γ` (one generator plus identities) would break
(`4_Γ`) already here: a full product expansion is `δ_τ` followed by one `𝔠`-expansion on each
copy, and that second factor has two nontrivial components.

**Lemma P** (as in the proof node). Let `X₂(v;e)` be pure and
`𝔰 = (A × B) ∖ {(1,1)}`, with `A ⊆ v𝔖^♯` and `B ∈ {{1}, {1,x,y}}`. Then every nonempty
piece of `γ(e,𝔰)`, leftover included, is pure. The proof is the three-case computation of the
holes `𝔣_s`, which are the minimal `f` with `sf ∈ 𝔰` or `sf ∈ mcm(s,e)`.

## C. Condition (St)

- **(`1_𝔛`)** is vacuous, since units are trivial.
- **(`2_𝔛`).** Let `e ⊆ v𝔖₂` be arbitrary.
  - A point `(ξ, t w)` lies in `(q,t')·X` iff `q ≼ ξ` and `t' ∈ {1, t}`.
  - So `X₂(v;e) = ⊔_{t ∈ {x,y}, (1,t) ∉ e} (1,t)·X₂(v; e_t × {1})`, where
    `e_t = {q : (q,1) ∈ e or (q,t) ∈ e}`.
  - The family `((1,t) X₂(v; e_t × {1}))_t` is an element of `𝐂` with target `X₂(v;e)`
    and domain in `𝐗`.
- **(`1_Γ`).** `γ(e, 𝔖₂)` is one-layer by `lem:gamma` (iii) with `L = 1`. It is pure by
  Lemma P with `A = 𝔖^♯` and `B = {1,x,y}`. So it lies in `Γ`.
- **(`2_Γ`).** Take `c = (c_𝔠, w)` with `‖c‖ = L`. By (A3), `‖cs‖ = L` for `s = (q,t)` iff
  `‖c_𝔠 q‖ ≤ L` and `|wt| ≤ L`. So `𝔰 = (A × B) ∖ {(1,1)}` with:
  - `A = {q : ‖c_𝔠 q‖ ≤ L}`;
  - `B = {1,x,y}` if `|w| < L`, and `B = {1}` if `|w| = L`.

  `𝔰` is closed under mcms by Li's lemma on norms of mcms. So `γ(e,𝔰)` is one-layer and, by
  Lemma P, pure. It lies in `Γ`.

## D. Condition (LCM), and lcms

- **(`3_Γ`)** holds, since `Π^* = 𝐂^*_𝐗` consists of permutations.
- **(`4_Γ`).** Let `α ∈ 𝚪`, `ω ∈ Π ∖ Π^*`, and `αω ∈ 𝚪`.
  - Componentwise, `a_i = b_j ω_i` with `a_i, b_j ∈ 𝔖₂^♯`, so `ω_i ∈ 𝔖₂^♯` by right-divisor
    closure.
  - For a hole `f` of the `i`-th piece, `b_j (ω_i f) = a_i f ∈ 𝔖₂^♯`, so `ω_i f ∈ 𝔖₂^♯`.
    Thus `ω ∈ 𝐒`.
  - Its targets are pieces of `𝐝(α)`, and its domains are pieces of `𝐝(αω)`. All are pure,
    so `ω ∈ 𝚪`.
- **(`5_Γ`).** `𝐂` admits lcms, by Li's `lem:lcm_bfC`: `𝔠₂` is right cancellative up to `=*`,
  right Noetherian, has disjoint mcms, and satisfies (F). For `α, β ∈ 𝚪`:
  - **The new factors.** The elements `a'_{ik}` of `lem:lcm_bfC` satisfy
    `a_i a'_{ik} = c_k ∈ mcm(a_i, b_j) ⊆ 𝔖₂^♯`. So `a'_{ik} ∈ 𝔖₂^♯`, as a right divisor.
  - **The new pieces.** They are
    `O_k = c_k^{-1}·(X(a_i; a_i e_i) ∩ X(b_j; b_j f_j) ∩ c_k X)`, with holes
    `c_k^{-1} mcm(c_k, a_i e_i)` and `c_k^{-1} mcm(c_k, b_j f_j)`.
    - Write `a_i = (p,t)`, `c_k = (c, c')` with `t ≼ c'`, and let `(q,1) ∈ e_i`. Then
      `mcm(c_k, (pq,t)) = mcm_𝔠(c,pq) × {c'}`. Its `c_k^{-1}`-translate is `(c^{-1}m, 1)`,
      which is pure.
    - These holes are one-layer, as in `lem:maxXG:allCOND`, because
      `mcm(c_k, a_i e_i) ⊆ 𝔖₂^♯`.
  - So `α', β' ∈ 𝚪`, and `lcm_𝐂(α,β) ∈ α𝚪 ∩ β𝚪`.
- **Consequences.** By Li's `cor:lcm`, `Π` admits lcms. So does its component `𝒞`, since an
  lcm in `Π` of two elements of `𝒞` has target in `𝐗(*)`. Then `prop:GarsideTFG` makes
  `Div_𝒞(Δ)` a Garside family with right Garside map `Δ`. With (St), `cor:ab=gamma` gives
  `𝒬(*,*) = Q(𝐂)(*,*)`, and `lem:QbfC=bmF` and `lem:QbfCYY=QbfCYvYv` identify it with
  `F((I_l ⋉ X₂)_Y^Y)`, exactly as in the second part of `thm:Fn`.

## E. The doubling moves

For pure `τ = X₂(v;e)`, `δ_τ = γ(e, {(1,x),(1,y)})` is the case `A = {1}`, `B = {1,x,y}` of
Lemma P.
- Its two pieces are `(1,x)·τ` and `(1,y)·τ`, both of type `τ`, and its leftover is empty.
- So `δ_τ ∈ Γ`.
- It is an atom of `𝒞`: a left divisor corresponds to a coarsening of the partition
  `{x·τ, y·τ}` into pure pieces, and the only proper coarsening is `{τ}`.

## Lesson for general BH

Li's (St) and (LCM) reduce to two closure facts about the chosen cylinder types:
- one-layer moves between them are closed under right divisors and lcms;
- every forced move stays among them.

A product with a free factor keeps both facts exactly when the holes never involve the free
factor. The general rule for building data is to pick types that each forced move and each
lcm preserve, and to take `𝚪` closed under finite disjoint unions, as Li's own maximal
datum is.
