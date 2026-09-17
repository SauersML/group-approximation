---
rg: 2
id: thompson-f-sandwich-splits-collapse-proof
kind: route
title: Prove the sandwich from JMBMdlS and the amenability transfer, sort kernels by Brin–Sapir type, and read mean-freeness off the stabilizer IRS dichotomy
target: f-sandwich-splits-collapse-unless-kernel-is-brin-sapir-exotic
requires:
  - affine-lamplighter-amenable-iff-extensively-amenable
  - thompson-f-amenable-iff-dyadic-action-extensively-amenable
  - thompson-f-interval-stabilizer-cosets-separate-only-if-amenable
  - thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived
  - nontrivial-normal-subgroups-of-thompson-f-contain-a-copy-of-f
  - thompson-f-mean-free-actions-dense-configurations-or-unconfined
---

**Imports.**
- JMBMdlS (arXiv:1503.04977), pinned verbatim in `affine-lamplighter-amenable-iff-extensively-amenable-citation`:
  "Lemma 2.1. Every action of an amenable group is extensively amenable, and every extensively amenable
  action on a nonempty set is amenable."
- JMBMdlS, pinned verbatim in `thompson-f-amenable-iff-dyadic-action-extensively-amenable-proof`
  (Verbatim 3, read from `extAmen2.tex` on 2026-09-17): "Let $G \acts X$ be an extensively amenable action
  and let $F\colon \cati \to \cata$ be any functor. A subgroup $H$ of $F(X) \rtimes G$ is amenable as soon
  as the intersection $H \cap (\{1\} \times G)$ is so."
- `thompson-f-interval-stabilizer-cosets-separate-only-if-amenable`, item 3: "If `H ≤ F` is amenable and
  `F/H` carries an invariant mean, then `F` is amenable."
- `thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived`, items 3–4: `m(X ∩ Fix(g)) = 0` for
  `g ≠ e`, where `X = Moved(c)`, and `μ_Ω = t·δ_e + (1−t)·μ_0` with `t = m(X)` and `μ_0` supported on
  subgroups containing `F'`.
- `nontrivial-normal-subgroups-of-thompson-f-contain-a-copy-of-f`: `F' ◁ F` is nontrivial, so it contains
  some `F_0 ≅ F`.
- `thompson-f-mean-free-actions-dense-configurations-or-unconfined`, items 2, 3 and 5.

Standard facts used: subgroups of amenable groups are amenable, and an invariant mean on `F` pushes forward
to an invariant mean on any `F`-set.

## Step 1. The sandwich (item 1)

**(T1), ⇐.** In `𝔉(X) ⋊ F` with law `(a,g)(b,h) = (a·g(b), gh)`, the cocycle identity gives
`ι(g)ι(h) = ι(gh)` for `ι(g) = (c_g, g)`. So `ι` is a homomorphism, injective because of its second
coordinate. `ι(F) ∩ ({1} × F) = {(1,g) : c_g = 1} = ι(K) ≅ K`. If `EA(X)` holds and `K` is amenable,
Verbatim 3 with `H = ι(F)` makes `ι(F) ≅ F` amenable.

**(T1), ⇒.** If `F` is amenable, Lemma 2.1 gives `EA(X)`, and `K ≤ F` is amenable.

**(T2), ⇐.** This is the imported item 3.

**(T2), ⇒.** If `F` is amenable, push its invariant mean forward along `g ↦ gK`; `K ≤ F` is amenable.

## Step 2. Items 2 and 3

**Item 2.** Suppose `F_1 ≤ K` with `F_1 ≅ F`. If `K` is amenable, so is `F_1 ≅ F`. Conversely `A` gives
`Amen(K)` by Step 1.

**Item 3.** If `Amen(K)` holds, Step 1 reads `A ⟺ P`.

## Step 3. Item 4

Suppose neither item 2 nor item 3 applies. Then `K` has no subgroup isomorphic to `F`, and `K` is not known
to be amenable. In particular `K` is not elementary amenable, since elementary amenable groups are amenable
and item 3 would apply. So `K ≤ F` is a subgroup that is neither elementary amenable nor contains `F`. That
is the statement of `some-subgroup-of-thompson-f-is-neither-ea-nor-contains-f`, and it is the negation of
`every-subgroup-of-thompson-f-is-ea-or-contains-f`.

Read as a dichotomy: if the Brin–Sapir conjecture holds, then every `K ≤ F` is elementary amenable (item 3)
or contains `F` (item 2).

## Step 4. Item 5

Let `K ≤ F` contain no copy of `F`. Let `m` be an invariant mean on `Ω = F/K`, with `t = m(Moved(c))`.

**`t = 1`.** Suppose `1 − t > 0`.
- Choose `F_0 ≅ F` inside `F'`, with a finite generating set `Q`.
- The set `S_Q = {H ∈ Sub(F) : Q ⊆ H}` contains every subgroup containing `F'`, so `μ_0(S_Q) = 1`.
- By the definition of the stabilizer IRS with `P = ∅`, `m({ω : Q ⊆ Stab(ω)}) = μ_Ω(S_Q) ≥ (1−t)·1 > 0`.
- So some `ω = hK` has `Q ⊆ Stab(ω) = hKh⁻¹`. Then `F_0 ≤ hKh⁻¹`, and `h⁻¹F_0h ≅ F` lies in `K`.
- This is a contradiction, so `t = 1`.

**Mean-free.** For `g ≠ e`, `m(Fix(g)) ≤ m(Fix(g) ∩ X) + m(Ω \ X) = 0 + (1 − t) = 0`.

**Not confined.** Every point of `F/K` has a stabilizer conjugate to `K`, and confinement is invariant under
conjugation. If `K` were confined, all of `F/K` would lie in `Ω_conf`, and by item 3 of
`thompson-f-mean-free-actions-dense-configurations-or-unconfined` we would have `m(Moved(c)) = 0`. That
contradicts `t = 1`.

**Sofic.** `F/K` is an `F`-set in which no point stabilizer is confined, and it carries a mean-free invariant
mean. This is shape (II) in item 2 of the same claim, and item 5 there gives that `F` is sofic.

This proves items 1–5. Every step is an imported statement or a line of group theory.
