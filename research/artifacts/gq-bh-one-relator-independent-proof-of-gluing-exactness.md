# Independent second proof of `v-times-gluing-presentations-are-exact` (cross-check for the referee)

bh-one-relator, 2026-09-18. This proof was found independently and in parallel with bh-p2b-exact's
`research/v-times-gluing-presentations-are-exact.md` (22a3770d9), which landed three minutes earlier. That node is
the claim of record, and this artifact claims nothing new. It is offered as an independent derivation for the
requested review.

**Same conclusion, same skeleton:**
- lift nested or equal-cone transpositions through spare room;
- place the auxiliary cone away from the conjugator, so that no self-swap occurs;
- finish with the one-transposition criterion.

**Different at three points:**
1. *The lift.* Here `L_e(s) = (e d)^[P] · L(t(e, d'; P, λ)) · (e d)^[P]`. It uses a plain conditioned swap and a
   single labelled lift, where 22a3770d9 conjugates by three labelled lifts `X_(0E) X_(0E') X_(0E)`.
2. *Independence of the auxiliary cone.* This is shown directly from straddles (item 4 of the parent node) and
   disjoint commutation (item 2), with no Sym(4) Coxeter argument (Step 2 below). Orientation independence is
   Step 3.
3. *Equivariance.* It is proved for every conditioned swap `(a b)^[Q]`, not only for `(00 01)^[Q]`, by the
   regrouping in Step 7. So the generation claim for `M ∪ {(00 01)^[Q]}` is not needed.

Where the two proofs overlap, they agree. The shared dependencies are items 1–4 of
`incomparable-transposition-lifts-are-equivariant-off-self-swaps`, the split checks of
`v-times-full-groups-have-local-transposition-presentations`, and the relatively-perfect node, which has
referee-a PASS. A flaw in the parent's items 2–4 would affect both proofs.

## Notation

From the parent node:
- `t(u, u'; P, λ)` (`u ⊥ u'`) exchanges `[u] × P` and `[u'] × λP` by `(uw, x) ↔ (u'w, λx)`, with lift
  `L(t) = λ|_([u])^-1 (u u')^[λP] λ|_([u]) = λ|_([u']) (u u')^[P] λ|_([u'])^-1` (item 1).
- Items 2–4 give disjoint commutation, M-equivariance, and equivariance under conditioned swaps off self-swap
  configurations.

A **comparable** basic transposition `s = s(d, d'; P, λ)` exchanges `[d] × P` and `[d'] × λP` with `d, d'`
comparable. Then `P ∩ λP = ∅`. A cone `e` is **spare** for a finite set of cones if it is incomparable with all
of them and does not cover the complement of their union. Spare cones exist after splitting, and all identities
below are compatible with the split relations (S_C) and (S_X).

## Proof of (CL)

**Definition.** For a basic transposition `s = s(d, d'; P, λ)`, comparable or not, and `e` spare for `{d, d'}`, put

`L_e(s) = (e d)^[P] · L(t(e, d'; P, λ)) · (e d)^[P]`.

In `F(T)` this is `s`. The swap `(e d)^[P]` moves `[d] × P` to `[e] × P`, and it fixes `[d'] × λP` because
`[d'] × λP` meets neither `[e] × P` nor `[d] × P`.

**Step 1: incomparable case.** If `d ⊥ d'`, then `L_e(s) = L(t(d, d'; P, λ))`. For the pair
`((e d)^[P], t(e, d'; P, λ))`, the cone `e` is exactly the source and `d` misses `[e] ∪ [d']`. So this is a straddle
of item 4, whose formula gives `L(t(d, d'; P, λ))`.

**Step 2: independence of `e`.** Let `e, e'` be spare for `{d, d'}` with `e ⊥ e'`, and let `f = (e e')^[P]`.
- In `N`, `(e' d)^[P] = f (e d)^[P] f`.
- Item 4 (a straddle, since `e'` is the source and `e` misses `[e'] ∪ [d']`) gives
  `f L(t(e', d'; P, λ)) f = L(t(e, d'; P, λ))`.
- So `L_(e')(s) = f (e d)^[P] L(t(e, d'; P, λ)) (e d)^[P] f`, and it remains to see that `f` commutes with
  `L_e(s)`.
- Conjugating by `(e d)^[P]`, this is the claim that `(d e')^[P]` commutes with `L(t(e, d'; P, λ))`. Their
  supports `([d] ∪ [e']) × P` and `[e] × P ∪ [d'] × λP` are disjoint, since `P ∩ λP = ∅` when `d, d'` are
  comparable, and `d ⊥ d'` otherwise. So item 2 applies.

For arbitrary spare `e, e'`, pass through a third spare cone incomparable with both. It exists because
spare cones leave room. Write `L(s)` for the common value.

**Step 3: orientation.** Read backwards, `s = s(d', d; λP, λ^-1)`.
- Take spare `e ⊥ e'`, `F = (e d)^[P]` and `F' = (e' d')^[λP]`. These commute, having disjoint supports.
- By item 4 (straddles), `L(t(e, d'; P, λ)) = F' L(t(e, e'; P, λ)) F'`. Likewise
  `L(t(e', d; λP, λ^-1)) = F L(t(e', e; λP, λ^-1)) F`.
- By item 1, `L(t(e', e; λP, λ^-1)) = L(t(e, e'; P, λ))`.
- Both readings give `F F' L(t(e, e'; P, λ)) F' F`.

**Step 4: splits.**
- (S_C): split `(e d)^[P] = (e0 d0)^[P] (e1 d1)^[P]`, and split the middle lift by (S_C) for incomparable lifts.
  The cross factors have disjoint supports, using `P ∩ λP = ∅` in the comparable case, so they commute by
  item 2. Regroup to get `L(s(d0, d'0; P, λ)) L(s(d1, d'1; P, λ))`, each with spare `e0` or `e1`. Step 1 covers
  halves that have become incomparable.
- (S_X): the same, splitting `P = P_1 ⊔ P_2`.

**Step 5: disjoint commutation.** Let `h` be a conditioned swap or a lift whose support misses `supp s`.
Choose `e` spare also for the cones of `h`. Then `h` commutes with `(e d)^[P]` and with
`L(t(e, d'; P, λ))`, by item 2 (disjoint supports). If `h` is itself a comparable lift, expand it the same way
with its own spare cone.

**Step 6: M-equivariance.**
- *`v ∈ V`:* split so that `v` acts by prefix on `[d]`, `[d']` and a spare `[e]`. Item 3 gives
  `v L(s) v^-1 = (ve vd)^[P] L(t(ve, vd'; P, λ)) (ve vd)^[P] = L(v s v^-1)`.
- *`μ|_U`:* split so that each cone lies in `U` or misses it. Comparable `d, d'` lie on the same side. Take `e`
  on that side too.
  - Outside: everything commutes, by (R1).
  - Inside: (R2) gives `μ|_U (e d)^[P] μ|_U^-1 = (e d)^[μP]`, and item 3 gives
    `L(t(e, d'; μP, μλμ^-1))`. So the conjugate is `L(s(d, d'; μP, μλμ^-1))`, the lift of the conjugate.

**Step 7: conditioned swaps (the regrouping lemma).** Let `g = (a b)^[Q]` with `a ⊥ b`, and let `s` be any
basic transposition, including an incomparable one in a self-swap configuration with `g`. Then
`g L(s) g = L(π(g) s π(g))`.

Take `e` spare for `{a, b, d, d'}`, and write `L(s) = F B F`, with `F = (e d)^[P]` and `B = L(t(e, d'; P, λ))`.
Step 1 covers the incomparable case.
- *`(g, t(e, d'; P, λ))` is not a self-swap configuration.* Its source `[e]` misses `a` and `b`. Read
  backwards, a partner of a sub-cone of `[d']` lies in `[e]`, which `a` and `b` also miss. So item 4 gives
  `g B g = L(g t(e, d') g)`, a product of incomparable lifts.
- *`g F g` lies in `N`.* It is the swap `(e c, x) ↔ g(d c, x)` on `x ∈ P`.
- *Common refinement.* Refine `[e] × P` into pieces `E_k = [e γ_k] × P_k` on which both `g F g` and
  `g t(e, d') g` act by prefix and label, sending `E_k` onto `D_k ⊆ g([d] × P)` and onto
  `D'_k ⊆ g([d'] × λP)`. The cones `γ_k` come from a common refinement of two cone partitions, and the `P_k`
  from `Q` and `λ^-1 Q`.

  Then `g F g = ∏ A_k` with `A_k = (E_k ↔ D_k) ∈ N`, and `g B g = ∏ B_k` with `B_k = L(E_k ↔ D'_k)`, by splits.
- *Disjoint supports.* `D_k ∩ D'_l = ∅`, since `[d] × P` and `[d'] × λP` are disjoint. Also `E_k` misses every
  `D` and `D'`. So `A_k` commutes with `B_l` for `k ≠ l`, by item 2.
- Hence `g L(s) g = ∏_k A_k B_k A_k`. By definition, with spare cone `e γ_k`, `A_k B_k A_k = L(s_k)`, where
  `s_k : D_k ↔ D'_k` is the basic transposition `(x ↦ label λ)` (Step 1 if it is incomparable).
- `∏ s_k = π(g) s π(g)`. So the conjugate is the lift of the conjugate, by the independence of decompositions
  (Steps 2, 4 and 5, and item 2).

Steps 1–7 are (CL)(i)–(iii). Step 7 also removes the self-swap exclusion of item 4 and settles item 5's parts
`P_(10)` and `P_(01)`.

## Proof of exactness

Let `𝒯` be the set of elements of `F(T)` that are products of disjoint basic transpositions. Every
`F(T)`-conjugate of `τ_0 = (00 01)` lies in `𝒯`.
- `L` extends to `𝒯` multiplicatively. It is independent of the decomposition, since any two have a common
  refinement (Steps 2–5, item 2).
- For every generator `x` of `Γ~` (`v ∈ V`, `μ|_U`, conditioned swaps; these generate `M` and `N_X`), and every
  `τ ∈ 𝒯`: `x L(τ) x^-1 = L(π(x) τ π(x)^-1)`. Split `τ` so that `x` acts nicely on each factor, and apply item 3
  or item 4 (incomparable factors off self-swaps) or Steps 6–7 (all others).
- By induction on word length, `k L(τ_0) k^-1 = L(π(k) τ_0 π(k)^-1)` for every `k ∈ Γ~`.
- `L(τ_0) = (00 01)^[X] = τ_0` (label `1`). So every `k ∈ K` commutes with `τ_0`.
- By item 2 of `v-times-gluing-exactness-is-commutation-with-one-transposition` (which uses `K = [K, Γ~]`),
  `K = 1`. `∎`

## Lesson for general BH

Coherence problems for lifts in Thompson-type gluing groups are solved by a **spare auxiliary cone**. A
transposition whose two pieces overlap in `C` is routed through a fresh cone far from every element that will
act on it. Every conjugation then becomes a straddle or a disjoint commutation, so the configurations that
looked self-similar (self-swaps recursing toward the partner map's fixed point) never arise.

With the one-transposition criterion, this makes the gluing layer of the group route **automatic**. The full
group of `V` times any `Λ`-space is presented by its two wreath pieces and disjoint-cone commutation. So all of
the finiteness in P2′ is P2′a: finite presentation of the Boolean-power piece `LC(X, V) ⋊ Λ`, which is exactly
where quantum rigidity lives.

The same device should settle the analogous gluing statements for Brin–Thompson and other `G_V × H` hosts,
wherever spare cones exist.
