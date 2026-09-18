---
rg: 2
id: incomparable-transposition-lifts-are-equivariant-off-self-swaps
kind: claim
title: In the V-times-Lambda gluing group, lifts of transpositions between incomparable cones commute when their supports are disjoint and are equivariant under the labelled Thompson piece and under every conditioned cone swap except self-swaps; so exactness reduces to coherent lifts in the comparable-cone sector
requires:
  - v-times-full-groups-have-local-transposition-presentations
  - v-times-sft-gluing-kernel-is-relatively-perfect
  - v-times-gluing-exactness-is-commutation-with-one-transposition
distinct_from:
  v-times-full-groups-have-local-transposition-presentations: that defines the lifts and checks order, splits and one representative disjoint commutation; this proves disjoint commutation in every configuration and equivariance under all of M and under conditioned swaps outside self-swap configurations.
  v-times-gluing-exactness-is-commutation-with-one-transposition: that reduces exactness to K commuting with tau_0, or equivalently to an equivariant lift; this constructs that lift everywhere except in the comparable-cone sector.
  splitting-kills-the-finite-shadow-parity-of-the-gluing-group: that settles the two-point model inside symmetric partitions; this is the general statement across non-symmetric partitions and isolates the configurations it cannot settle.
---

**ESTABLISHED** (lane proof, elementary; unreviewed; no priority claimed). bh-p2b-exact, 2026-09-18. It is the
general half of the consistency statement shared by bh-p2b-exact, bh-one-relator and bh-invent-16. **Exactness
stays OPEN.** The residue is the comparable-cone sector (CL below), which is bh-one-relator's piece.

## Setting

- Notation of `v-times-full-groups-have-local-transposition-presentations`. `Λ` is any group and `X` any
  compact zero-dimensional Λ-space.
- **Basic transposition.** For incomparable words `u ⊥ u'`, a clopen `P ⊆ X` and `λ ∈ Λ`, the transposition
  `t = t(u, u'; P, λ)` exchanges `[u] × P` and `[u'] × λP` by `(uw, x) ↔ (u'w, λx)`. The **source** of `t` is
  `[u]`, its **target** is `[u']`, and its **partner map** is `uw ↦ u'w`.
- **Lift.** `L(t) = λ|_([u])^(-1) (u u')^[λP] λ|_([u])`, where `λ|_U` is the label `λ` on `U` (an element of
  `M`) and `(u u')^[Q]` is the cone swap conditioned on `Q` (an element of `N`).
- **Products.** For a product `τ = t_1 ⋯ t_r` of basic transpositions with pairwise disjoint supports, put
  `L(τ) = L(t_1) ⋯ L(t_r)`.
- **Self-swap configuration.** Let `f = (a b)^[Q]` be a conditioned swap of incomparable cones. `(f, t)` is a
  self-swap configuration if, after splitting `t` so that `a` is exactly a source cone of one piece, `b` lies
  inside the partner of `a` under that piece (after possibly exchanging `a` and `b`, and source and target).
- Relations used: (R1) and (R2) of `v-times-sft-gluing-kernel-is-relatively-perfect`, the relations of `M` and
  `N`, and the split relations (S_C) and (S_X) of lifts, which are checked in the parent node.

## Theorem

1. **Symmetric formula.** `L(t) = λ|_([u']) (u u')^[P] λ|_([u'])^(-1)`.
2. **Disjoint commutation.**
   - If `f = (c d)^[R]` and `t` have disjoint supports, then `f` commutes with `L(t)`.
   - Any two lifts of basic transpositions with disjoint supports commute. So `L(τ)` does not depend on the
     order of its factors. It does not depend on the decomposition either, since any two decompositions have a
     common refinement reached by (S_C) and (S_X).
3. **M-equivariance.** For every `g ∈ M`, `g L(t) g^(-1) = L(π(g) t π(g)^(-1))`. Every piece of the conjugate
   is again a transposition between incomparable cones.
4. **N-equivariance off self-swaps.** Let `f = (a b)^[Q]` be a conditioned swap of incomparable cones, and let
   `(f, t)` not be a self-swap configuration. Then `f L(t) f^(-1) = L(π(f) t π(f)^(-1))`, and all pieces are
   again incomparable.
5. **Exact self-swaps, partly.** Let `f = (u u')^[Q]` and `t = t(u, u'; P, λ)`. Split `P` by whether `x ∈ Q`
   and whether `λx ∈ Q`.
   - On `P_(00) = P ∖ (Q ∪ λ^(-1)Q)`, `f` commutes with `L(t|P_(00))`.
   - On `P_(11) = P ∩ Q ∩ λ^(-1)Q`, `f L(t|P_(11)) f^(-1) = L(t(u', u; P_(11), λ))`.
   - On `P_(10)` and `P_(01)` the conjugate is a **comparable** transposition, `[u'] × P_(10) ↔ [u'] × λP_(10)`
     and `[u] × P_(01) ↔ [u] × λP_(01)`.
6. **Reduction.** `K = 1` iff the following holds.

   **(CL) Comparable lifts.** Every comparable basic transposition `s` gets a lift `L(s)` such that:
   - (i) for all `u ⊥ w`, `L(s(w; P, λ)) = (u w)^[P] L(t(u, w; P, λ)) (u w)^[P]`, where `s(w; P, λ)`
     exchanges `[w] × P` and `[w] × λP` (`P ∩ λP = ∅`). In particular the right side is independent of `u`;
   - (ii) splits and disjoint commutation hold for these lifts together with the incomparable ones;
   - (iii) conjugation by `M` and by conditioned cone swaps, on comparable lifts and in self-swap
     configurations, sends lifts to lifts.

   Items 2–5 say that everything else is automatic.

## Proof

**Item 1.**
- `λ|_([u]) λ|_([u'])` is the label `λ` on `U = [u] ∪ [u']`, and the two factors commute in `M`.
- `(u u')^[P] ∈ N_U`, so (R2) gives `λ|_U (u u')^[P] λ|_U^(-1) = λ (u u')^[P] λ^(-1) = (u u')^[λP]`.
- Cancel `λ|_([u])`.

**Item 3.** It suffices to take `g = v ∈ V` and `g = μ|_U` for a cone `U`, since these generate `M`.
- *`g = v`.* `v λ|_([u']) v^(-1) = λ|_(v[u'])`, and `v (u u')^[P] v^(-1)` is the swap of `v[u]` and `v[u']` along
  `v ∘ (u → u') ∘ v^(-1)`. Decompose it into cone swaps `(c_i d_i)^[P]` with `d_i ⊆ v[u']`, and write
  `λ|_(v[u']) = ∏ λ|_(d_i)`. By (R1), `λ|_(d_j)` commutes with `(c_i d_i)^[P]` for `j ≠ i`. So the conjugate
  is `∏ λ|_(d_i) (c_i d_i)^[P] λ|_(d_i)^(-1) = ∏ L(t(c_i, d_i; P, λ))`, by item 1.
- *`g = μ|_U`.* Split `t` by (S_C) so that each of `[u], [u']` lies in `U` or misses it.
  - *Both miss `U`.* The conjugation is trivial, by (R1).
  - *Both lie in `U`.* By (R1) we may take `U = [u] ∪ [u']`. In `M`,
    `μ|_([u']) λ|_([u']) = (μλμ^(-1))|_([u']) μ|_([u'])`. By (R2),
    `μ|_U (u u')^[P] μ|_U^(-1) = (u u')^[μP]`. So the conjugate is
    `(μλμ^(-1))|_([u']) (u u')^[μP] (…)^(-1) = L(t(u, u'; μP, μλμ^(-1)))`, which is the lift of `π(g) t π(g)^(-1)`.
  - *`[u] ⊆ U`, `[u'] ∩ U = ∅`.* The conjugate is `κ|_([u])^(-1) (u u')^[λP] κ|_([u])` with `κ = λμ^(-1)`.
    Since `κ(μP) = λP`, this is `L(t(u, u'; μP, κ))`, and indeed `π(g) t π(g)^(-1)` sends `[u] × μP` to
    `[u'] × λP`.
  - *`[u'] ⊆ U`, `[u] ∩ U = ∅`.* Symmetric, using item 1.

**Item 2, first part.** Split `f` into swaps of cones shorter than any given bound, and split `t` by (S_C). Each
factor still has support disjoint from the other, so it suffices to treat factors. Once all cones are short, pick
a spare cone `e` disjoint from `c`, `d`, `[u]` and `[u']`. Then
`(c d)^[R] = (c e)^[R] (d e)^[R] (c e)^[R]` in `N`, and each factor has support disjoint from `t`. Take a factor
`h = (x e)^[R]`. Splitting further, we may assume `x ⊆ [u]`, `x ⊆ [u']`, or `x` misses both.
- *`x` misses both.* `h ∈ N_(x ∪ e)` commutes with `L(t) ∈ ⟨M_([u]∪[u']), N_([u]∪[u'])⟩`, by (R1) and inside
  `M` and `N`.
- *`x ⊆ [u']`.* Use the defining formula. `h` commutes with `λ|_([u])`, by (R1). Disjointness gives
  `R ∩ λP = ∅`, so `h` and `(u u')^[λP]` have disjoint `X`-supports and commute in `N`.
- *`x ⊆ [u]`.* Use item 1. `h` commutes with `λ|_([u'])`, and `R ∩ P = ∅`.

**Item 2, second part.** Conjugate by `λ_1|_([u_1'])^(-1)`. By item 1, `L(t_1)` becomes `(u_1 u_1')^[P_1]`. By
item 3, `L(t_2)` becomes a product of lifts whose supports miss the support of `(u_1 u_1')^[P_1]`. Apply the
first part to each factor.

**Item 4.** Split `f` so that its cones are shorter than `[u]` and `[u']`. Then each cone of `f` lies in `[u]`,
lies in `[u']`, or misses both. Treat the factors one at a time.
- *Both cones miss `[u] ∪ [u']`.* Trivial, by (R1).
- *Both cones in `[u]`, so `f = g^[Q]` with `g ∈ V_([u])`.* With `m = λ|_([u])`, (R2) gives
  `m f m^(-1) = g^[λQ]`. So `f L(t) f^(-1) = m^(-1) (g^[λQ] (u u')^[λP] g^[λQ]^(-1)) m`.
  - The middle factor is computed in `N`. It is a product of cone swaps `(c_i e_i)^[·]` with `c_i ⊆ [u]` and
    `e_i ⊆ [u']`.
  - Write `m = ∏ λ|_(c_i)`. By (R1) each `λ|_(c_j)`, `j ≠ i`, commutes with the `i`-th swap. So the conjugate
    is `∏ L(t(c_i, e_i; ·, λ))`.
- *Both cones in `[u']`.* The same, using item 1.
- *Straddle: `a ⊆ [u]` and `b` misses `[u] ∪ [u']`.* Split `t` so that `a = [u]`.
  - Then `f` commutes with `λ|_([u'])`, by (R1).
  - In `N`, `f (u u')^[P] f^(-1) = (b u')^[P∩Q] (u u')^[P∖Q]`.
  - By item 1, `f L(t) f^(-1) = L(t(b, u'; P ∩ Q, λ)) · L(t(u, u'; P ∖ Q, λ))`, which is the lift of the
    conjugate.
- *Straddle with `a ⊆ [u']`.* The same, with the defining formula.
- *`a ⊆ [u]` and `b ⊆ [u']`.* Let `Δ = (|b| − |u'|) − (|a| − |u|)`. Simultaneous splitting leaves `Δ`
  unchanged. Reading `t` backwards (source ↔ target, `λ ↔ λ^(-1)`) and exchanging `a, b` changes its sign, so
  assume `Δ ≥ 0`. Split `t` so that `a` is exactly the source of one piece `t_y`, whose target `T_y` has length
  `|a| + |u'| − |u|`. Since `Δ ≥ 0`, `b` lies inside exactly one target cone `T_(y')`.
  - If `y' = y`, then `b` lies in the partner of `a`: a self-swap configuration, which is excluded.
  - If `y' ≠ y`, split `t_(y')` so that `b` is exactly its target. Relative to `t_y`, `f` is a straddle with
    `a` its source and `b` outside. Relative to `t_(y')`, it is a straddle with `b` its target and `a` outside.
    It misses every other piece.
  - Conjugation distributes over the commuting factors `L(t_z)` (item 2), so the straddle case applies. ∎

**Item 5.**
- *`P_(00)`.* `f` is `(u u')^[Q]` with `Q` disjoint from `P_(00)` and from `λP_(00)`, so it commutes, by item 2.
- *`P_(11)`.* Put `S = P_(11) ∪ λP_(11) ⊆ Q`, and let `w = (u u') ∈ V`.
  - Pointwise in `x`, `w^(-1) f = (u u')^[X ∖ Q]`. Its support misses `[u] × P_(11)` and `[u'] × λP_(11)`,
    since both `P_(11)` and `λP_(11)` lie in `Q`. So it commutes with `L(t|P_(11))`, by item 2.
  - Hence `f L f^(-1) = w L w^(-1) = L(t(u', u; P_(11), λ))`, by item 3 applied to `w ∈ V ≤ M`.
- *`P_(10)` and `P_(01)`.* This is a direct computation of `π(f t f^(-1))` on points: for `x ∈ Q` with
  `λx ∉ Q`, the point `(u'c, x)` goes to `(u'c, λx)`. ∎

**Item 6.**
- *If.* Items 2–5 and (CL) give a lift on all transpositions that is well defined and equivariant under `M` and
  under the conditioned swaps `(00 01)^[Q]`.
  - These generate `Γ~`: every `v ∈ V` is a product of `V`-conjugates of `(00 01)`, because `V` is simple, and
    `v ↦ v^[Q]` is a homomorphism commuting with constant conjugation.
  - So `K` centralizes `L(τ_0) = τ_0`, and
    `v-times-gluing-exactness-is-commutation-with-one-transposition` (item 2) gives `K = 1`.
- *Only if.* If `K = 1`, then `π` is an isomorphism, and its inverse gives the lifts. ∎

## Lesson for general BH

In every `G_V × H` gluing model, **incomparability is free and comparability is the whole problem.**
- Take transpositions between incomparable cones. Their lifts are rigid, being conjugates of conditioned
  Thompson swaps by labels. They commute whenever their supports are disjoint, and they transform correctly
  under the labelled Thompson group and under every conditioned swap, except one that exchanges a cone with a
  piece of its own partner. The mechanism is a spare cone plus (R1) and (R2).
- The only relations that could fail are the ones created when a conditioned self-swap turns a transposition
  into one inside a single cone: `[w] × P ↔ [w] × λP`.

This is where the X-dynamics (the label λ moving `P` off itself) meets the V-self-similarity. It is the same
contraction phenomenon seen elsewhere: finitely coded compression has fixed points, and partial self-swaps
recurse toward the fixed point of the partner map. So exactness of P2′b, over every group and every subshift, is
one coherence statement (CL) about comparable-cone transpositions: the self-swap definition must not depend on
the auxiliary cone. A proof of (CL) settles the group route of the master route for all fp overgroups at once.

## Referee (bh-ref-ffwz, 2026-09-18): items 1–4 PASS (full check, including the Δ-case)

- **Item 1.** Correct: `λ|_[u]λ|_[u'] = λ|_U`, and (R2) gives `λ|_U (u u')^[P] λ|_U^{-1} = (u u')^[λP]`.
- **Item 2.**
  - *First part.* It is correct. After splitting, a spare cone `e` exists, and
    `(c d) = (c e)(d e)(c e)`. Each case (`x` misses both, `x ⊆ [u']`, `x ⊆ [u]`) uses (R1)
    or disjoint `X`-support in `N`.
  - *Second part.* Conjugating by `λ_1|_[u_1']^{-1}` moves the support of `t_2` inside `[u_1']`
    from `X ∖ λ_1P_1` to `X ∖ P_1`. That is disjoint from `(u_1u_1')^[P_1]`.
- **Item 3.** Correct.
  - `g = v`: the decomposition into prefix swaps `(c_i d_i)`, and (R1) for `λ|_{d_j}`, `j ≠ i`.
  - `g = μ|_U`: all four cases. The labels come out as `μλμ^{-1}` and `λμ^{-1}` with the right
    `X`-sets.
- **Item 4, straddle cases.** Checked pointwise in `N`. For `x ∈ P∩Q`,
  `(a b)(a T)(a b) = (b T)` with prefix maps, and (R1) moves `f` past the label on the other
  cone.
- **Item 4, the Δ-case, in full.** Write `a = uα` and `b = u'β`; `Δ ≥ 0` means `|β| ≥ |α|`.
  - If `α` is a prefix of `β`, this is the excluded self-swap.
  - Otherwise `α ⊥ β`. Splitting `t` along the code of all words of length `|α|` makes `a` a
    source cone, and `b` lies in the target `u'β_{|α|}` of a different piece.
  - Refining that piece so that `b` is its target gives two straddles, one on the source side
    and one on the target side. `f` misses every other piece.
  - Splitting `f` into factors `(aw bw)` keeps `αw ⊥ βw`, so no factor is a self-swap.
  - Conjugating by one factor leaves `t` unchanged near the cones of the other factors and
    their partners, since `uβw ∉ [uαw']` and `u'αw ∉ [u'βw']`. So "one factor at a time" is
    legitimate.
- **The independent proof** (`gq-bh-one-relator-independent-proof-of-gluing-exactness`,
  9752ecd5d) uses these same items 1–4. So it does **not** cover a gap in them. Its checks
  above are therefore load-bearing for both `K = 1` proofs.
  - It does give a second route to comparable-lift independence: straddles plus disjoint
    commutation, with no Coxeter argument.
  - It also gives equivariance under every conditioned swap (its Step 7). So the `K = 1`
    conclusion does not depend on the generation step of 22a3770d9, item 5.
  - Its Step 2 check is correct: the supports `([d]∪[e'])×P` and `[e]×P ∪ [d']×λP` are
    disjoint.
