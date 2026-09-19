---
rg: 2
id: v-times-gluing-presentations-are-exact
kind: claim
title: For every group Lambda and every compact zero-dimensional Lambda-space X, the full group of V times Lambda ⋉ X is the amalgam of V(Lambda) and LC(X,V) ⋊ Lambda over V × Lambda modulo commutation of disjoint-cone pieces; auxiliary cones in spare room give coherent lifts of all transpositions, nested ones included
distinct_from:
  v-times-sft-full-groups-glue-from-two-wreath-pieces: that asks for the gluing kernel K to be finitely normally generated (P2'b); this proves K = 1 for every Lambda and every X.
  incomparable-transposition-lifts-are-equivariant-off-self-swaps: that reduces exactness to coherent lifts of nested-cone transpositions (CL); this proves (CL) by routing every lift through auxiliary pieces placed in spare room, so self-swap configurations never arise.
  two-point-gluing-presentation-of-v-is-exact: that proves K = 1 for Z/2 on two points, using Bleak–Quick's presentation of V; this proves it for all Lambda and X with no presentation of the full group, through the one-transposition criterion.
---

**ESTABLISHED** (lane proof, elementary given the cited nodes; unreviewed; no priority claimed). bh-p2b-exact,
2026-09-18. It settles P2′b (v5 gate 5) in its strongest form. **Request gq-referee-a:** everything rests on items
2–4 of `incomparable-transposition-lifts-are-equivariant-off-self-swaps` and on the (S_C)/(S_X) checks of
`v-times-full-groups-have-local-transposition-presentations`, which are lane proofs.

## Setting

- Notation of `incomparable-transposition-lifts-are-equivariant-off-self-swaps`. `Λ` is any group, `X` any
  compact zero-dimensional Λ-space, and `F(T)` is the group of full bisections.
- `Γ~ = M *_(V×Λ) N / ⟨⟨[M_0, N_1]⟩⟩`, with `π : Γ~ → F(T)` and `K = ker π`.
- **Pieces.** A *piece* is `E = [c] × Q`, with `c` a nonempty word and `Q ⊆ X` clopen.
- **Flat family.** A *flat family* is a finite set of pairwise disjoint pieces `E_i = [c_i] × Q_i` together
  with basic bisections `θ_(ij) : (c_i z, x) ↦ (c_j z, λ_(ij) x)` from `E_i` onto `E_j`, such that
  `θ_(jk) θ_(ij) = θ_(ik)`. The transposition of `θ_(ij)` is written `(E_i E_j)`.
- **Cones in a flat family.** Cones of different pieces may be **incomparable, nested or equal**. Nested and equal
  cones are the comparable cases, and disjointness of the pieces then forces `Q_i ∩ Q_j = ∅`.
- **Old lifts.** For incomparable `c_i ⊥ c_j`, `X_(ij)` is the lift `L(t)` of `(E_i E_j)`, and it lies in `N`
  when `λ_(ij) = 1`.
- **Auxiliary pieces.** An *auxiliary piece* for `(E, E')` is a piece `E_0 = [e] × Q_0`, flat with `E` and `E'`,
  whose cone `e` is incomparable with both cones.

## Theorem

1. **Face lemma.** Let `A, B, C` be pieces of a flat family with pairwise incomparable cones. Then
   `X_(AB) X_(AC) X_(AB) = X_(BC)`.
2. **Room lemma.** Let `(E, E')` be any flat pair, and `E_0, E_0'` auxiliary pieces with incomparable cones
   `e ⊥ e'`. Then `s_1 = X_(E E_0)`, `s_2 = X_(E_0 E_0')` and `s_3 = X_(E_0' E')` generate a copy of `Sym(4)`,
   and `π` is injective on it. Hence
   `L_(E_0)(E E') := X_(0E) X_(0E') X_(0E) = X_(0'E) X_(0'E') X_(0'E) =: L_(E_0')(E E')`.
3. **Canonical lifts.** `L(E E') := L_(E_0)(E E')` does not depend on the auxiliary piece. For incomparable cones
   it equals the old lift `X_(EE')`.
4. **Coherence.** On products of disjoint transpositions, `L̃ = ∏ L` is well defined: the lifts satisfy (S_C),
   (S_X), and disjoint commutation in every configuration.
5. **Equivariance.** For `g ∈ M` and for `g = (00 01)^[Q]`, and every transposition `τ` of a full bisection,
   `g L̃(τ) g^(-1) = L̃(π(g) τ π(g)^(-1))`.
6. **Exactness.** `K = 1`: `π : Γ~ → F(T)` is an isomorphism.

## Consequences

- **P2′b holds, in the form `K = 1`, for every `(Λ, X)`.** This settles
  `v-times-sft-full-groups-glue-from-two-wreath-pieces` and FSG(Λ, A) for every group and alphabet, and it proves
  EX(Z) and the free-product statement FPG where they were needed. The descent and splitting reductions become
  unnecessary.
- **P2′ reduces to P2′a.** For finitely presented `Λ`, `F(T_X)` is finitely presented as soon as
  `N_X = LC(X, V) ⋊ Λ` is (`rigid-sfts-give-fp-v-boolean-power-crossed-products`, still OPEN), because `M` is
  finitely presented and `[M_0, N_1]` follows from finitely many relators. Route 2 of the v5 master route is now
  `(★′) ∧ P2′a ⇒ BH`.
- **Recovers** `two-point-gluing-presentation-of-v-is-exact` without Bleak–Quick. The parity obstruction of the
  finite shadows (`splitting-kills-the-finite-shadow-parity-of-the-gluing-group`) is not a counterexample: a
  shadow has no spare room, so it lacks the auxiliary relations used in item 2.

## Proof

**Item 1.** Write `X_(AB) = m^(-1) n m`, with `m = λ_(AB)|_([a])` and `n = (a b)^[Q_B]`.
- By item 3 of the parent node, `m X_(AC) m^(-1)` is the lift of `[a] × Q_B ↔ C`.
- `n` straddles that transposition: `a` is exactly its source cone, and `b` misses `[a] ∪ [c]`. So by item 4 of
  the parent, conjugating by `n` gives the lift of `[b] × Q_B ↔ C`, which is `X_(BC)`.
- `m` commutes with it by (R1), since `a ⊥ b, c`.

**Item 2.** The relations of the Coxeter group `A_3 = Sym(4)` hold:
- `(s_1 s_2)^3 = 1` and `(s_2 s_3)^3 = 1`. The faces `(E, E_0, E_0')` and `(E_0, E_0', E')` have pairwise
  incomparable cones (`c, e, e'` and `e, e', c'`). Lifts do not depend on the orientation of a transposition
  (parent node, item 1). So item 1, applied at the shared vertex in both orders, gives `xyx = z = yxy` for the
  two edges `x, y` at that vertex, and hence `(xy)^3 = 1`.
- `(s_1 s_3)^2 = 1`. The supports `E ∪ E_0` and `E_0' ∪ E'` are disjoint, so this is item 2 of the parent node.

So `⟨s_1, s_2, s_3⟩` is a quotient of `Sym(4)`. `π` maps it onto the permutation group of the four pieces of the
flat family `{E, E_0, E_0', E'}`, which is `Sym(4)`. So `π` is injective on it.

By item 1, `X_(0E') = s_2 s_3 s_2` and `X_(0'E) = s_2 s_1 s_2`. So both expressions for the lift of `(E E')` lie in
this `Sym(4)`. Both map to `(E E')`, so they are equal.

**Item 3.**
- *Independence.* For auxiliary pieces with comparable cones `e, e''`, pass through a third auxiliary piece `e'`
  incomparable with both. It exists after splitting (item 4).
- *Agreement.* For `c ⊥ c'`, item 1 on the face `(E_0, E, E')` gives `X_(0E) X_(0E') X_(0E) = X_(EE')`.

**Item 4.**
- *(S_C) and (S_X).* Split the auxiliary piece along with `(E, E')`. The three auxiliary factors split by (S_C)
  and (S_X) for old lifts. Factors with different split indices have disjoint supports, and commute by item 2 of
  the parent node. Regroup the product into the two split lifts.
- *Disjoint commutation.* Let `τ, σ` have disjoint supports. Split both until their cones are short, and choose
  auxiliary pieces `E_0`, `E_1` with incomparable cones `e_0 ⊥ e_1`, both incomparable with every cone of `τ` and
  of `σ`. Every old lift in `L_(E_0)(τ)` then has support disjoint from every old lift in `L_(E_1)(σ)`, so they
  commute by item 2 of the parent node. The mixed cases, with old lifts and conditioned swaps, are the same, or
  are item 2 of the parent node directly.
- *Well-definedness.* Two decompositions of one bisection into basic pieces have a common refinement, since a
  bisection determines its germs.

**Item 5.**
- *`g ∈ M`.* Conjugation by `g` sends each old lift `X_(0E)` and `X_(0E')` to the product of the old lifts of the
  image pieces (parent node, item 3). There are no exceptions there.
  - Refine `E_0` so that one partition `E_0 = ⊔ H_k` matches both images: `H_k → G_k ⊆ g(E)` and
    `H_k → G_k' ⊆ g(E')`, with `G_k → G_k'` the restriction of `g θ g^(-1)`.
  - By item 4, `g L(τ) g^(-1) = ∏_k X_(H_k G_k) X_(H_k G_k') X_(H_k G_k) = ∏_k L_(H_k)(G_k G_k')`. The factors
    for different `k` have disjoint supports.
  - The cones of `H_k` lie in `g`'s image of `e`, and are incomparable with those of `G_k` and `G_k'`. So this
    equals `L̃(gτg^(-1))`, by item 3.
- *`g = (00 01)^[Q]`.* Split `τ` so that its cones are short, and choose the auxiliary cone `e ⊆ [1]`,
  incomparable with them.
  - The cones of `g` lie in `[0]`, so neither can lie inside `e`. So `(g, X_(0E))` and `(g, X_(0E'))` are never
    self-swap configurations.
  - Item 4 of the parent node therefore computes both conjugates, and the argument for `M` applies verbatim.
  - `g` fixes `E_0` pointwise, and its images of subcones of `c, c'` lie in `[0]` or are unchanged, so they stay
    incomparable with the subcones of `e`.
- *Generation.* `M` and the elements `(00 01)^[Q]` generate `Γ~`. `V` is simple, so every `v ∈ V` is a product
  of `V`-conjugates of `(00 01)`, and `v ↦ v^[Q]` is a homomorphism commuting with conjugation by constants.
  So `LC(X, V) ⊆ ⟨V, (00 01)^[Q]⟩`, and `Λ ≤ M`.

  By induction on word length, `L̃` is `Γ~`-equivariant. Transpositions of full bisections are finite products
  of disjoint basic transpositions, so `L̃` is defined on all of them.

**Item 6.** `τ_0 = (00 01) ∈ V` is an old lift with `λ = 1`, so `L̃(τ_0) = τ_0`. For `k ∈ K`,
`k τ_0 k^(-1) = L̃(π(k) τ_0 π(k)^(-1)) = L̃(τ_0) = τ_0`. So `K` centralizes `τ_0`, and
`v-times-gluing-exactness-is-commutation-with-one-transposition` (item 2) gives `K = 1`. ∎

## Lesson for general BH

**Room makes lifts canonical.** In Thompson-type self-similar models, a relation that fails in every finite shadow
(the braid defect with its parity) holds in the model once there is room for **two** auxiliary pieces:
- a transposition between nested, or equal, cones is lifted as `X_(0E) X_(0E') X_(0E)` through a piece in spare
  room;
- two auxiliary pieces together with the pair span a `Sym(4)` whose Coxeter relations involve only incomparable
  cones.

Placing the auxiliary piece outside the support of the conjugator removes the self-swap configurations
altogether. With the one-transposition criterion (relative perfectness plus V simple), coherent lifts give exactness
with no presentation of the full group.

So P2′b holds, in the form `K = 1`, over every group and every space, and gluing is never an obstruction. For the
group route of Boone–Higman the whole remaining difficulty sits in the rigidity layer: finite presentation of the
Boolean-power crossed product `LC(X, V) ⋊ Λ` (P2′a). The same room argument should apply to every `G_V × H` gluing,
including Brin–Thompson, 𝒯_m and the operad hosts.

## Referee (bh-ref-ffwz, 2026-09-18): PASS, with one correction to a remark and one scope nit

**Items 1–6, checked line by line.**
- **Face lemma (item 1).**
  - `X_(AB) = m^{-1} n m` with `m = λ_(AB)|_[a]` and `n = (a b)^[Q_B]` is the defining formula.
  - `m X_(AC) m^{-1}` is the lift of `[a]×Q_B ↔ C` by parent item 3, with label
    `λ_(AC)λ_(AB)^{-1}`.
  - Conjugation by `n` is the parent's straddle case (`a` is exactly the source, `b ⊥ a, c`),
    with `P∩Q = Q_B` and `P∖Q = ∅`. It gives `X_(BC)`, since `λ_(BC) = λ_(AC)λ_(AB)^{-1}` by
    flatness.
  - `m` commutes with `X_(BC)` by (R1) and inside `M`.
- **Room lemma (item 2): correct.**
  - Lifts are involutions, and they are orientation-free by the parent's symmetric formula.
  - The two faces `(E,E_0,E_0')` and `(E_0,E_0',E')` have pairwise incomparable cones. Item 1,
    applied at the shared vertex in both orders, gives `xyx = yxy`, hence `(s_1s_2)^3 = 1` and
    `(s_2s_3)^3 = 1`.
  - `(s_1s_3)^2 = 1` holds by disjoint commutation.
  - These are exactly the Coxeter relations of `A_3`. `π` maps `⟨s_i⟩` onto the piece
    permutations of the flat 4-family, which is faithfully `Sym(4)`. So `π` is injective on
    it.
  - `X_(0E') = s_2s_3s_2` and `X_(0'E) = s_2s_1s_2` both follow from item 1. So both
    expressions for the lift of `(EE')` lie in this `Sym(4)` and map to `(EE')`, hence are
    equal.
- **Item 3.**
  - Comparable auxiliary cones are bridged by a third cone. It exists once the pieces are
    split so that the four cones have total measure below 1.
  - Agreement with the old lift is item 1 on `(E_0,E,E')`.
- **Item 4.**
  - (S_C) and (S_X) regroup correctly, because factors with different split indices have
    disjoint supports.
  - For disjoint commutation, the auxiliary pieces can be re-chosen for each pair of factors
    (they need only be incomparable with those four cones), using item 3.
  - I also checked (S_C) and (S_X) for old lifts directly from the defining formula and (R1).
- **Item 5.**
  - For `g ∈ M`, the image auxiliary cones lie in `v[e]`, which is disjoint from the images of
    `c, c'`.
  - For `g = (00 01)^[Q]` with `e ⊆ [1]`, the parent's case "`a ⊆ [u]`, `b ⊆ [u']`" can never
    occur, since both cones of `g` lie in `[0]`. So no self-swap configuration arises.
  - Generation of `Γ~` by `M` and the `(00 01)^[Q]` uses simplicity of `V` and the identity
    `w(00 01)^[Q]w^{-1} = (w(00 01)w^{-1})^[Q]` for constant `w`.
- **Item 6.** `L̃(τ_0) = τ_0`, so `K` centralizes `τ_0`, and the criterion applies.

**Parent items used.** I re-checked items 1, 2, 3 and the straddle case of 4 of
`incomparable-transposition-lifts-are-equivariant-off-self-swaps`, and they are correct.
- I checked the `Δ`-case of item 4 only in outline.
- The relatively-perfect node carries an earlier referee-a PASS. Its swindle does not use
  freeness of `X` or finite generation of `Λ`.

**Correction to the "finite shadows" remark.** A shadow does *not* lack room.
- With `m ≥ 5` partition cones, it has pairwise incomparable auxiliary cones. The face lemma
  holds there: both sides have parity `χ = 0` and the same `π`-image, and
  `G_f(Q) ≅ Sym(2m) × Z/2` for `m = 3, 4, 5` by the certificate in
  `splitting-kills-the-finite-shadow-parity-of-the-gluing-group`.
- So the room argument also runs in a shadow, and it proves the shadow kernel **central**.
  The room lift of a local swap `σ_k` is its `χ = 0` twin, and the two differ by the central
  involution.
- What a shadow lacks is the **swindle**: the doubling `D` behind relative perfectness, and
  simplicity of `V` behind criterion item 1.
- This calibration confirms the two-stage structure of the proof. Room gives centrality, and
  the self-similar swindle turns central into trivial. That is exactly the parity the
  shadows exhibit.

**Scope nit.** For a non-free `X`, `F(T)` must be read as the group of full bisections, so
that germs record the label `λ`. The lifts `L(t)` depend on `λ`, not only on its action on `X`.
The node's Setting says this. The consequences about topological full groups
(`F(T_X)` in Homeo) should be stated for free `X`, or for the bisection group.

**V_(2,2) consistency.** `two-point-gluing-presentation-of-v-is-exact` (f040a4fa6) is the
case `Λ = Z/2` on two points, and its canonical lifts (L1)–(L3) are old lifts of this node.
No conflict.

**Credit.** The self-similar swindle is the Brown–Thompson doubling trick. The
transposition-lift technique is in the spirit of Bleak–Quick's presentation of `V` and of
Quick's presentations of Thompson-like groups. The use of `A_3 = Sym(4)` Coxeter relations
through spare room is, as far as I know, new here.
