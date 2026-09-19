---
rg: 2
id: mirror-extension-splits-over-free-finite-by-free-subgroups-proof
kind: route
title: Match fundamental domains of two free finite lifts by a partial isomorphism of the ergodic tail relation, get freeness from the null-coset lemma, and lift a graph of finite groups vertex by vertex along a maximal tree
target: mirror-extension-splits-over-free-finite-by-free-subgroups
requires:
  - bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift
  - mirror-lift-untwists-only-through-a-mirror-splitting
---

The notation is that of the target. [BL] means `bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift`,
and [UT] means `mirror-lift-untwists-only-through-a-mirror-splitting-proof`.

**Imported facts.**
* **(I1)** [BL] Theorem 1 gives two things. First, `1 -> [T_-] -> N_- -> Q -> 1` is exact. Second, if
  `f ∈ N_-` has `pi_-(f) != 1`, then `Fix(f)` is `mu_-`-null. The second is [UT] Section 1, "distinct cosets are at
  distance 1", applied to `f` and `1`.
* **(I2)** `Ê_-` normalizes `[T_-]`. Each `g ∈ Ê_-` is a finite-band matrix plus a finite matrix, so it maps
  `V_fin^-` into itself and preserves `T_-` ([BL] Setup).
* **(I3)** The tail relation `T_-` on `X_- = (F_2^n)^N` with the product (Haar) measure is ergodic. A `T_-`-invariant
  Borel set is a tail event of an i.i.d. sequence, so it is null or conull by Kolmogorov's 0-1 law.
* **(I4)** (Partial isomorphisms; Kechris--Miller, *Topics in orbit equivalence*, LNM 1852, Lemma 7.10.) If `T` is an
  ergodic p.m.p. countable Borel equivalence relation and `A, B` are Borel sets with `mu(A) = mu(B)`, then there is a
  `theta ∈ [[T]]` with domain `A` and range `B`, up to null sets.
  * *Proof sketch.* Write `T` as the union of the graphs of a countable group `{g_i}` (Feldman--Moore).
  * Define `theta` greedily: on `A_1 = A ∩ g_1^(-1) B` set `theta = g_1`, then remove `A_1` from `A` and `g_1 A_1`
    from `B`, and continue through an enumeration in which each `g_i` recurs infinitely often.
  * If positive-measure leftovers `A_∞, B_∞` remained, ergodicity would give some `i` with
    `mu(g_i A_∞ ∩ B_∞) > 0`. But `g_i` recurs infinitely often, so this contradicts the construction.

## 1. Conjugacy of finite lifts (Theorem part 1)

Let `T`, `F`, `alpha'`, `alpha''` be as in part 1. Discard an invariant null set, so that both actions are free
everywhere and all the identities below hold everywhere.

**Fundamental domains.** Fix a Borel linear order `<` on `X`.
* Put `A' = {x : x < alpha'(f) x for all f != 1}`, and define `A''` in the same way for `alpha''`.
* Both are Borel. Since the actions are free, `A'` meets every `alpha'`-orbit in exactly one point, so
  `X = ⊔_(f ∈ F) alpha'(f) A'`.
* Each `alpha'(f)` preserves `mu`, so `mu(A') = 1/|F|`. Likewise `mu(A'') = 1/|F|`.

**The matching.** By (I4) there is a `theta ∈ [[T]]` with domain `A'` and range `A''`. Define `s : X -> X` by

`s(alpha'(f) a) = alpha''(f) theta(a)`, for `a ∈ A'` and `f ∈ F`.

This makes sense because each point of `X` is uniquely of the form `alpha'(f) a`.

**`s` is a measure-preserving bijection.**
* On the piece `alpha'(f) A'`, `s` equals `alpha''(f) theta alpha'(f)^(-1)`, a composition of measure-preserving
  partial bijections.
* The images `alpha''(f) A''` are disjoint and cover `X`.

**`s ∈ [T]`.** Let `x = alpha'(f) a`, and write `k_f = alpha'(f)^(-1) alpha''(f) ∈ [T]`.
* `theta(a) T a`, because `theta ∈ [[T]]`.
* `alpha''(f) theta(a) = alpha'(f) k_f theta(a)`, and `k_f theta(a) T theta(a) T a`.
* `alpha'(f) ∈ N[T]` maps `T`-classes onto `T`-classes, so `alpha'(f) k_f theta(a) T alpha'(f) a = x`.

Hence `s(x) T x` for every `x`.

**`s` intertwines.** For `g ∈ F` and `x = alpha'(f) a`:

`s(alpha'(g) x) = s(alpha'(gf) a) = alpha''(gf) theta(a) = alpha''(g) alpha''(f) theta(a) = alpha''(g) s(x)`.

So `s alpha'(g) = alpha''(g) s`, that is, `alpha''(g) = s alpha'(g) s^(-1)`. ∎

*Remark.* Ergodicity of `T` is used only in (I4). Nothing is assumed about the displacement of `alpha'` or
`alpha''`. The conjugator `s` has unbounded displacement in general, because `theta` does.

## 2. Freeness is automatic (Theorem part 2)

Let `alpha : F -> N_-` lift the inclusion of a finite `F <= Q`. For `f != 1` we have `pi_-(alpha(f)) = f != 1`, so
`Fix(alpha(f))` is null by (I1). A finite union of null sets is null, so `alpha` is essentially free. ∎

Note that (I1) is the null-coset lemma, applied through [UT] Section 1. Freeness therefore comes from the symbol:
the lift may be as point-dependent as one likes.

## 3. Splitting over graphs of finite groups (Theorem part 3)

**The key step (edge conjugacy).** Let `C` be a finite group, and let `beta_1, beta_2 : C -> N_-` be homomorphisms with
`pi_- o beta_1 = pi_- o beta_2`. Suppose this common map `C -> Q` is injective.
* Then `beta_1(c)^(-1) beta_2(c) ∈ ker pi_- = [T_-]` by (I1).
* Both are free by part 2, applied to the finite group `pi_-(beta_1(C)) ≅ C`.
* By part 1 and (I3), `beta_2 = s beta_1 s^(-1)` for some `s ∈ [T_-]`.

**The presentation.** Let `(Y, G_v, G_e)` be a finite graph of finite groups, with edge maps
`iota_e : G_e -> G_(o(e))` and `iota_(ebar) : G_e -> G_(t(e))`, and let `Y_0` be a maximal tree. Then
`Λ = π_1(Y, G_*, Y_0)` is generated by the `G_v` and by stable letters `t_e`, one for each geometric edge `e` not in
`Y_0`. The relations are:
* the relations of each `G_v`;
* `iota_e(c) = iota_(ebar)(c)` for each edge `e` of `Y_0` and each `c ∈ G_e`;
* `t_e iota_e(c) t_e^(-1) = iota_(ebar)(c)` for each edge `e` outside `Y_0` and each `c ∈ G_e`.

This is Serre, *Trees*, Section I.5.1. Let `rho : Λ -> Q` be injective on every vertex group, with each `rho|G_v`
liftable.

**Vertex lifts along the tree.** Choose a root `v_0` and a lift `alpha_(v_0)` of `rho|G_(v_0)`. Go through the tree in
breadth-first order. Suppose `alpha_v` has been fixed and `e` is a tree edge from `v` to a new vertex `w`.
* Take any lift `alpha_w^0` of `rho|G_w`.
* The two homomorphisms `alpha_v o iota_e` and `alpha_w^0 o iota_(ebar) : G_e -> N_-` both lie over
  `rho o iota_e = rho o iota_(ebar)`, and that map is injective because `rho` is injective on `G_v`.
* By the key step there is `s_e ∈ [T_-]` with `alpha_v o iota_e = s_e (alpha_w^0 o iota_(ebar)) s_e^(-1)`.
* Put `alpha_w = s_e alpha_w^0 s_e^(-1)`. It is again a lift of `rho|G_w`, since `pi_-(s_e) = 1`.

A tree has no cycles, so every tree relation holds and no choice is revisited.

**Stable letters.** For an edge `e ∉ Y_0` from `v` to `w`, take any `g ∈ N_-` with `pi_-(g) = rho(t_e)`.
* Put `beta_1 = alpha_w o iota_(ebar)` and `beta_2(c) = g alpha_v(iota_e(c)) g^(-1)`.
* Both lie over `rho o iota_(ebar)`, because `rho(t_e) rho(iota_e c) rho(t_e)^(-1) = rho(iota_(ebar) c)`.
* By the key step, `beta_1 = s beta_2 s^(-1)` with `s ∈ [T_-]`. Put `g_e = s g`. Then
  `g_e alpha_v(iota_e c) g_e^(-1) = alpha_w(iota_(ebar) c)`, and `pi_-(g_e) = rho(t_e)`.

**Conclusion.** Sending `G_v` through `alpha_v` and `t_e` to `g_e` respects every defining relation, so it defines a
homomorphism `rho~ : Λ -> N_-`. It agrees with `rho` after `pi_-` on the generators, hence everywhere.

**Subgroups.** A finitely generated virtually free group is the fundamental group of a finite graph of finite groups
(Karrass--Pietrowski--Solitar; Serre, *Trees*, II.2.6). Its vertex groups are finite subgroups. For
`Λ <= Q` with inclusion `rho`, the hypotheses are exactly "the vertex groups lift". So (HS) holds over `Λ`. ∎

*Special cases.*
* `F x| Λ_0` with `Λ_0` free on `q_1, ..., q_m` is the graph with one vertex `F` and `m` loops, each with edge group
  `F`. The edge maps are `id` and the automorphism `c -> q_i c q_i^(-1)`.
* `F x Z` is the case `m = 1` with the trivial automorphism.

## 4. The named test (Theorem part 4)

**Linear lifts of the finite groups used.**
* *Root subgroups.* Let `ell : A -> J` be any `F_2`-linear section of the symbol `J -> A`, for example monomials sent
  to powers of the two Jacobson generators, in whatever orientation the mirror convention of [BL] uses.
  * Since `x_12(b) x_12(c) = x_12(b + c)` in `EL_n(J)`, the map `a -> x_12(ell(a))` is a homomorphism
    `X_12(A) -> E_-` lifting the inclusion. Each `x_12(ell(a))` is an involution.
  * Composing with the dualization `M -> (xi -> xi o M^(-1))`, which is a homomorphism `E_- -> Ê_-`, gives a lift into
    `Ê_- <= N_-`. So every finite `x_12(W)`, and indeed all of `X_12(A)`, lifts. The same holds for every root
    subgroup `X_ij(A)`.
* *Constants.* `g -> g ⊗ 1` (the block-constant matrix, with entries in `F_2 ⊂ J`) lifts `SL_n(F_2) <= Q` to `E_-`.

**The pair.** Let `a != 0` and `h ∈ C_Q(u_a)`. Apply part 3 to `Λ = <u_a> x Z` (one vertex `<u_a> ≅ Z/2`, one loop,
trivial edge automorphism) and `rho(u_a, m) = u_a h^m`. Here `rho` is injective on the vertex group.
* Keep `alpha(u_a) = u~ = x_12(ell(a))`, dualized.
* The stable letter is sent to `h' = s h~`. Here `h~` is any lift of `h`, and `s ∈ [T_-]` satisfies
  `s (h~ u~ h~^(-1)) s^(-1) = u~`. Such an `s` exists by part 1, applied to the two free involutions `h~ u~ h~^(-1)`
  and `u~`. They lie in the same `[T_-]`-coset, because both have symbol `u_a` (as `h` commutes with `u_a`), so (I1)
  applies.

Then `h' u~ h'^(-1) = u~`. Since `[T_-]` is normal in `N_-`, `h' ∈ [T_-] h~ = h~ [T_-]`. So the involution may even be
taken **linear** (`u' = u~`), with only `h~` corrected. ∎

*Unpacked, for the reader of `jacobson-symbol-sequence-does-not-virtually-split`.*
Write `v = h~ u~ h~^(-1)`.
* `A = {x < v x}` is a fundamental domain for `v`, and `B = {x < u~ x}` is one for `u~`. Each has measure `1/2`.
* `theta ∈ [[T_-]]` maps `A` onto `B` (I4).
* Put `s = theta` on `A` and `s = u~ theta v` on `v A`.

Then `s ∈ [T_-]`, `s v s^(-1) = u~`, and `h' = s h~` commutes with `u~`.

No finite-dimensional bookkeeping survives, and the Fredholm index `-k` of `h~^k` on the image layer is simply
not an invariant of the coset `h~^k [T_-]`.

## 5. Locally finite subgroups and the finite Steinberg test (supplement, proved)

**(LF) Locally finite subgroups.** Let `Λ = ∪_m F_m <= Q` be an increasing union of finite subgroups, each of which
lifts to `N_-`. Then `Λ` lifts.
* Let `alpha_1` lift `F_1`. Given `alpha_m`, take any lift `alpha^0` of `F_(m+1)`.
* By the key step of Section 3, `alpha_m = s alpha^0|_(F_m) s^(-1)` for some `s ∈ [T_-]`.
* Put `alpha_(m+1) = s alpha^0 s^(-1)`. It extends `alpha_m` exactly.
* The union of the `alpha_m` is a homomorphism `Λ -> N_-`.

No limit of conjugators is taken, so no convergence question arises. In particular every root subgroup `X_ij(A)`
lifts; it even lifts linearly, by Section 4.

**The finite Steinberg test lifts linearly.** The Steinberg relator
`rho_- = [x_12(T), x_23(S)] x_13(1)^(-1)` of `jacobson-haar-relation-lifts-into-bilateral-relation` has a finite
shadow in `Q`, namely the group

`F_St = < x_12(1), x_12(x), x_23(1), x_23(x^(-1)) > <= UT_3(A)`.

In `UT_3` over a ring of characteristic 2, `x_12(b) x_23(c) = x_23(c) x_12(b) x_13(bc)`, with `x_13` central. So
`F_St = { x_12(b) x_23(c) x_13(d) : b ∈ <1, x>, c ∈ <1, x^(-1)>, d ∈ <1, x, x^(-1)> }`, which has order `2^7`. It
contains the relation `[x_12(1), x_23(1)] = [x_12(x), x_23(x^(-1))]`.

Let `p, q ∈ J` be the elementary lifts of `x, x^(-1)`, and put `e = pq`. This is a lift of `1`: it equals `1` or
`1 - P_0`, depending on orientation. Take the lifts
`x_12(1), x_12(p), x_23(e), x_23(q)`.
* They generate `G~ = { x_12(b) x_23(c) x_13(d) : b ∈ <1, p>, c ∈ <e, q>, d ∈ <e, q, pe> }`, because
  `1·e = e`, `1·q = q`, `p·e = pe` and `p·q = e`.
* The symbols of `e, q, pe` are `1, x^(-1), x`, which are independent. So `|G~| = 2^7`, and the symbol maps `G~` onto
  `F_St` bijectively.
* The inverse is a homomorphic lift `F_St -> E_-`.

So the Steinberg defect is absorbed at the finite level by re-lifting `x_23(1)` as `x_23(pq)`. The obstruction of
[BL]/[UT], if there is one, lives only in the interaction of infinitely many such re-liftings. That interaction is
the Kazhdan whole, not a finite or locally finite piece.

**What is not proved.** It is not claimed that every finite subgroup of `Q` lifts to `N_-`. A finite subgroup that
does not lift would refute (HS) outright. That makes it the cheapest possible refutation, and it is recorded below as
(FL).

## 6. What dies, and the next falsifiable steps

**Death of the entropy index (Section 5 of `mirror-lift-untwists-only-through-a-mirror-splitting-proof`).**
The candidate was `ind(u', h') = H(h'F | F) - H(F | h'F)`, where `F` is the σ-algebra of `u'`-invariant sets.
* At the commuting pair `(u~, h' = s h~)` of Section 4, `h' F = F`, so the index is `0`.
* At the pair `(u~, h~)` the index is whatever it is. The two pairs have the same pair of `[T_-]`-cosets.
* So the index is not a function of the cosets. Any version that is a function of the cosets must vanish on every
  coset pair containing a commuting pair, which by Section 4 is every coset pair `(u_a, h)` with `[u_a, h] = 1`.

The same argument applies to any measurable image-layer index: the image layer of `u~ + 1` in `E` becomes, in
`N_-`, the choice of a fundamental domain of `u'`, and all fundamental domains are `[T_-]`-equivalent (I4).
The failure point named on that note, conjugators outside the linear world, is realized by `s`. Suppose
`s ∈ L_- = Ê_- ∩ [T_-]`. Then `u~` and `h' = s h~` would be commuting elements of `Ê_- ≅ E_-` with symbols
`u_a` and `h`, which (NVS) of `jacobson-symbol-sequence-does-not-virtually-split` forbids for `h = h_0^k`, applied in
its mirror form. So `s ∉ L_-`: the conjugator is genuinely measurable.

**Proper outerness (a strengthening of part 2, same proof).** For `f ∈ N_-` with `pi_-(f) != 1`, the set
`{x : f x T_- x}` is null. Write `f = M t` with `M ∈ Ê_-`, `t ∈ [T_-]`. Then `f x T_- x` iff `M x - x ∈ V_fin^-`, and
`M - 1` has nonzero symbol `pi_-(f) - 1`, so Lemma 1 of [BL] applies. So every lift of a subgroup of `Q` is a
**properly outer** action modulo `[T_-]`: no non-identity element agrees with an element of `[T_-]` on a positive set.

**(FL) Finite subgroups.** *Does every finite subgroup `F <= Q` lift to `N_-`?*
* A negative answer for one `F` refutes (HS), hence under (SR) refutes (ML) and the canonical bilateral lift.
* A positive answer, with part 3 and (LF), gives (HS) over every virtually free and every locally finite subgroup
  of `Q`.
* Known liftable: root subgroups `X_ij(A)`, constants `SL_n(F_2)`, `F_St`, and every `Q`-conjugate of these. The
  conjugates lift because conjugation by any lift of `g ∈ Q` carries a lift to a lift.
* The first genuinely new case is a finite subgroup whose `Q`-conjugacy class meets none of these families.
  An example would be a finite 2-subgroup of a Bruhat–Tits vertex stabilizer that is not conjugate into
  `UT_n(A)` or `SL_n(F_2)`.

**(Z2) The first non-virtually-free test.** Take `g_1 = diag(x, x^(-1), 1, ...)` and `g_2 = diag(1, x, x^(-1), ...)`.
(HS) over `<g_1, g_2> ≅ Z^2` holds iff there are `g_1' ∈ g~_1 [T_-]` and `t ∈ [T_-]` with
`t g_1' t^(-1) = g~_2^(-1) g_1' g~_2`. (Put `g_2' = g~_2 t`. Then `g_2' g_1' g_2'^(-1) = g_1'` is exactly this.)
* `g_1'` and `g~_2^(-1) g_1' g~_2` are conjugate in `N[T_-]` by `g~_2`, so any `Aut`-invariant (entropy, spectrum,
  ergodic type) agrees on them.
* An obstruction must be an invariant of pairs `(g, T_-)` under `[T_-]`-conjugacy that is not `N[T_-]`-invariant.
  That is an outer-conjugacy invariant in the sense of Connes–Krieger, relative to the fixed relation `T_-`.
* Both elements are aperiodic and properly outer, so finite-group tricks (fundamental domains) do not apply.

**(AM) The amenable question, and what would settle both.** `T_-` is hyperfinite. A lifting theorem of Ocneanu type
for relations would say: every properly outer homomorphism of a countable amenable group into
`Out(T_-) = N[T_-]/[T_-]` lifts to `N[T_-]`. Such a theorem would give (HS) over every amenable subgroup of `Q`, and
hence (FL) and (Z2).
* The von Neumann obstruction in `H^3(F, S^1)` has no analogue here. The cocycle `u(f, f') = alpha(f) alpha(f') alpha(f f')^(-1)`
  of a set-theoretic lift is determined exactly in `[T_-]`, not up to scalars, and it is exactly associative.
* So the only remaining issue is 2-cocycle vanishing for `[T_-]`-valued cocycle actions.
* This is **not** proved here. The Bezuglyi–Golodets and Sutherland line of outer-conjugacy results for amenable
  actions on hyperfinite relations is the place to look, and it is recorded as a spark.
* If it holds, every refutation of (HS) must go through a non-amenable, in effect Kazhdan, part of `Q`.
* If it fails for one amenable group, the failing case is the candidate refutation.
