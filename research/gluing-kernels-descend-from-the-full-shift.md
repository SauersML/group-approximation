---
rg: 2
id: gluing-kernels-descend-from-the-full-shift
kind: claim
title: For V times a topologically free subshift, the gluing kernel is the image of the full shift's gluing kernel, and the full group is the full-shift full group modulo one conditioned relator per forbidden pattern; so P2'b over a fixed group and alphabet is one statement about the full shift
distinct_from:
  v-times-sft-full-groups-glue-from-two-wreath-pieces: that is P2'b for one subshift X; this compares the kernels of different closed invariant sets and shows every one is an image of the full-shift kernel, so P2'b for all topologically free subshifts over an alphabet reduces to the full shift.
  v-times-sft-gluing-kernel-is-relatively-perfect: that computes what the copy endomorphisms force on one kernel (K = [K, Gamma~]); this is a descent statement between kernels of nested systems and uses no swindle.
  v-times-shift-restriction-kernels-are-perfect: that localizes the restriction kernel of the alternating group off C x Y for Lambda = Z and minimal Y and asks whether it is perfect; this localizes it for every group, every topologically free closed invariant set and the whole full group, and computes normal generators (conditioned V-elements off X).
  v-times-shift-fp2-forces-fp2-of-every-subshift-restriction: that passes FP_2 from the full shift to restrictions for Lambda = Z; this passes exactness and finite normal generation of the gluing kernel from any ambient system to its subsystems, for every Lambda.
---

**ESTABLISHED** (lane proof, elementary; unreviewed; no priority claimed). bh-p2b-exact, 2026-09-18.
The reduction target is gate 5 of the v5 synthesis (P2′b, group route only).

## Setting

- `Λ` is a countable group, and `Y` is a compact metrizable totally disconnected space with any action of `Λ`
  by homeomorphisms. The full shift `A^Λ`, fixed points included, is allowed.
- `X ⊆ Y` is nonempty, closed and invariant, and `Λ` acts on `X` **topologically freely**: for `λ ≠ 1`, the
  fixed-point set of `λ` in `X` has empty interior. Free actions are a special case.
- For `Z ∈ {X, Y}`:
  - `T_Z = G_V × (Λ ⋉ Z)` acts on `C × Z`, with `F(T_Z)` its topological full group;
  - `M = C(C, Λ) ⋊ V` (independent of `Z`) and `N_Z = LC(Z, V) ⋊ Λ`;
  - `Γ~_Z = M *_(V×Λ) N_Z / ⟨⟨[M_0, N_(1,Z)]⟩⟩`, with `π_Z : Γ~_Z → F(T_Z)` and `K_Z = ker π_Z`.

  These are exactly as in item 5 of `v-times-sft-full-groups-split-into-two-wreath-pieces`, with the same
  formulas. Defining them uses no freeness.
- For `v ∈ V` and clopen `P ⊆ Z`, `v^[P] ∈ LC(Z, V)` is `v` over `P` and `1` off `P`.
- `q : Γ~_Y → Γ~_X` is the identity on `M` and restriction `(f, λ) ↦ (f|_X, λ)` on `N_Y`.
- `res : F(T_Y) → F(T_X)` is restriction to `C × X`.

## Theorem

1. **Restriction kernel.** `res` is a surjective homomorphism. Its kernel is the normal closure in `F(T_Y)` of
   `{v^[P] : v ∈ V, P ⊆ Y clopen, P ∩ X = ∅}`.
2. **Gluing groups.** `q` is a surjective homomorphism with `π_X ∘ q = res ∘ π_Y`, and `ker q = ⟨⟨L⟩⟩` for
   `L = {f ∈ LC(Y, V) : f|_X ≡ 1}`.
3. **Descent.** `K_X = q(K_Y)`.
4. **SFTs.** Let `Y = A^Λ` and let `X` be the SFT with forbidden patterns `p_1, …, p_r ∈ A^F` on a finite window
   `F`, with cylinders `Z_i = Z(F, p_i)`. Then for any `v_0 ∈ V ∖ {1}`, `L` is the normal closure in `N_Y` of
   the `r` elements `v_0^[Z_i]`. So:
   - `Γ~_X` is `Γ~_Y` modulo the normal closure of these `r` elements;
   - if `X` is topologically free, `F(T_X)` is `F(T_Y)` modulo the normal closure of their images.

5. **The full shift is itself topologically free (Λ infinite, |A| ≥ 2).**
   - Let `λ ≠ 1` and take a cylinder `Z(F, α)`.
   - Pick `g ∈ Λ ∖ (F ∪ λF ∪ λ^(-1)F)`, which exists because `Λ` is infinite. Then `g ≠ λ^(-1) g`.
   - Take `x ∈ Z(F, α)` with `x(g) ≠ x(λ^(-1) g)`. Then `(λx)(g) = x(λ^(-1) g) ≠ x(g)`. The other convention
     for the shift action is symmetric.

   So `X = A^Λ` is allowed in items 1–4, and FSG(Λ, A) below is P2′b for the full shift itself.
6. **Relative form.** Let `Λ` be finitely presented and `X` topologically free. Then `K_X` is finitely normally
   generated iff `F(T_X)` is finitely presented relative to the subgroup `N_X`, meaning that
   `F(T_X) = (N_X ∗ F(S)) / ⟨⟨R⟩⟩` with `S, R` finite.
   In particular:
   - If `F(T_X)` is finitely presented, then `K_X` is finitely normally generated. So P2′b is a necessary
     condition for finite presentation of `F(T_X)`, not an artifact of the gluing model.
   - If `N_X` is finitely presented (P2′a), then `F(T_X)` is finitely presented iff P2′b holds for `X`.

## Corollaries

- **(0) The full shift is the universal case.** For infinite `Λ`, P2′b holds for every topologically free subshift
  over `A` iff it holds for `A^Λ`. One direction is (c) below. The other is item 5: `A^Λ` is one of those
  subshifts.

- **(a) Exactness descends.** If `K_Y = 1`, then `K_X = 1`.
- **(b) Finite normal generation descends, uniformly.** If `K_Y = ⟨⟨R⟩⟩`, then `K_X = ⟨⟨q(R)⟩⟩`.
- **(c) One statement per group and alphabet.** Every subshift over `A` is a closed invariant subset of `A^Λ`.
  So P2′b for **every** topologically free subshift over `A` (rigid or not, minimal or not, SFT or not) follows
  from one statement:

  > **FSG(Λ, A)** (full-shift gluing): the kernel of `Γ~_(A^Λ) → F(G_V × (Λ ⋉ A^Λ))` is the normal closure
  > of finitely many elements.

  Likewise, exactness for all of them follows from `K_(A^Λ) = 1`. If `Λ` is finitely generated, so is
  `Γ~_(A^Λ)`: `M = ⟨V, s|_(C_0)⟩`, and the §3 argument of the split proof gives `N_(A^Λ) = ⟨Λ, v^(a)⟩`, using only
  site conditions.
- **(d) Presentations of SFT full groups.** Combining (b) with item 4, for a topologically free SFT `X` over `A`,

  `F(T_X) = Γ~_(A^Λ) / ⟨⟨ R ∪ {v_0^[Z_1], …, v_0^[Z_r]} ⟩⟩`.

  So under FSG(Λ, A) with relator set `R`, every such full group is the one full-shift gluing group modulo
  `|R| + r` relators. With P2′a (`N_X` fp for rigid `X`) and `M` fp, this is P2′ for the SFT.
- **(e) Refutations climb.** If `K_X` is not finitely normally generated for one topologically free `X`, then
  FSG(Λ, A) fails, and so does finite normal generation of `K_Y` for every closed invariant `Y ⊇ X`.
- **(f) Universal Cantor form.** A topologically free Λ-Cantor system `X` embeds equivariantly in `C^Λ`, by
  `x ↦ (λ ↦ ι(λ^(-1) x))` for an embedding `ι : X → C`. So every `K_X` is an image of the single kernel
  `K_(C^Λ)`. But `N_(C^Λ)` is not finitely generated, so the finite-alphabet form (c) is the useful one.

**Consequence for the master route.** Route 2 becomes `(★′) ∧ FSG(Λ₀, A) ⇒ BH`, where `A` is the alphabet of
the (★′) SFT over the fp overgroup `Λ₀`, because (★′) supplies a topologically free SFT. The two layers of P2′ now
live on different objects:
- P2′a (rigidity) is about `X`;
- P2′b is about the full shift `A^(Λ₀)`, which is canonical and has no dynamics to choose.

## Not claimed

- FSG is not proved.
  - The full shift is not quantum rigid, so `F(T_(A^Λ))` and `N_(A^Λ)` are not finitely presented. FSG asks
    only for finitely many extra relators over the finitely generated `Γ~_(A^Λ)`, a relative finite
    presentation.
  - `A^Λ` has points with nontrivial stabilizers. By item 5 they form a set with empty interior when `Λ` is
    infinite, so `T_(A^Λ)` is effective and `F(T_(A^Λ))` acts faithfully.
  - For finite `Λ`, FSG holds trivially. Then `A^Λ` is finite, and `F(T_(A^Λ)) = ∏_O V_(2,|O|)(Stab_O)` as a group of bisections
    (and `∏_O V_(2,|O|)` as a group of homeomorphisms). Either way it is a product of labelled Higman–Thompson groups
    over the orbits. It and `Γ~` are both finitely presented. This
    calibration carries no information.
  - The topologically free subshifts over `A` form a directed family: a union of two of them is again one,
    since an open set of the union meets one of them in a relatively open set. So P2′b for `X₁ ∪ X₂` gives it
    for both.
- "Exactness" in P2′b means exactness of a presentation (`K = 1`). It is unrelated to exactness of groups
  (property A), the sense of Osajda's non-exact groups. The lane found no implication between them in either
  direction. `F(T_(A^Λ))` contains `Λ`, so it is non-exact when `Λ₀` is, and that says nothing about `K`.

## Lesson for general BH

The gluing layer of the group route belongs to the ambient full shift, not to the subshift. Let `X` be
topologically free. Every relation of `[[G_V × (Λ ⋉ X)]]` is then:
- the restriction of a full-shift relation,
- up to conditioned V-elements on cylinders that miss `X`.

For an SFT, those extra relators are finitely many, one per forbidden pattern.

So P2′b over a fixed `Λ₀` and alphabet is one statement, FSG(Λ₀, A). It does not depend on which rigid SFT (★′)
produces, and rigidity plays no part in it. The general mechanism is **descent of presentation kernels**. Suppose:
- a model group maps onto a full group;
- both are functorial under restriction to closed invariant sets;
- the target's restriction kernel is normally generated by images of model elements.

Then the model kernel of a subsystem is the image of the ambient model kernel. Any exactness question for hosts
of the form `[[G_V × H]]` can therefore be posed once, on the universal (full-shift) `H`. Refutations climb, and
proofs descend.

## Proof

**Normal forms.** By Step 1 of `v-times-ample-full-groups-are-generated-by-transpositions-proof`, refining
bisections of `Λ ⋉ Z` to sets `{λ} × Q`, every `g ∈ F(T_Z)` is a disjoint union of *pieces*
`(u_i w, z) ↦ (u'_i w, λ_i z)` on `D_i = [u_i] × Q_i`. The `D_i` partition `C × Z`, and so do the ranges
`[u'_i] × λ_i Q_i`.

*Piece transpositions.* A transposition `τ_B`, with `B` a compact open bisection of `T_Z` and
`s(B) ∩ r(B) = ∅`, is a product of commuting piece transpositions `t : [w] × P ↔ [w'] × λP`, given by
`(wc, z) ↦ (w'c, λz)`. The pieces have pairwise disjoint sources, pairwise disjoint ranges, and no source meets a
range. The words `w, w'` can be taken nonempty (split on the first digit).

**Item 1, well defined and onto.**
- Each piece maps `C × (Q_i ∩ X)` into `C × X`, because `X` is invariant, and so does `g^(-1)`. So `g` preserves
  `C × X`, and the restricted pieces form a normal form over `T_X`. So `res` is a homomorphism.
- For surjectivity, `F(T_X)` is generated by piece transpositions `t : [w] × P ↔ [w'] × λP` with `P ⊆ X` clopen
  (the transposition theorem, `F = S`).
  - Choose a clopen `P^ ⊆ Y` with `P^ ∩ X = P`.
  - If `w` and `w'` are comparable, disjointness forces `P ∩ λP = ∅`. Replace `P^` by `P^ ∖ λP^`, which still
    meets `X` in `P` and is disjoint from its `λ`-image.
  - The piece transposition `t^` of `T_Y` on `[w] × P^ ↔ [w'] × λP^` satisfies `res(t^) = t`.

**Item 1, localization.** Let `res(g) = 1`, with a normal form as above.
- If `D_i` meets `C × X`, then for every `x ∈ Q_i ∩ X` and every `w`,
  `(u'_i w, λ_i x) = g(u_i w, x) = (u_i w, x)`. So `u'_i = u_i`, and `λ_i` fixes the nonempty relatively open
  set `Q_i ∩ X` pointwise. Topological freeness gives `λ_i = 1`, so `g` is the identity on `D_i`.
- Let `Z` be the union of the `D_i` with `Q_i ∩ X = ∅`, and `U` the union of those `Q_i`. Then `U` is clopen,
  `U ∩ X = ∅`, and `Z ⊆ C × U`.
- `g` is the identity off `Z`, so it maps `Z` onto itself and preserves `C × U`. Hence
  `g|_(C×U) ∈ F(G_V × (Λ ⋉ Y)|_U)`.

**Item 1, generators.** `H = (Λ ⋉ Y)|_U` is ample and Hausdorff, with compact totally disconnected unit space,
and the transposition theorem assumes no minimality. So `g|_(C×U)` is a product of piece transpositions
`t : [w] × P ↔ [w'] × λP` with `P ∪ λP ⊆ U`, each extended by the identity. Following §1 of
`v-times-sft-full-groups-split-into-two-wreath-pieces-proof`:
- **Case `w ⊥ w'`.** With `m = λ|_(C_w) ∈ π_Y(M)`, `m t m^(-1) = (w w')^[λP]`. Check it pointwise:
  - on `(wc, y)`, `y ∈ λP`: `m^(-1)` gives `(wc, λ^(-1) y)`, `t` gives `(w'c, y)`, and `m` fixes it;
  - on `(w'c, y)`: `t` gives `(wc, λ^(-1) y)`, and `m` gives `(wc, y)`;
  - everything else is fixed.
- **Case `w, w'` comparable.** Here `P ∩ λP = ∅`.
  - Pick `v ∈ V` with `v(w'c) = wc`, a prefix map between proper cones, and put `n = v^[λP]`. Then
    `s = n t n^(-1)` swaps `[w] × P` and `[w] × λP`.
  - Pick `u ⊥ w`. Let `τ_1 : [w] × P ↔ [u] × λP` (the first case) and `τ_2 = (u w)^[λP]`. Then
    `s = τ_2 τ_1 τ_2`.

In both cases `t` is a product of conjugates of conditioned elements `v^[λP]` with `λP ⊆ U`, which is disjoint
from `X`. Each such element lies in `π_Y(L)` and is the image of an element of `L`, and the conjugators lie in
`π_Y(Γ~_Y)`. So `ker res ⊆ π_Y(⟨⟨L⟩⟩)`. Conversely, every `v^[P]` with `P ∩ X = ∅` acts trivially on `C × X`.

`π_Y` is onto: §1 of the split proof uses no freeness, only the transposition theorem and the formulas above. So
`π_Y(⟨⟨L⟩⟩)` is the normal closure in `F(T_Y)` of the conditioned elements off `X`. That proves item 1.

**Item 2.**
- Restriction `ρ : N_Y → N_X` is a surjective homomorphism, since every clopen partition of `X` extends to one of
  `Y`. It agrees with `id_M` on `V × Λ`, and it maps `N_(1,Y)` onto `N_(1,X)`. So `q` is defined, and it is onto.
- `ker ρ = L`, and `L ∩ (V × Λ) = 1`, because a constant `v` with `v|_X = 1` is trivial.
- Hence `(M *_(V×Λ) N_Y) / ⟨⟨L⟩⟩ = M *_(V×Λ) (N_Y / L)`. Adding the image relators `[M_0, N_(1,X)]` gives
  `Γ~_X`, so `ker q = ⟨⟨L⟩⟩`.
- `π_X q = res π_Y` holds on the generators `M ∪ N_Y`: they are the same maps, restricted.

**Item 3.**
- `π_X(q(K_Y)) = res(π_Y(K_Y)) = 1`, so `q(K_Y) ⊆ K_X`.
- Conversely, let `k ∈ K_X` and pick `k~` with `q(k~) = k`.
  - Then `res(π_Y(k~)) = π_X(k) = 1`, so by item 1, `π_Y(k~) = π_Y(j)` for some `j ∈ ⟨⟨L⟩⟩ = ker q`.
  - Then `k~ j^(-1) ∈ K_Y`, and `q(k~ j^(-1)) = k`.

**Item 4.**
- `Y ∖ X = ⋃_(λ, i) λ Z_i` is open.
- Let `f ∈ L`. Write `f` as a product of commuting factors `v_π^[π]` over a clopen partition. The factors with
  `v_π ≠ 1` have `π ∩ X = ∅`. By compactness and refinement, each is a product of elements `v^[π']` with `π'`
  clopen inside one `λ Z_i`.
- In `N_Y`, `λ^(-1) v^[π'] λ = v^[λ^(-1) π']`. So it suffices that `v^[P] ∈ ⟨⟨v_0^[Z_i]⟩⟩_(N_Y)` for every
  `v ∈ V` and every clopen `P ⊆ Z_i`.
  - First, `a ↦ a^[Z_i]` is a homomorphism `V → N_Y`, and constants `c ∈ V ≤ N_Y` conjugate `a^[Z_i]` to
    `(c a c^(-1))^[Z_i]`. `V` is simple (Higman), so `V^[Z_i] ⊆ ⟨⟨v_0^[Z_i]⟩⟩`.
  - Second, `[a^[Z_i], b^[P]] = [a, b]^[P]` for `P ⊆ Z_i`, with `b^[P] ∈ N_Y`, and `V` is perfect.
- Each `v_0^[Z_i]` lies in `L`. The statements about `Γ~_X` and `F(T_X)` follow from items 1–3 and the
  surjectivity of `π_Y`. ∎

**Item 6.**
- *`Γ~_X` is finitely presented relative to `N_X`.* Take `S` to be a finite generating set of `M`.
  - `M = V(Λ)` is finitely presented (`cantor-integer-maps-by-v-are-of-type-fp2`), and `V × Λ` is finitely
    generated. So the amalgam `M ∗_(V×Λ) N_X` is `(N_X ∗ F(S))` modulo finitely many relators: the relators of
    `M`, plus one identification for each generator of `V × Λ`.
  - The gluing relators `[M_0, N_(1,X)]` follow from the finite set `R_0` (split node, item 5).
  - So `Γ~_X = (N_X ∗ F(S)) / ⟨⟨R'⟩⟩` with `R'` finite.
- *Equivalence.*
  - If `F(T_X) = (N_X ∗ F(S)) / ⟨⟨R⟩⟩` with `R` finite, then `R' ⊆ ⟨⟨R⟩⟩`, and `K_X` is the normal closure of
    the image of `R`.
  - Conversely, adding finitely many normal generators of `K_X` to `R'` gives a finite relative presentation.
  - A change of the finite relative generating set changes this by finitely many relators, by the usual Tietze
    argument.
- *First bullet.* Let `F(T_X) = F(S') / ⟨⟨R''⟩⟩` be finite. `N_X` is finitely generated, say by `n_1, …, n_k`
  (split node, item 3). Choose words `w_j` in `S'` representing the `n_j`. Then
  `(N_X ∗ F(S')) / ⟨⟨R'' ∪ {n_j^(-1) w_j}⟩⟩` is generated by `S'` and satisfies `R''`. So it is a quotient of
  `F(T_X)` that maps onto `F(T_X)`, hence equal to it.
- *Second bullet.* This is the first bullet together with P2′a ∧ P2′b ⇒ fp (split node, "Consequence"). ∎
