---
rg: 2
id: wreath-recursion-thompson-groups-inherit-fn
kind: claim
title: For every group B of type F_n and every wreath recursion psi from B to B wr S_d, injective or not, the Thompson group V_{d,r}(B, psi) has type F_n; so a self-similar group with an F_n cover whose kernel dies under splitting has an F_n Röver–Nekrashevych group
distinct_from:
  contracting-rover-nekrashevych-groups-are-f-infinity: that is the open Skipper–Zaremsky question for all contracting G; this is a transfer theorem that answers it whenever G has a dying-kernel cover of type F_infinity, and reduces the rest to contracting-groups-have-dying-kernel-covers-of-type-fn.
  rover-nekrashevych-polynomial-activity-tower-sigma-full: that uses finite germ extensions and needs polynomial activity; this needs no activity bound and no germ analysis, only an F_n group that maps onto the labels through a recursion.
  noninjective-ln-completions-have-self-similar-bases: that is the algebra analogue (Leavitt–Nekrashevych completions of non-injective recursions are finitely presented, with base B/J); this is the group statement, and it is proved for every F_n, not only finite presentation.
  ffwz-nonfaithful-stein-stabilizers-contain-canonical-kernel: that shows Stein complexes fail for non-faithful labels, because stabilizers contain the kernel; this replaces the complex by a category whose automorphism groups need not inject, which is exactly what is needed.
  twisted-brin-thompson-type-fn-criterion: that is the faithful twisted Brin–Thompson criterion; this is for Röver–Nekrashevych type recursions.
---

**ESTABLISHED** (lane proof `bh-free-06`, 2026-09-18, in
`wreath-recursion-thompson-groups-inherit-fn-proof`; Referee bh-ref-q12 2026-09-19: PASS, with the standard categorical inputs recalled rather than re-derived and one step (Lemma 7) to be written out; see the Referee section). No priority
claimed.
- The faithful case `B = G` is Skipper–Zaremsky arXiv:1709.06524, Corollary `cor:Finfty_inherited`
  (TeX l.1284), and Li arXiv:2110.04505, Corollary `intro:ZS`. Li needs condition (F), which
  concerns faithfulness (his TeX l.1454, l.2354).
- The non-injective case was not found in the literature checked (SZ, Li, BHM arXiv:2407.03149,
  Nekrashevych arXiv:1312.5654, Belk–Matucci arXiv:1312.2282).

## Setting

Fix `d >= 2` and `X = {0, ..., d−1}`, and let `B` be any group. A **wreath recursion** is a
homomorphism

  `ψ : B → B ≀ S_d`, written `ψ(b) = (b|_0, ..., b|_{d−1}) π_b`.

This is the same thing as a covering `B`-biset with `d` right orbits and a chosen transversal
(Nekrashevych).
- `B` acts on `X^*`. Its image `G := B/K` is a self-similar group, where `K` is the kernel of the
  action.
- Put `K_j := {b : b fixes X^j and b|_v = 1 for all v ∈ X^j}`, so that `1 = K_0 ≤ K_1 ≤ ... ≤ K`.
- The **dying kernel** is `J := ∪_j K_j`. The recursion has **dying kernel** if `J = K`.

The **cloning category** `𝒞(B, ψ)` is defined as follows.
- Its objects are the integers `n >= 1`.
- A morphism `n → m` is a pair `(F, α)`, where `F` is a `d`-ary forest with `n` roots and `m`
  leaves, and `α ∈ B ≀ S_m`. It means: split along `F`, then apply `α`.
- Composition pushes labels through forests using `ψ`.
- It is the Zappa–Szép product of the forest category and the groupoid `⊔_n B ≀ S_n`. For
  injective `ψ` it is Skipper–Zaremsky's `S_* ≀ G`.
- It admits a calculus of left fractions. Write `V_{d,r}(B, ψ)` for the automorphism group of the
  object `r` in the groupoid of fractions (`1 <= r <= d−1`).

## Theorem

1. **Transfer.** If `B` has type `F_n`, then `V_{d,r}(B, ψ)` has type `F_n` for every `r`.
   There are no other hypotheses: `ψ` need not be injective, and the action need not be faithful.
2. **Identification.**
   - `V_{d,r}(B, ψ) ≅ V_{d,r}(B/J, ψ̄)`.
   - The groupoid of fractions maps onto the Röver–Nekrashevych groupoid of `G`. It maps
     isomorphically if and only if `J = K`.
   - So if the recursion has dying kernel, `V_{d,r}(B, ψ) ≅ V_{d,r}(G)`, and hence **`V_{d,r}(G)`
     has type `F_n` whenever some dying-kernel cover of `G` does.**

## Proof in five lines (details in the proof node)

1. **Localization.** The cloning category satisfies Ore's condition and left cancellation. So
   Quillen's Theorem A (the comma categories are filtered) gives
   `B𝒞(B,ψ) ≃ ⊔_r BV_{d,r}(B,ψ)`. The dying kernel enters only in the identification with `V(G)`.
2. **Morse filtration.** `𝒞` is an EI-category. Adding the object `m` is a homotopy pushout along
   `(L_m)_{hΓ_m} → BΓ_m`, where `Γ_m = B ≀ S_m` and `L_m` is the nerve of the category of arrows
   from lower objects into `m`.
3. **Stein retraction.** Keeping only the bottom carets deforms `L_m` onto its elementary part
   `E_m`.
4. **Structure of `E_m`.** An elementary arrow has automorphism group `K_1^{#carets}` (not
   trivial when `ψ` is not injective). So `N(E_m)` is the **polyhedral join**, over the complex
   `M_m` of disjoint `d`-subsets of `[m]`, of the nonempty spaces `Y_I = ⊔ BK_1`.
5. **Connectivity and finiteness.**
   - `M_m` is weakly Cohen–Macaulay of dimension `ν(m) = ⌊(⌊m/d⌋ − 1)/d⌋`, by Belk–Forrest
     grounding.
   - A new lemma: polyhedral joins over a wCM complex with nonempty fibers are as connected as the
     complex. So `L_m` is `(ν(m)−1)`-connected, whatever `K_1` is.
   - All Borel constructions only involve groups `B^a ⋊ finite`, so they have type `F_n`.
   - Brown's criterion finishes.

## Consequences (each checked at source; see the proof node §8)

- **Nekrashevych's finite presentation theorem, re-proved.**
  - Let `G` be contracting with nucleus `N`. Then `B = ⟨N | all relations of length <= 3⟩` is
    finitely presented and has dying kernel (Nekrashevych arXiv:1312.5654, Prop.
    `pr:lengththree` at TeX l.1646 and Prop. `pr:kernelcontracting` at TeX l.1668).
  - So `V_d(G)` is finitely presented. This is his Theorem `th:finitepresentation` (TeX l.1948),
    obtained here as the case `n = 2`.
- **Expanding maps.**
  - Let `f : M_1 → M` be an expanding partial self-covering of a compact path-connected,
    semi-locally simply connected space. The `π_1(M)`-biset has dying kernel (ibid. Prop.
    `pr:expandingpi1`, TeX l.1710).
  - So `V_f ≅ V_d(IMG f)` has type `F_n` whenever `π_1(M)` does.
  - In particular `V_f` has type `F_∞` for every **hyperbolic post-critically finite rational
    map**: see `hyperbolic-pcf-rational-nekrashevych-groups-are-f-infinity`.
- **Röver's group, re-proved.** The Grigorchuk group has the dying-kernel cover
  `C_2 * (C_2 × C_2)`, which is virtually free, so `V(G)` has type `F_∞` (Belk–Matucci).
- **The Skipper–Zaremsky question.**
  - It is reduced to `contracting-groups-have-dying-kernel-covers-of-type-fn`.
  - That node also records an obstruction: a torsion element with a fixed ray of nontrivial
    sections forbids torsion-free covers.

## Lesson for general BH

**The finiteness of a Thompson-type envelope is inherited from any group that maps onto the labels
through a recursion. The labels' own finiteness is irrelevant, because the Thompson structure kills
the kernel for free when the kernel dies under splitting.**
- For host constructions, an infinitely presented self-similar input (branch groups, IMGs, spinal
  groups) can be traded for a free, virtually free, orbifold or hyperbolic cover.
- The right tool for non-faithful labels is an **EI-category with a calculus of fractions**, not a
  group acting on a Stein complex. Automorphism groups of objects need not inject into the
  fraction group, and the only price in descending links is the polyhedral-join fattening by
  `BK_1`, which costs no connectivity.
- The same mechanism should transfer to self-similar groupoids over SFTs, hence to full
  contracting RSGs (BBMZ-hyperbolic Q1.2). There the natural cover of the RSG built from a
  hyperbolic group `G` is `G` itself, which has type `F_∞`. This is flagged as the next target, not
  proved here.

## Referee (bh-ref-q12, 2026-09-19): PASS

I checked the proof node section by section. **Hypotheses:** `B` of type `F_n` and any homomorphism
`ψ : B → B ≀ S_d`. Nothing else is needed. The conclusion about `V_{d,r}(G)` needs, in addition, **dying kernel**
`J = K`.

**§1, the cloning category: correct.**
- Composition is the Zappa–Szép rule. "Left cancellation" is cancellation of the first factor: `f∘s = g∘s` implies
  `f = g`, since `α^*` is a bijection on forests, grafting is cancellative, and `α_*` is an isomorphism.
- The precomposition stabilizer of `(F, α)` is `σ = 1` with `a_i ∈ K_(T_i)`, and `a_i = 1` at trivial trees.

**§2, Lemmas 1 and 2: correct.**
- *Ore.* Take a common refinement, then postcompose with `β′β^{-1}`.
- *The Gabriel–Zisman cancellation axiom* holds with `t = id`.
- *Filteredness.* `y/L` is filtered, and it is nonempty since `(y, id)` is an object. Quillen A applies. The
  localization facts are standard and were not re-derived here.
- *Identification.* `Λ(f) = Λ(g)` forces `F = F′` and `α′ = αk` with `k ∈ K^m`. Then `t∘f = t∘g` iff each
  `k_ℓ ∈ K_(T_ℓ)`, and `⋃_T K_T = ⋃_j K_j = J`, since `K_T ⊆ K_(depth T)`.
- *The quotient `B/J`.*
  - `K_j = ker ψ^j` is normal.
  - `ψ(K_(j+1)) ⊆ K_j^d` with trivial permutation.
  - `ψ̄` on `B/J` is injective, since `d` is finite.
  - So `V_{d,r}(B, ψ) ≅ V_{d,r}(B/J, ψ̄)`. It equals `V_{d,r}(G)` iff `J = K`.
- This agrees with the referee remark in `abstract-rn-simple-subgroups-avoid-tree-kernel`, where `L_∞ = J`.

**§3, the collage: correct.**
- There are no arrows from `m` to lower objects (EI). The category of arrows is the Grothendieck construction of the
  free `Γ_m`-action on `O_m = 𝒞_(<m) ↓ m`.
- So `B𝒞_(≤m) ≃ B𝒞_(<m) ∪_((L_m)_(hΓ_m)) BΓ_m`. A `(k−1)`-connected `L_m` gives a `k`-connected inclusion.
- The collage lemma is standard: a category over `[1]` is the homotopy pushout along the category of elements of its
  profunctor. It was recalled, not re-derived.

**§4, the Stein retraction: correct.**
- Removing the bottom carets gives `f = e(f) ∘ h_f`.
- For `g : f_1 → f_2`, the transported bottom carets of `F_2` are bottom carets of `F_1`, because
  `F_1 = γ^*F_2 ∘ G`. So `u` exists, with elementary forest `E_(F_1) ∖ γ^*E_(F_2)`. Cancellation gives
  uniqueness and `e(f_2)∘u = e(f_1)`.
- `r∘i = id`, and `h` is natural and commutes with postcomposition.

**§5, Lemma 4: correct.**
- `Aut(f) = ∏_(M(f)) K_1`.
- `Hom(f′, f)` is nonempty iff `M(f) ⊆ M(f′)` with matching decorations. It is then an `Aut(f)`-torsor: `G` is
  recovered as the carets of `f′` outside `M(f)`, and the remaining freedom is the precomposition stabilizer.
- Thomason's theorem and the hocolim-of-products-with-projections description of a polyhedral join apply.
- Grouping decorations per block gives the fibers `Y_I = ⊔ BK_1`. They are nonempty, since `Γ_I` acts simply
  transitively on `Ω_I`, so `Ω_I ≠ ∅`.

**§6, Lemmas 5 and 6: correct.**
- *Lemma 5.* Cone off one vertex at a time. The pushout square is
  `(Z_old ⊇ Y_v ∗ W ⊆ CY_v ∗ W)`, with `W` the polyhedral join over `lk(v)`.
  - `lk(v)` is wCM of dimension `n−1` and nonempty for `n ≥ 1`, so the induction applies to it with arbitrary
    nonempty fibers.
  - The join bound gives `Y_v ∗ W` `(n−1)`-connected, and all cones give `L`.
- *Lemma 6.* A maximal matching is a `d`-ground (Belk–Matucci Def. 6.1 and Thm 6.2, via Belk–Forrest), and `M_m` is
  flag.
  - The `ν(m)` stated is weaker than grounding gives (`⌊⌊m/d⌋/d⌋`), which is harmless.
  - Links are `M_(m−d(p+1))`, and `⌊(N−p−1)/d⌋ ≥ ⌊N/d⌋ − p − 1`.

**§7, Lemma 7 and the conclusion: correct in outline. This is the one step to write out.**
- *Why the outline works.* `(L_m)_(hΓ_m) ≃ B(E_m//Γ_m)`.
  - `E_m//Γ_m` has finitely many isomorphism classes, one per number of carets. `Γ_m` acts transitively on the
    decorations of a matching shape, because `Γ_I` is simply transitive on `Ω_I`. The infinitely many cosets
    `Ω_I/ψ(B)` therefore cause no infinite object set.
  - The automorphism group of an elementary `f` in `E_m//Γ_m` is `Stab_(Γ_c)(F) ≅ (B ≀ S_k) × (B ≀ S_(c−k))`.
  - The stabilizers of morphisms, under both automorphism groups, are again products `B ≀ S_(k_i)`. The new carets'
    labels are free, and the old caret roots sit on strands where the action is `a′`.
  - So every group in the collage induction is a finite extension of a power of `B`, of type `F_n`, and the induction
    gives finite `n`-type.
- *The node's own count.* The node computes the same thing as `(BK_1)_(h(B/K_1)) ≃ BB`. Its phrase "morphism sets
  finite modulo automorphisms" should be replaced by the stabilizer statement above.
- *The conclusion.* Take `m` with `ν(m) ≥ n`. Every later attachment is `ν(m′) ≥ n`-connected, so
  `B𝒞_(≤m) → B𝒞_([r]) ≃ BV_{d,r}(B, ψ)` is `n`-connected, from a space of finite `n`-type. Attaching cells of
  dimension `≥ n+1` gives `F_n`.

**How `F_∞` reaches `V_{d,r}(G)`.** It passes to `V_{d,r}(B, ψ)` by the above. Lemma 2 identifies this group with
`V_{d,r}(B/J, ψ̄)`, and with `V_{d,r}(G)` exactly when `J = K`. So the cover must be of type `F_n` and have dying
kernel. For expanding coverings, dying kernel is Nekrashevych, arXiv:1312.5654, Prop. `pr:expandingpi1`, which the
node quotes at source; I did not re-read it.

**Consistency checks.**
- *The faithful, injective case* is Skipper–Zaremsky, Cor. `cor:Finfty_inherited`.
- *SWZ's non-`F_n` groups (persistent actions).* The free cover has `J = K_∞ = 1 ≠ K`, so no conclusion is drawn,
  consistent with their theorem.
- *Finite-state `G` with the free cover.* The theorem gives `V_d(F/K_∞)` of type `F_∞`. Its `n = 2` case matches the
  presentation `V̂` of the lift-ideal Theorem A with `R = ∅`, by that proof's Remark.
- *The Grigorchuk cover `C_2 ∗ (C_2 × C_2)`.* The length-≤3 relations of the nucleus are
  `a² = b² = c² = d² = 1` and `bcd = 1`; the length-8 relator `(ad)^4` is not among them.

**Literature.** The non-injective case was not found in SZ, SWZ, Li or BHM (the node's search). Witzel–Zaremsky
cloning systems are also relevant: I did not check whether their framework allows non-injective cloning maps. No
priority claimed.

**Verdict: PASS.** Write out Lemma 7's stabilizers.
