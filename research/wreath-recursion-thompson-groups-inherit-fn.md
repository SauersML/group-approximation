---
rg: 2
id: wreath-recursion-thompson-groups-inherit-fn
kind: claim
title: For every group B of type F_n and every wreath recursion psi from B to B wr S_d, injective or not, the Thompson group V_{d,r}(B, psi) has type F_n; so a self-similar group with an F_n cover whose kernel dies under splitting has an F_n Röver–Nekrashevych group
requires:
  - wreath-recursion-thompson-groups-inherit-fn-proof
distinct_from:
  contracting-rover-nekrashevych-groups-are-f-infinity: that is the open Skipper–Zaremsky question for all contracting G; this is a transfer theorem that answers it whenever G has a dying-kernel cover of type F_infinity, and reduces the rest to contracting-groups-have-dying-kernel-covers-of-type-fn.
  rover-nekrashevych-polynomial-activity-tower-sigma-full: that uses finite germ extensions and needs polynomial activity; this needs no activity bound and no germ analysis, only an F_n group that maps onto the labels through a recursion.
  noninjective-ln-completions-have-self-similar-bases: that is the algebra analogue (Leavitt–Nekrashevych completions of non-injective recursions are finitely presented, with base B/J); this is the group statement, and it is proved for every F_n, not only finite presentation.
  ffwz-nonfaithful-stein-stabilizers-contain-canonical-kernel: that shows Stein complexes fail for non-faithful labels, because stabilizers contain the kernel; this replaces the complex by a category whose automorphism groups need not inject, which is exactly what is needed.
  twisted-brin-thompson-type-fn-criterion: that is the faithful twisted Brin–Thompson criterion; this is for Röver–Nekrashevych type recursions.
---

**ESTABLISHED** (lane proof `bh-free-06`, 2026-09-18, in
`wreath-recursion-thompson-groups-inherit-fn-proof`; not independently reviewed). No priority
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
