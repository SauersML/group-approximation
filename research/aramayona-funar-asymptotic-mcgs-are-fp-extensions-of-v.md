---
rg: 2
id: aramayona-funar-asymptotic-mcgs-are-fp-extensions-of-v
kind: claim
title: The Aramayona--Funar asymptotic mapping class groups of Cantor-punctured closed surfaces are finitely presented, perfect in genus at least three, and extensions of Thompson's group V by a direct limit of bordered mapping class groups
distinct_from:
  thompson-v-finitely-presented-infinite-simple: that is Thompson's group V itself, finitely presented and simple; this imports groups that surject onto V with kernel a direct limit of surface mapping class groups, candidate hosts that are finitely presented but not simple.
  punctured-surface-mcgs-satisfy-permutational-boone-higman: that imports Boone--Higman for finite-type mapping class groups with a puncture or boundary; this imports structure theorems for infinite-type asymptotic mapping class groups, which contain the bordered groups but are not stated to contain any closed-surface mapping class group.
  cantor-punctured-birman-sections-have-no-finite-end-orbit: that is an obstruction to forgetful sections into mapping class groups of Cantor-punctured surfaces; this imports the structure of the finitely presented subgroups of those mapping class groups where such sections would land.
artifacts:
  - research/artifacts/bh-mcg-closed-surface-2026-09-12.md
---

**ESTABLISHED (literature import).** Read on 2026-09-12 from the arXiv PDFs,
downloaded on MSI and read page by page.
- **AF.** J. Aramayona and L. Funar, *Asymptotic mapping class groups of closed
  surfaces punctured along Cantor sets*, arXiv:1701.08132v2, pages 1--12.
- **ABFPW.** J. Aramayona, K.-U. Bux, J. Flechsig, N. Petrosyan and X. Wu, with an
  appendix by O. Randal-Williams, arXiv:2110.05318v5 (running head "Asymptotic
  mapping class groups of Cantor manifolds"), pages 1--5.

**Setting (AF Section 2).**
- `S_{g,n}` is "the compact surface of genus g ≥ 0 with n ≥ 0 boundary
  components", and `Σ_g` is the closed surface of genus `g` with a Cantor set
  removed.
- `Mod(S)` "is the group of isotopy classes of self-homeomorphisms of S, where
  homeomorphisms and isotopies are required to fix the boundary of S pointwise."
- `PMod(S)` is the subgroup "whose elements fix every topological end of S".
  `PMod_c(Σ_g)` "is the subgroup of PMod(Σ_g) whose elements are the identity
  outside a compact subsurface of Σ_g".
- `B_g ≤ H_g ≤ Mod(Σ_g)` are defined in AF Section 3 from a rigid structure on
  `Σ_g`. Only the facts quoted below are used.

**Quoted from AF.**
1. **Abstract.** `B_g` and `H_g` are "extensions of Thompson's group V by a
   direct limit of mapping class groups of compact surfaces of genus g".
2. **Proposition 4.2.** "For every g ≥ 0, there is a short exact sequence
   1 → PMod_c(Σ_g) → B_g → V → 1."
   - The quotient is the action on ends: "Every element of V induces a
     homeomorphism of the space of ends of 𝒯, which is homeomorphic to the
     Cantor set C."
   - Lemma 4.4: "For every genus g, we have PMod(Σ_g) ∩ B_g = PMod_c(Σ_g)."
   - Corollary 4.5: "Homeo_{B_g}(C) is isomorphic to Thompson's group V."
3. **Proposition 4.6.** "For every g ≥ 0, the restriction to the sequence (1)
   to H_g yields a short exact sequence 1 → PMod_c(Σ_g) → H_g → V₂[Z₂] → 1."
   On the same page: "by a surprising result of Bleak-Donoven-Jonušas [11] we
   have that, in fact, V ≅ V₂[Z₂]".
4. **Theorem 1.2**, as restated on page 12. "The groups B_g and H_g are finitely
   presented for every g ≥ 0."
5. **Corollary 1.5.** "B_g and H_g are perfect for every g ≥ 3."
6. **Lemma 2.1**, introduced as an "immediate observation". "For g ≥ 0 and
   n ≥ 1, Mod(S_{g,n}) < Mod(Σ_g)."
7. **Lemma 2.2**, introduced as "an easy observation". "Let g ≥ 0. Consider any
   family {S_i} of compact subsurfaces of Σ_g whose union equals Σ_g, partially
   ordered with respect to inclusion. Then PMod_c(Σ_g) ≅ lim→(PMod(S_i))."
8. **Theorem 1.11.** "Let Γ be a lattice in a semisimple Lie group G of real
   rank at least two, where G has no compact factors isogenous to SU(1,n) or
   SO(1,n). For every g ≥ 0, any homomorphism from Γ to B_g or H_g has finite
   image."
9. **Theorem 1.13.** "B_g is not linear for any g ≥ 0. In particular, H_g is not
   linear either."

**Quoted from ABFPW.**
1. **Theorem 1.1.** "The asymptotic mapping class groups of surfaces defined in
   [24, 26, 2] are of type F∞." Here `[2]` is AF; `[24]` and `[26]` are
   Funar--Kapoudjian.
2. **Theorem 1.7.** "Let O be a compact surface, and Y diffeomorphic to either
   S² or S¹ × S¹. For every d ≥ 2 and r ≥ 1, B_{d,r}(O,Y) is of type F∞."
3. **Identifications, page 5.** "the group B_0 of [24] is B_{2,1}(S², S²); the
   group B_g of [2] is B_{2,1}(S_g, S²), where S_g denotes the closed surface of
   genus g; and the group B_∞ of [26] is B_{2,1}(S², S¹ × S¹)".
4. **Sequence (1.3)**, Proposition 4.3.
   "1 → Map_c(C_{d,r}(O,Y)) → B_{d,r}(O,Y) → V_{d,r} → 1, where V_{d,r} denotes
   the standard Higman–Thompson group of degree d and with r roots, while
   Map_c(C_{d,r}(O,Y)) stands for the compactly-supported mapping class group,
   which is a direct limit of mapping class groups of suited submanifolds of
   C_{d,r}(O,Y)." A suited submanifold "is the union of O and finitely many
   pieces".
5. **Page 2.** Funar--Kapoudjian [26, Theorem 3.1] treat an "infinite-genus"
   asymptotic mapping class group "which contains the mapping class group of
   every compact surface with non-empty boundary".
6. **Theorem 1.5.** `B_{d,r}(O,Y)` acts cellularly on a contractible cube complex
   "in such way that cube stabilizers are finite extensions of mapping class
   groups of suited submanifolds".

**Not in these pages.**
- No statement that the mapping class group of a closed surface, or a
  finite-index subgroup of one, embeds in any of these groups. AF Lemma 2.1
  requires `n ≥ 1`.
- No description of normal subgroups beyond the displayed sequences.
- No Boone--Higman statement for the groups themselves.

**Why it matters.** These are the natural finitely presented groups that
contain the bordered mapping class groups of genus `g` and act on a Cantor set
of ends through `V`. The consequences for normal subgroups, and for copies of
closed-surface mapping class groups inside them, are derived in
`closed-mcg-in-asymptotic-mcg-is-bordered-or-infinite-in-v`.

The import is `aramayona-funar-asymptotic-mcg-citation`.
