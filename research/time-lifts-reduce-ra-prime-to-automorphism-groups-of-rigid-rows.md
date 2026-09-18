---
rg: 2
id: time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows
kind: claim
title: A finitely generated group of automorphisms of a minimal free quantum-rigid Z^d-SFT, meeting the shifts trivially, times Z^d carries a minimal free rigid SFT; so (RA′) implies that such automorphism groups are exact, a non-exact one refutes (RA′), and an fp one is a carrier, and the non-exactness needs infinite fibres over the equicontinuous factor (a profinite distal layer, possible for residually finite inputs, or a relatively weakly mixing one), while homology of the V-full groups is blind to amenability
requires:
  - quantum-rigid-minimal-topfree-subshift-actions-are-amenable
  - deterministic-time-lifts-inherit-quantum-rigidity
  - minimal-system-automorphisms-fix-every-proximal-factor
  - automorphisms-of-hierarchical-rows-are-virtually-abelian
  - v-times-full-groups-are-acyclic-over-stratified-minimal-systems
distinct_from:
  quantum-rigid-minimal-topfree-subshift-actions-are-amenable: that poses (RA) and (RA′) for arbitrary acting groups; this shows the time-lift face of (RA′) is exactly a statement about automorphism groups of rigid Z^d-rows, and gives the carrier criterion that follows.
  automorphisms-of-hierarchical-rows-are-virtually-abelian: that bounds automorphism groups of hierarchical rows; this shows why the bound matters for (RA′), and where a non-exact automorphism group would have to live in any rigid row.
  deterministic-time-lifts-inherit-quantum-rigidity: that transfers rigidity to time lifts; this adds freeness, minimality and exactness bookkeeping for lifts over abelian rows.
---

**ESTABLISHED** (lane bh-invent-16, 2026-09-18; lane proof, elementary given the cited nodes; not
reviewed; no priority claimed). It addresses gate 1 of the v7 synthesis, (RA′) at Osajda's input, from
the homological and commutant side. (RA′) itself stays **OPEN**.

## Setting

- `P = Z^d`, and `Y ⊆ A^P` is a minimal, free, `D`-quantum-rigid SFT, for example the crossing-wire shift.
- `Aut(Y)` is the group of cellular automata commuting with `P`, and `σ(P) ≤ Aut(Y)` is the group of shifts.
- `G ≤ Aut(Y)` is finitely generated with `G ∩ σ(P) = 1`.
- `X_G ⊆ A^(G×P)` is the time lift of `deterministic-time-lifts-inherit-quantum-rigidity`, with
  `Λ_1 = G` and `Λ_2 = P`.
- (RA′): a finitely generated group carrying a minimal, topologically free, quantum-rigid subshift is
  exact.

## Statement

1. **Time-lift criterion.** `X_G` is an SFT over `G × P` that is:
   - minimal;
   - **free**;
   - `max(D, R+1)`-quantum rigid over the same field.

   `G × P` is exact iff `G` is. Hence:
   - (RA′) implies that every such `G ≤ Aut(Y)` is exact;
   - a single non-exact such `G` refutes (RA′), and with it (RA);
   - if `G ≤ Λ_1 ≤ Aut(Y)` with `Λ_1` finitely presented and `Λ_1 ∩ σ(P) = 1`, then `Λ_1 × P` is a finitely
     presented overgroup of `G` carrying (★′). This is the **carrier criterion**.
2. **Where a non-exact `G` must live.** Let `π : Y → M` be the maximal equicontinuous factor. `M` is a
   compact abelian rotation group, since `P` is abelian.
   - The map `Aut(Y) → Aut(M) = M` has abelian image. Its kernel `Aut_0(Y)` consists of the automorphisms
     that preserve every `π`-fibre.
   - Exactness is closed under extensions by amenable groups. So a non-exact `G` has a non-exact subgroup
     `G_0 = G ∩ Aut_0(Y)`.
   - Since an automorphism is determined by its value at one point, `|Aut_0(Y)|` is at most the smallest
     fibre cardinality of `π`.
     - It is trivial when a fibre is a singleton (almost automorphic rows).
     - It is finite for every row that is finite-to-one over its rotation on a dense set, as recorded
       for the hierarchical, fixed-point, Labbé and crossing-wire rows in
       `automorphisms-of-hierarchical-rows-are-virtually-abelian`.
   - So a non-exact `G_0` needs **infinite fibres** over `M`, and it must act in one of two ways.
     - **(a) Through a distal factor.** It can act faithfully on a non-expansive distal factor
       `Y → Z → M`, through a compact group, which is possible only for maximally almost periodic groups.
       Osajda's group is residually finite, so this door is open for it.
       - If `Y` itself is an isometric extension of `Z`, the fibres are finite (expansiveness), so the
         distal factor must be a proper factor.
     - **(b) In a relatively weakly mixing layer** over the distal part.
   - No rigidity source on main produces infinite fibres over the equicontinuous factor.
3. **Homology is blind to amenability.** For every minimal `Λ ↷ X`, amenable or not,
   `F(G_V × (Λ ⋉ X))` is integrally acyclic (Li's Corollary D, as in
   `v-times-full-groups-are-acyclic-over-stratified-minimal-systems`). So no invariant computed from the
   homology of the V-full group or of the groupoid can prove (RA′). Two further points:
   - The hypothesis of (RA′), quantum rigidity, is itself a homological finiteness statement. It is
     equivalent to finite presentation of the V-full group, by the necessity theorem together with (A₂).
   - Finitely presented groups can be non-exact (Higman embedding of Osajda's group).

   A proof of (RA′) must therefore extract an analytic invariant from rigidity: an invariant mean, or
   property A. One precise target is the Brodzki–Niblo–Nowak–Wright characterization: `Λ ↷ X` is
   amenable iff the Johnson class in bounded cohomology with coefficients in `W_0(Λ, X)^{**}` vanishes
   (recalled, not re-read).

## Proof

**1.**
- *SFT and conjugacy.* By item 1 of the time-lift node, `x ↦ x(1, ·)` conjugates `X_G` to `Y` with the
  joint action `(g, p)·y = g(σ_p y)`. The lift is cut out by the row SFT and by finitely many local rules
  for generators of `G`, so it is an SFT.
- *Minimality.* `P` alone acts minimally on `Y`.
- *Freeness.*
  - Suppose `g σ_p` fixes some `y`. Its fixed set is closed and nonempty.
  - It is `P`-invariant, because `g` commutes with `P` and `P` is abelian. So it is all of `Y`, by
    minimality.
  - Then `g = σ_(−p) ∈ G ∩ σ(P) = 1`, and `p = 0` because `Y` is free.
- *Rigidity.* This is item 2 of the time-lift node.
- *Exactness.* It passes to subgroups and to extensions by amenable groups, and `P` is amenable.
- *The carrier bullet.* Apply the same argument to `Λ_1`.

**2.**
- *The map to `M`.* Each automorphism descends to `M` by the universal property. `Aut(M, P)` consists of
  the translations of `M`, since they commute with a dense subgroup (the argument of
  `minimal-system-automorphisms-fix-every-proximal-factor`, item 5). So it is abelian.
- *Fibre bound.* `g ↦ g(y)` injects `Aut_0(Y)` into `π^(-1)(π y)`, by item 3 there.
- *Isometric extensions of expansive systems.* Let `Y → Z` be isometric with an invariant continuous fibre
  metric `ρ`, and suppose some fibre is infinite. Then it contains pairs with `ρ` arbitrarily small.
  - `ρ` is invariant, and by compactness small `ρ` forces small ambient distance.
  - So such pairs are never separated, which contradicts expansiveness.
- The split into (a) and (b) is the Furstenberg–Veech structure of the extension `Y → M` (recalled).

**3.** This is item 2 of the stratified node, with a single stratum. Its inputs (Li, Corollary D;
Künneth; `H_*(G_V) = 0`) do not see whether `Λ ↷ X` is amenable. ∎


## What this gives the RA lanes

- **bh-ra-counter: the sharpest time-lift target.**
  - We want a minimal, free, quantum-rigid `Z^d`-SFT `Y` with infinite fibres over its odometer or toral
    factor.
  - Through those fibres it should factor onto a **non-abelian profinite skew extension** `Z = M ×_c K` of
    its rotation, with `K` the profinite completion of Osajda's residually finite group `G`.
  - The right `G`-translations of `Z` must lift to cellular automata of `Y`.
  - There is one warning. A `G`-invariant finite partition only ever sees `K/N` for a finite-index `N`.
    So `Y` cannot be an almost 1-1 `G`-symmetric coding of `Z`: the lift has to use genuinely expansive
    extra data over `Z`.
  - Alternatively, use route (b), a relatively weakly mixing layer.
- **bh-ra-proof.** (RA′) implies a checkable dynamical corollary: automorphism groups of rigid minimal
  free `Z^d`-SFTs have only exact finitely generated subgroups, modulo shifts. A proof of (RA′) must be
  analytic (item 3). Rigidity is finite presentation of the V-full group, and finite presentation alone
  forces nothing about exactness.
- **The carrier (gate 2).** The criterion in item 1 is a new route to (★′). Any input inside an fp group
  of automorphisms of a rigid row, meeting the shifts trivially, gets a carrier. The known rows have
  virtually abelian `Aut`, so this needs rows with infinite fibres over their rotation.

## Lesson for general BH

**The time-lift face of (RA′) is a question about commutants.** A non-exact group acting by
automorphisms of a rigid minimal free `Z^d`-row gives a rigid, minimal, free, non-amenable SFT at once,
and a carrier if it is finitely presented. It must avoid the abelian translations of the equicontinuous
factor, and it needs infinite fibres over that factor.

There it can act only through a non-expansive distal factor, which works via profinite groups and so
exactly for residually finite inputs such as Osajda's, or in a relatively weakly mixing layer. Every
rigid row built so far is finite-to-one over its rotation.

Homology cannot decide the question: V-full groups of minimal systems are acyclic whether or not the
action is amenable. The decisive (RA′) statement is analytic. Its dynamical shadow is "rigid rows have
exact commutants", and its most promising counter-shape is a rigid row over a profinite skew extension
of its odometer.
