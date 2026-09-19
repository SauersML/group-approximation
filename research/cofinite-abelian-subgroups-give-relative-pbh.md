---
rg: 2
id: cofinite-abelian-subgroups-give-relative-pbh
kind: claim
title: A finitely presented group with a faithful action that has finitely generated point stabilizers and a finite-rank free abelian subgroup with finitely many orbits satisfies relative PBH, through Houghton ports; such actions have finitely many ends
distinct_from:
  amalgams-of-orbit-finite-actions-are-type-a2: that is the gluing lemma, which needs a type [A_2] actor already extending the port's action; this supplies such actors for every action of a finite-rank free abelian group with finitely many orbits, from Brown's Houghton group H_3, so the port hypothesis becomes a condition on the input alone.
  boone-higman-implies-relative-permutational-bh: that derives relative PBH from Boone--Higman; this derives it from a one-dimensional condition on one action of the group, with no simple group and no finiteness of pair orbits.
  fp-strongly-shift-similar-admits-type-a-action: that needs the host to contain the finitary symmetric group, which forces finitely many pair orbits; here the host may have infinitely many pair orbits, and the Houghton factor supplies the pair-orbit finiteness.
  relative-pbh-closed-under-finite-direct-products: that combines two given type [A_2] pairs; this builds one from a single action of the input.
---

**ESTABLISHED** (lane bh-invent-02, 2026-09-18). This is a lane proof, elementary given
Brown's theorem and the gluing lemma. It has not been reviewed, and no priority is claimed.

Terms are as in `amalgams-of-orbit-finite-actions-are-type-a2`:
- *type [A_2]* means a finitely presented group, finitely generated point stabilizers, and
  finitely many orbits on pairs;
- *relative PBH* for `D` is a sharp embedding of `D` in `(P, ker(P ↷ S))` for some type [A_2]
  action `P ↷ S`.

**Definition.** An action `D ↷ X` is *abelian-cofinite* if some subgroup `A ≤ D` with
`A ≅ Z^n` (`n ≥ 1`) has finitely many orbits on `X`. It is *cyclically cofinite* if one can
take `n = 1`.

## Statement

1. **Houghton ports.** Let `A ≅ Z^n` act on a set `Y` with finitely many orbits. Then some
   finitely presented `Γ ⊇ A` acts on `Y' = Y × [2^n]` with type [A_2], and restricted to `A`
   this action is the product action (`A` on `Y`, trivially on `[2^n]`).
2. **Relative PBH.** Let `D` be finitely presented, acting faithfully on `X` with
   finitely generated point stabilizers, and abelian-cofinite through `A ≅ Z^n`. Then
   `P = Γ *_A D` acts on `X × [2^n]` with type [A_2], and `D` meets its kernel trivially.
   So `D`, and every subgroup of `D`, satisfies relative PBH.
3. **Necessary conditions.** A finitely presented `D` with such an action has solvable word
   problem. Each of its finitely many orbits has a Schreier graph with at most two ends per
   `A`-orbit it contains. So, for instance, it is never the action on the vertices of a
   locally finite tree with infinitely many ends on which `D` acts cocompactly.

## Proof

**Houghton's element.** Let `H_3` be Houghton's group on `R = [3] × N`: the permutations that
are eventually translations on each ray.
- `H_3` is finitely presented (K. S. Brown, *Finiteness properties of groups*, JPAA 44
  (1987); `H_n` is of type `F_{n-1}`).
- It contains `FSym(R)`, so it has finitely many orbits on `R × R`.
- The stabilizer of a point `x` is isomorphic to `H_3`: renumber the ray of `x` to close the
  gap. So it is finitely generated, and `H_3 ↷ R` is type (A).
- Define `g ∈ H_3` by:
  - `(2,k) ↦ (2,k-1)` and `(3,k) ↦ (3,k-1)` for `k ≥ 1`;
  - `(2,0) ↦ (1,0)` and `(3,0) ↦ (1,1)`;
  - `(1,k) ↦ (1,k+2)`.
  It is a bijection, and it translates the three rays by `+2, -1, -1`. It has exactly two
  orbits, `R_2 ∪ {(1,2k)}` and `R_3 ∪ {(1,2k+1)}`, and each is a free `⟨g⟩`-orbit.

**Item 1.** An orbit of `A` on `Y` is `A/L` for some `L ≤ A`.
- **Splitting.** Let `L' ⊇ L` be the saturation of `L`, which has rank `r` and contains `L`
  with finite index, and write `A = M ⊕ L'` with `M ≅ Z^{n-r}`.
- **One block.** Put `Γ_L = H_3^{n-r} × L'`, acting on `R^{n-r} × (L'/L)` factorwise, with `L'`
  acting on `L'/L` by translation.
  - Send `A` into `Γ_L` by sending the `i`-th basis vector of `M` to `g` in the `i`-th
    factor, and `L'` identically. This is injective.
  - `M` acts freely on `R^{n-r}` with `2^{n-r}` orbits, and each `A`-orbit is `M·p × L'/L`,
    with stabilizer `L`. So as an `A`-set, `Γ_L`'s set is `2^{n-r}` copies of `A/L`.
  - `Γ_L` is finitely presented. Its point stabilizers are `H_3`-stabilizers times `L`,
    which are finitely generated. Its pair orbits are products of finitely many pair orbits.
    So `Γ_L` is type [A_2].
- **All orbits.** Each orbit `O_j ≅ A/L_j` of `Y` gives `2^n` orbits of `Y'`.
  - Take `2^{r_j}` blocks `Γ_{L_j}` for each `j`, and let `Γ` be their direct product,
    acting on the disjoint union of the blocks' sets, each factor on its own block.
  - Send `A` in diagonally.
  - A product of finitely many type [A_2] actions on a disjoint union is type [A_2]: the
    stabilizer of a point is a stabilizer in one factor times the other factors, and pair
    orbits across two blocks are products of orbits.
  - Its `A`-set is isomorphic to `Y'`, orbit type by orbit type. Transport the action along
    such an `A`-bijection.

**Item 2.** Apply item 1 to `Y = X`. Then `D` acts on `X × [2^n]` through `X`. Check the
hypotheses of the gluing lemma for `Γ *_A D`:
- (a) `Γ` and `D` are finitely presented, and `A` is finitely generated;
- (b) `A` has finitely many orbits;
- (c) the stabilizers of `Γ` and `D` are finitely generated, and those of `A` are subgroups
  of `Z^n`;
- (d) `Γ` has finitely many orbits on pairs.
So `P = Γ *_A D` is type [A_2]. Since `D ↷ X × [2^n]` is faithful, `D ∩ ker = 1`. ∎

**Item 3.**
- **Word problem.** By item 2 and `a2-kernel-removal-forces-recursive-kernel` (a), `D`
  embeds in `P/K`, whose word problem is co-r.e. A finitely presented group has r.e. word
  problem, so `D`'s word problem is recursive.
- **Ends.** Fix a finite generating set of `D` in which the basis `t_1, ..., t_n` of `A`
  have length at most `ℓ`. Each `A`-orbit `O ≅ A/L_j` is the image of the Cayley graph of
  `A/L_j` under an injective `ℓ`-Lipschitz map into the Schreier graph.
  - Let `F` be finite, and `F'` its `ℓ`-neighbourhood.
  - Outside the finite preimage of `F'`, the Cayley graph of `A/L_j ≅ Z^k × (finite)` has at
    most two infinite components, and exactly one when `k ≥ 2`.
  - Adjacent points there map to points joined by paths of length `≤ ℓ` avoiding `F`.
  - Removing a finite set leaves finitely many components, so the finite ones hold finitely
    many points. Every infinite component of the Schreier graph minus `F` therefore contains
    the image of an infinite component, and each image lies in one component.
  So the ends number at most `2 × #{A-orbits}`. Taking `X × [2^n]` does not change this. ∎

## Calibration: which recorded groups are abelian-cofinite hosts

- **Houghton groups.** `H_n` for `n ≥ 3`, via the analogue of `g` with ray translations
  `(n-1, -1, …, -1)`.
- **Houghton-like groups.** `H_n(G)` for finitely presented, strongly shift-similar `G`
  (`fp-strongly-shift-similar-groups-have-fp-houghton-like-groups`), via the Houghton element
  inside `H_n ≤ H_n(G)`.
  - Stabilizers are finitely generated by `fp-strongly-shift-similar-admits-type-a-action`,
    applied to the strongly shift-similar representation (MZ Proposition 5.5). That this
    representation is the given action transported along a bijection `[n] × N ≅ N` was not
    rechecked here.
  - So every group certified by the shift-similar route lies in a cyclically cofinite finitely
    presented group.
- **The odometer group.** Let `B = V_(2,1)(⟨a⟩)`. Then `L_od = FSym(Z) ⋊ B` acts on the
  integers, with the odometer `a` as a single free orbit. It is finitely presented by
  `fsym-by-odometer-group-on-the-integers-is-fp` (lane proof).
  - Its point stabilizer `Stab(0)` maps onto `B` (correct `b` by the transposition
    `(0 b(0))`), with kernel `FSym(Z∖{0})`.
  - `Stab(0)` is finitely generated, and so is `Stab_B(0)`, so `B` itself is a host
    (`higman-closure-of-abelian-cofinite-hosts-is-port-faithfulness`, item 1).

All of these are already in the permutational class. **No group with Boone--Higman open is
yet known to embed in an abelian-cofinite host.** Finding one is
`decidable-groups-embed-in-abelian-cofinite-hosts`, and each instance would be a new case of
the relative conjecture (FFWZ Conjecture 1.8).

## Lesson for general BH

**Pair-orbit finiteness is cheap and borrowable.**
- Brown's `H_3` lends it to any input through one infinite-order element with finitely many
  orbits, because the gluing lemma only asks the *port* to be orbit-finite.
- So relative PBH, FFWZ's intermediate form of BH, needs no high transitivity, no simple
  group and no finitary symmetric subgroup. It needs:
  - finite presentation;
  - finitely generated stabilizers;
  - one coarsely one-dimensional coordinate: a `Z^n`-orbit structure, whose Schreier graphs
    have finitely many ends.

**What this moves.**
- *The relative conjecture.* It becomes a Higman-type embedding problem with an ends
  constraint, and no longer asks for a host that is at once highly transitive and finitely
  presented.
- *Where the rest of BH sits.* The kernel of `Γ *_A D` is free, and removing it is FFWZ
  Question 5.9, i.e. finite presentation of `⟨Γ, D⟩ ≤ Sym(X × [2^n])`.
- *The ends constraint* shows the one-dimensional coordinate must be built. Cocompact
  actions on locally finite trees with infinitely many ends never supply it.
