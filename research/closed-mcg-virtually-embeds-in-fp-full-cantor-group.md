---
rg: 2
id: closed-mcg-virtually-embeds-in-fp-full-cantor-group
kind: claim
title: For every genus at least three some finite-index subgroup of the closed-surface mapping class group embeds in a finitely presented full clopen-transitive group of Cantor homeomorphisms
distinct_from:
  closed-mcgs-virtually-embed-in-punctured-mcgs: that asks for a finite-index subgroup inside a punctured-surface mapping class group; this asks for one inside a finitely presented full Cantor group, for example a Brin--Thompson group nV.
  closed-mcg-finite-index-subgroups-do-not-embed-in-v: that excludes the single host V = 1V; this asks for any host in the class, including nV for n >= 2, where that obstruction does not apply.
  every-closed-surface-mcg-embeds-in-some-aut-free-group: that asks for a host Aut(F_n); this asks for a Cantor-group host. Neither premise is known to imply the other.
---

**OPEN.** Let `Σ` be a closed orientable surface of genus `g ≥ 3`. Then there exist:
- a finite-index subgroup `L ≤ Mod(Σ)`;
- a Cantor space `Y` and a group `D ≤ Homeo(Y)` satisfying hypotheses 1--3 of
  `fp-clopen-transitive-full-cantor-groups-have-type-a-actions` (full, clopen
  transitive, finitely presented);
- an injective homomorphism `L → D`.

This premise feeds `closed-mcg-bh-via-full-cantor-host`.

## Instances

- **`V = 1V`: excluded** by `closed-mcg-finite-index-subgroups-do-not-embed-in-v`
  (Koberda's `Z² ∗ Z` of twist powers, and Bleak--Salazar-Díaz).
- **`nV`, `n ≥ 2`: open, and no node on main excludes it.**
  - The `V` obstruction does not transfer. Every finitely generated right-angled
    Artin group embeds in `2V` (`every-raag-embeds-in-brin-thompson-group-2v`,
    V. Salo arXiv:2103.06663), so `Z² ∗ Z ≤ 2V`.
  - The Heisenberg obstruction (`heisenberg-group-embeds-in-no-brin-thompson-group`,
    open for `m ≥ 2`) would not apply even if proved. Solvable subgroups of
    `Mod(Σ)` are virtually abelian (Birman--Lubotzky--McCarthy 1983, not re-read
    here), so `H_3(Z)` is not a subgroup of `Mod(Σ)`.
  - Kazhdan finiteness for `nV` (`kazhdan-subgroups-of-brin-thompson-groups-are-finite`)
    is open for `n ≥ 2`. Even if proved, it would exclude `L` only through an
    infinite subgroup of `Mod(Σ)` with property (T), and this lane knows of none.
    It did not search the literature for one.
  - `nV` is full and clopen transitive on the Cantor cube, since its elements are
    exactly the homeomorphisms given piecewise by finitely many dyadic brick
    maps. Its finite presentation is the Brin and Hennig--Matucci theorem, which
    this lane cites but has not read at source.
- **Not in this class.** The Aramayona--Funar groups `B_h` and `H_h` act on their
  Cantor set of ends through `V`, with kernel `PMod_c(Σ_h)`. So they are not
  groups of Cantor homeomorphisms, and
  `closed-mcg-in-asymptotic-mcg-is-bordered-or-infinite-in-v` treats them.
- **Other members of the class** include every finitely presented shell envelope
  (`shell-envelopes-are-full-cantor-groups`). They also include the host `2V_τ`
  of `odometer-2v-is-fp-simple-and-contains-bs12`, which contains `2V`.

## Attempts

1. **Literature re-check (lane bh-mcg, 2026-09-18).** Two arXiv API queries:
   - `all:"Boone-Higman"`: 16 results, newest 2609.01868;
   - `all:"mapping class group" AND all:"finitely presented simple"`: one result,
     BFFHZ 2503.21882.

   No abstract treats closed-surface mapping class groups or Brin--Thompson hosts
   for them. Only abstracts were read.
2. **Candidate mechanism, not pursued.** This is survey Remark 5.5's PIP route in
   a Cantor model.
   - **Calibration, genus one.** `PSL_2(Z)` acts on `RP¹` by integral projective
     maps. The Farey coding conjugates this action into Thompson's `T`, and
     blowing up the rational points puts it inside `V`.
   - **Genus g ≥ 3.** `Mod(Σ)` acts on `PMF(Σ) ≅ S^{6g−7}` by
     piecewise-integral-projective maps in train-track charts.
   - **What is missing:**
     - a coding of `PMF`, e.g. by train-track splitting sequences, in which every
       mapping class maps cylinders to finite unions of cylinders;
     - a proof that the resulting full group is finitely presented.
   - **A constraint from `V`.** Since no finite-index subgroup embeds in `V`, any
     such coding must be genuinely higher-dimensional. A one-dimensional Farey
     coding cannot work.
