---
rg: 2
id: ra-forces-amenable-commutants-of-uniquely-ergodic-rigid-rows
kind: claim
title: A non-amenable finitely generated group of automorphisms of a minimal free quantum-rigid Z^d-SFT, meeting the shifts trivially and fixing an invariant measure, refutes (RA_free); so (RA_free) forces uniquely ergodic rigid rows to have amenable commutants and no free subgroups, the SU(2) target T1, if built, refutes (RA_free) rather than calibrating it, and the infinite-fibre time-lift line and the finite-fibre Toeplitz line are two measured instances of one refutation principle
requires:
  - quantum-rigid-minimal-topfree-subshift-actions-are-amenable
  - time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows
  - profinite-skew-layers-collapse-into-the-equicontinuous-factor
  - rigid-subshifts-over-free-factors-are-tight-almost-everywhere
  - quantum-rigid-subshifts-are-determined-by-thick-collars
distinct_from:
  time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows: that shows a non-EXACT commutant refutes (RA′); this shows a non-AMENABLE commutant that fixes an invariant measure already refutes the stronger (RA_free), and derives the amenability consequence for uniquely ergodic rows.
  rigid-subshifts-over-free-factors-are-tight-almost-everywhere: that shows invariant measures over Λ_0 × F_n force tightness and leaves tight spacetimes open; this identifies the time lifts of rigid rows as tight spacetimes and reduces the measured (RA_free) for them to amenability of commutants.
  quantum-rigid-subshifts-are-determined-by-thick-collars: that records that finite fibres carry an invariant measure, so the finite-fibre case of (CC′) is the non-existence statement (RA_fin); this is the infinite-fibre, time-lift counterpart.
---

**ESTABLISHED** (lane bh-invent-16, 2026-09-19; lane proof, elementary given the cited nodes; no
priority claimed). **Referee PASS** (bh-ref-q11, 2026-09-19) for the mathematics, with a scope correction: read (RA) as its free form (RA_free); see the Referee section.
- **Recalled standard inputs:**
  - a topologically amenable action with an invariant probability measure forces the group to be
    amenable (Anantharaman-Delaroche–Renault);
  - the Tits alternative for linear groups.
- **Open:** the T1 construction itself is **not built**. This node shows that T1, if built, refutes (RA_free), and lists
  exactly what it needs.

## Setting

- `Y ⊆ A^(Z^d)` is a minimal, free, `D`-quantum-rigid SFT.
- `σ(Z^d) ≤ Aut(Y)` are the shifts. They are central in `Aut(Y)`.
- `G ≤ Aut(Y)` is finitely generated with `G ∩ σ(Z^d) = 1`.
- `X_G` is its time lift over `G × Z^d`, as in `time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows`:
  minimal, free and quantum rigid.
- **(RA_free)**: a minimal, **free**, quantum-rigid subshift action of a finitely generated group is
  topologically amenable. The topologically free (RA) of
  `quantum-rigid-minimal-topfree-subshift-actions-are-amenable` is already refuted by a point stabilizer, so
  only the free form is at stake. Time lifts are free. (RA′) is as in that node.

## Statement

1. **Measured refutation.** Suppose `G` is non-amenable and fixes a `Z^d`-invariant Borel probability
   measure `μ` on `Y`. Then `X_G` is a minimal, free, quantum-rigid subshift over `G × Z^d` that carries an
   invariant probability measure. So its action is not topologically amenable, and (RA_free) fails.
2. **What (RA_free) predicts for rigid rows.** Assume (RA_free). Then:
   - if `Y` is uniquely ergodic, every finitely generated `G ≤ Aut(Y)` with `G ∩ σ(Z^d) = 1` is
     amenable;
   - the same holds if `Y` has only finitely many ergodic measures;
   - in either case `Aut(Y)` contains no non-abelian free group.

   This is a rigid analogue of the amenability results of Cyr–Kra for low-complexity shifts
   (arXiv:1708.06253, abstract read). Rigid rows have zero entropy
   (`quantum-rigid-subshifts-are-determined-by-thick-collars`).
3. **T1, if built, refutes (RA_free).** Let `Y` be as in target T1 of
   `profinite-skew-layers-collapse-into-the-equicontinuous-factor`. That is, `Y` is almost 1-1 over a
   minimal non-equicontinuous `Z = M ×_c SU(2)`, with a dense finitely generated group of lifted right
   translations. Suppose also that `Z` is uniquely ergodic and the singular set is null. Then:
   - `Y` is uniquely ergodic;
   - the lifted group contains `F_2`, and `F_2` meets the shifts trivially;
   - so T1 refutes (RA_free) by 1.

   T1 is therefore not a calibration: if built, it refutes (RA_free), and T2 refutes (RA′). Their
   non-existence would decide nothing.
4. **Time lifts are the tight regime.** `X_G` is determined by its restriction to the slab
   `{1} × Z^d`. So the measured (RA_free) question over `G × Z^d`, restricted to time lifts, is exactly item 2.
   That question is left open in item 3 of `rigid-subshifts-over-free-factors-are-tight-almost-everywhere`
   (for `G ⊇ F_n`).

## Proof

**1.**
- Transport `μ` to `X_G` through the conjugacy `x ↦ x(1, ·)` of the time-lift node, under which
  `(g, v)·y = g(σ_v y)`. It is `Z^d`-invariant by hypothesis and `G`-invariant because `G` fixes it.
- A topologically amenable action with an invariant probability measure forces the acting group
  `G × Z^d` to be amenable. Hence `G` would be amenable, a contradiction.

**2.**
- *Uniquely ergodic.* Every automorphism maps `Z^d`-invariant measures to `Z^d`-invariant measures, so it
  fixes the unique one. Apply 1.
- *Finitely many ergodic measures.* `G` permutes them, so a finite-index subgroup `G_1` fixes one. `G_1` is
  finitely generated and meets the shifts trivially, so it is amenable by 1, and hence so is `G`.
- *Free groups.* An `F_2 ≤ Aut(Y)` meets the central subgroup `σ(Z^d)` in a central subgroup of `F_2`,
  which is trivial. Apply the first two bullets to it.

**3.**
- *Unique ergodicity lifts.* `ρ : Y → Z` is injective off the preimage of the null singular set. So the
  pullback of the unique invariant measure of `Z` is the only invariant measure on `Y`.
- *Free subgroups.* A dense finitely generated subgroup of `SU(2)` is not virtually solvable, since the
  closure of a virtually solvable subgroup of a compact Lie group has abelian identity component. By the
  Tits alternative it contains `F_2`.
- *Lifting the free subgroup.* The lifted group `L ≤ Aut_0(Y)` embeds in `SU(2)` (item 3 of the collapse
  node), and its image is the given dense finitely generated group. So `L` contains a copy of `F_2`.
- *Meeting the shifts trivially.* That `F_2` meets the central subgroup `σ(Z^d)` in a central subgroup of
  `F_2`, which is trivial.

**4.** This is item 1 of the time-lift node: the row at `1` determines the lift. ∎

## The two lines (kept separate on the boards)

| | **Line F: finite fibres (bh-ra-proof)** | **Line I: infinite fibres (bh-invent-16)** |
|---|---|---|
| acting group | Osajda's `G` itself | `G × Z^d`, with `G ≤ Aut(Y)` |
| object | rigid (regular) Toeplitz `G`-subshift | rigid minimal free `Z^d`-row `Y` |
| fibres over the MEF | almost 1-1 over the `G`-odometer | infinite: a connected compact layer (distal door) or an RWM layer |
| invariant measure | Haar on the odometer, lifted | unique invariant measure of the row |
| statement at stake | (RA_fin), non-existence at non-amenable `G` | amenable commutants (item 2) |
| what it refutes | (RA′) directly (`G` non-exact) | (RA_free) via T1 (`SU(2)`); (RA′) via T2 (`∏ SU(n_i)` ⊇ Osajda's `G`) |
| obstruction known | nested periodic wire nets | profinite layers collapse; commensuration of `Z_1` |

**The common principle is item 1:** a minimal, free, rigid action of a non-amenable group that carries
an invariant probability measure refutes (RA_free). Both lines are searches for such an action.
- Line F gets the measure from finiteness.
- Line I gets it from unique ergodicity of an amenable row. It pays for this by needing infinite fibres
  over the MEF, since finite fibres give virtually abelian commutants. In the distal door those fibres must
  be connected.

## What T1 needs (checklist for any construction)

1. A minimal, free, quantum-rigid `Z^d`-SFT `Y`. The only rigid mechanism known is fixed-point
   (crossing-wire) simulation.
2. Almost 1-1 and proximal over `Z = M ×_c SU(2)`, where:
   - `M` is its MEF;
   - `c` is a continuous cocycle;
   - `Z` is minimal, non-equicontinuous and uniquely ergodic;
   - the singular set is null.

   SFT factor maps onto such effective `Z` are supplied in principle by Barbieri–Carrasco-Vargas–Rojas
   (arXiv:2401.07973, abstract read).
3. A dense finitely generated `G ≤ SU(2)` of right translations commensurating the closed singular set
   `Z_1` (item 4 of the collapse node), each lifted to a cellular automaton.

Items 1 and 2 together are already new: no rigid row with infinite fibres over its MEF is known. Item 3 is
the automorphism condition.

## Lesson for general BH

**Invariant measures turn automorphism groups into (RA_free)-tests.**
- A rigid, uniquely ergodic row with a non-amenable commutant is, through its time lift, a rigid minimal
  free action of a non-amenable group with an invariant measure, and (RA_free) forbids exactly that.
- So (RA_free) contains a clean statement about commutants: rigid, uniquely ergodic rows have amenable
  automorphism groups. It is the rigid counterpart of the Cyr–Kra amenability phenomenon for
  low-complexity shifts.

Of the two ways to supply the measure:
- the finite-fibre way (Toeplitz over the non-amenable group itself);
- the infinite-fibre way (unique ergodicity of an amenable row plus a connected compact layer).

Both amount to the same refutation principle. The first test of the second way, `SU(2)`, would already
refute (RA_free), not just calibrate it.

## Referee (bh-ref-q11, 2026-09-19): PASS for the mathematics; SCOPE CORRECTION to "(RA)"

**The arguments are correct.**
- **Item 1.**
  - `μ` is `G × Z^d`-invariant on `X_G`.
  - A topologically amenable action with an invariant probability measure forces the group to be amenable.
  - `X_G` is minimal, **free** and rigid by item 1 of the time-lift node.
- **Item 2.**
  - Unique ergodicity makes `G` fix `μ`.
  - With finitely many ergodic measures, a finite-index subgroup fixes one of them, and amenability passes back to `G`.
  - `F_2 ∩ σ(Z^d)` is central in `F_2`, hence trivial.
- **Item 3.**
  - Unique ergodicity lifts through an almost 1-1 map with null singular set.
  - A dense finitely generated subgroup of `SU(2)` is not virtually solvable, since a virtually solvable closure would have an abelian identity component. So Tits gives `F_2`.
  - Item 3 of the collapse node applies: `Z = M ×_c SU(2)` is distal (isometric over `M`), and almost 1-1 implies proximal. So the lifted group is isomorphic to its image and contains `F_2`.

**Scope correction.**
- (RA) as stated in `quantum-rigid-minimal-topfree-subshift-actions-are-amenable` concerns topologically free actions. It is already marked REFUTED on main (2026-09-18, lane proof) by `rigid-minimal-topfree-sft-with-non-amenable-point-stabilizer`, a topologically free action that is **not free**, with isotropy `F_2 × Z`.
- So, as written:
  - item 2 ("Assume (RA)") assumes a statement recorded as false;
  - items 1 and 3 ("refutes (RA)") would refute a statement already refuted.
- Everything here concerns time lifts, which are **free**. The correct reading is the unrefuted free form:
  - **(RA_free):** a minimal, free, quantum-rigid subshift action of a finitely generated group is topologically amenable;
  - its **measured corollary:** no minimal free rigid subshift over a non-amenable group carries an invariant probability measure.
- With "(RA)" replaced by "(RA_free)" throughout, items 1–4 hold as written.
- "T1 decides (RA)" should read "T1, if built, refutes (RA_free)". The non-existence of T1 would decide nothing.
- (RA′) (exactness) is unaffected.

**Repairs applied (bh-invent-16, 2026-09-19).** "(RA)" is replaced by "(RA_free)" throughout the body, and
"decides" by "if built, refutes", as the referee asked.
