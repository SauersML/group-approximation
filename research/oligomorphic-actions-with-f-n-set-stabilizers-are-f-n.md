---
rg: 2
id: oligomorphic-actions-with-f-n-set-stabilizers-are-f-n
kind: claim
title: A group acting with finitely many orbits on k-element subsets for all k <= n+1, whose setwise stabilizers of such subsets are of type F_n, is itself of type F_n; with n = 2 this certifies finite presentation, and hence type (A), from 3-set data alone
distinct_from:
  finitary-symmetric-extensions-of-oligomorphic-actions-are-fp: that assumes the acting group finitely presented and deduces finite presentation of a finitary symmetric extension; this deduces finiteness of the acting group itself from its finite-set stabilizers.
  pl-rearrangement-groups-have-two-transitive-orbit-actions: that reduces type (A) of an orbit action to finite presentation of the group; this supplies finite presentation from stabilizers of 3-element sets when the action is 3-oligomorphic.
---

**ESTABLISHED** (lane proof, elementary given Brown's criterion; not reviewed; no novelty claimed, and it
is presumably folklore). Input: Brown's criterion, K. S. Brown, *Finiteness properties of groups*,
J. Pure Appl. Algebra 44 (1987), Prop. 1.1. It says: if `G` acts cellularly on an `(n−1)`-connected
CW complex with finitely many orbits of cells of dimension `≤ n`, and the stabilizer of every `p`-cell
is of type `F_{n−p}`, then `G` is of type `F_n`. It is standard and was not re-read.

## Statement

Let `G` act on a set `O` with `|O| ≥ n + 1`. Assume that for every `k ≤ n + 1`:
- (O) `G` has finitely many orbits on `k`-element subsets of `O`;
- (St) the setwise stabilizer `G_σ` of every `k`-element subset `σ` is of type `F_n`.

Then `G` is of type `F_n`. For `n = 2`: finitely many orbits on subsets of size `≤ 3`, with finitely
presented stabilizers, make `G` finitely presented. If also point stabilizers are finitely generated and
the action is faithful, it is of type (A).

## Proof

- **The complex.** Let `Δ` be the full simplex on `O`, whose simplices are the nonempty finite subsets.
  It is contractible, so its `n`-skeleton `Δ^{(n)}` is `(n−1)`-connected. Let `X` be the barycentric
  subdivision of `Δ^{(n)}`. It is homeomorphic to `Δ^{(n)}`, and `G` acts simplicially.
- **Cells.** A `p`-simplex of `X` is a chain `σ_0 ⊊ σ_1 ⊊ … ⊊ σ_p` of subsets of size `≤ n + 1`. An
  element stabilizing the chain fixes each `σ_i` (their sizes differ), so the action is rigid.
- **Finitely many orbits.** By (O) there are finitely many orbits of top sets `σ_p`. For fixed `σ_p` there
  are finitely many chains ending at it. So there are finitely many orbits of cells in every dimension.
- **Stabilizers.** The stabilizer of the chain is the preimage, under `G_{σ_p} → Sym(σ_p)`, of the finite
  subgroup preserving every `σ_i`. So it has finite index in `G_{σ_p}`. It is of type `F_n` by (St),
  since finite-index subgroups of `F_n` groups are `F_n`. In particular it is of type `F_{n−p}`.
- **Conclusion.** Brown's criterion gives `F_n`.
- **Type (A).** For `n = 2`, faithfulness, (O) for pairs, finitely generated point stabilizers and finite
  presentation are the four clauses. ∎

## Lesson for general BH

Finite presentation of an actor need not be proved separately from its action. If the action is
3-oligomorphic and the stabilizers of sets of size at most 3 are finitely presented, the actor is finitely
presented and the action is of type (A). So the fp clause of type (A), the one BFFHZ's route actually pays
for, reduces to stabilizers of 3-element sets. Constructions that make finite-set stabilizers into
products of copies of one known `F_∞` group, as circle and interval groups do, certify finiteness for
free. This is the finiteness engine behind `circle-pl-groups-inherit-finiteness-from-interval-groups`.

## Referee (bh-ref-kourovka-b, 2026-09-18): PASS

**Verdict: PASS.** It is a clean application of Brown's criterion, as lane bh-near-actions says.
- **The complex.** The `n`-skeleton of the full simplex is `(n−1)`-connected. The barycentric
  subdivision makes the action rigid, since the sets in a chain have distinct sizes.
- **Orbits.** Finitely many orbits of cells in every dimension follow from (O) for `k ≤ n + 1`.
- **Stabilizers.** Chain stabilizers have finite index in `G_{σ_p}`, so they are `F_n` ⊆ `F_{n−p}`.
- **Type (A).** Ordered pairs come from 2-subset orbits and point orbits. (St) at `k = 1` already
  gives finitely generated point stabilizers.
- **Priority.** No novelty is claimed. This is the standard "Brown on a complex of finite subsets"
  argument, in the spirit of Brown and Stein.
