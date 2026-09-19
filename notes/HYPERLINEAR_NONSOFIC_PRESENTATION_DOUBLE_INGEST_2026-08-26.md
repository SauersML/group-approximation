# Presentation-double attack: Cairn ingestion audit

Date: 2026-08-26

This note records the verified content ingested from the research attack on a
hyperlinear nonsofic group. It is an audit, not a claim that the open problem
has been solved.

## New material wired into Cairn

The genuinely new lane is the presentation double of the simple Leavitt
quotient. Write

```text
Q=F/K=EL_4(L_(F_2)(1,2)),       P=F *_K F,
```

with `F` a finitely generated free group. The following are now separate
Cairn nodes.

1. `simple-map-quotient-has-rigid-fd-restriction`: since a finitely generated
   infinite simple nonsofic group has no nontrivial finite-dimensional unitary
   representations, two finite-dimensional representations of `F` agreeing
   on `K` agree on all of `F`. The proof uses the invariant left-right space
   `Hom_K(v,u)`.
2. `shulman-double-forces-unstable-kernel-restriction`: Shulman's weak-MF
   theorem for `P` nevertheless gives exact finite-dimensional pairs `u_n,v_n`
   which converge pointwise on `K` in operator norm but remain uniformly
   separated on one fixed `f_0 notin K`. Thus exact restriction is injective
   in every dimension but has no dimension-uniform inverse modulus.
3. `leavitt-positive-rank-intertwiner-retention`: the remaining open theorem
   asks for **some choice** of the Shulman witness pairs and almost-reducing,
   almost-`K`-trivial sectors of the left-right representations on
   `HS(C^(d_n))`, normalized by the retained sector's own rank, on which
   `f_0` survives. No positive ambient density is assumed; the conditions
   themselves force the retained dimensions to become unbounded.
4. `leavitt-presentation-double-retention-proves-hyperlinear`: polar
   compression then gives a nontrivial homomorphism from the simple group `Q`
   to a tracial matrix ultraproduct, hence an injective one. Standard Cesaro
   tensor/direct-sum Haarization converts that abstract embedding to canonical
   trace microstates. This would make the already nonsofic `Q` hyperlinear.

This is a real reduction, but `(IR1)--(IR3)` are not proved.

## Material already present

Several other parts of the attack were already represented and were not
duplicated.

- The exterior/Fock rank amplifier and its dimension-defect failure are in
  `notes/FALSE_FERMIONIC_AMPLIFICATION.md`,
  `adaptive-tensor-amplification`, and
  `dimension-defect-controlled-mf-hyperlinear`.
- Operator-MF of symmetric doubles is `symmetric-double-weak-mf`; the warning
  that it does not select the reduced/canonical trace is already attached to
  that node and to `weak-mf-embedding-not-reusable`.
- The centralizing HNN/free-lamp identity is
  `centralizer-hnn-is-free-generalized-wreath`.
- The reduced-MF finish for the Kun--Thom double is already the
  `reduced-amalgam-canonical-trace-is-mf` lane.

## Correction to the free-lamp action proposal

The suggested Alekseev--Bradford certificate is valid as a conditional
implication, but it is not a route to the first seed. Cairn already closes
that shortcut at `halo-target-class-enrichment`, by two arguments:

1. `single-lamps-recover-set-action` recovers the forbidden Kun--Thom set
   action from any halo-action witness, independently of the target class;
2. more generally, if an action is a hyperlinear-class action but not a
   sofic-class action, one finite witness target is itself hyperlinear and
   nonsofic (`halo-locally-sofic-target-collapse` and
   `notes/FALSE_ACTION_APPROXIMATION_NO_SHORTCUT.md`).

Thus proving the proposed free-lamp action already contains the requested
group in an auxiliary target. It is a reformulation after a seed exists, not
an independent construction, and no new live route was added for it.

## Status

No hyperlinear nonsofic group has been proved. The accepted new frontier is
the quotient-specific relative-rank theorem
`leavitt-positive-rank-intertwiner-retention`; the other proposed positive
certificate was deduplicated against an existing circularity theorem.
