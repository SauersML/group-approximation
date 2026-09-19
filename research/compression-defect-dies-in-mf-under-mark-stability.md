---
rg: 2
id: compression-defect-dies-in-mf-under-mark-stability
kind: claim
title: Point-norm stability replaces property (T) outright in the compression-defect non-MF mechanism
distinct_from:
  normal-kazhdan-defect-non-mf: that obtains corona collapse from a normal Kazhdan subgroup sitting inside the compression defect, and its transport is a spectral-gap argument; this deletes the Kazhdan hypothesis entirely and transports the same exact finite-dimensional kill across the approximation gap by point-norm stability at the mark, with no gap, no trace and no averaging.
  compression-defect-dies-in-finite-dimensions: that is the exact finite-dimensional half, proved by injective-implies-surjective on a finite-dimensional commutant, and says nothing about approximate representations; this is the transport of that half into the norm matrix corona, and its whole content is the transport hypothesis.
  matricial-stability-identifies-radicals: that computes the MF radical of a stable group and supplies no nontrivial finite-dimensionally invisible elements of its own; this supplies them -- the intrinsic compression-centralizer defect -- and is therefore the half that turns that computation into an obstruction.
  corona-commutant-no-growth: that is the refuted operator-norm commutant-invariance hinge, which tried to transport the same kill by making the corona relative commutant compression-invariant; this transports it by repairing the approximants instead, and so is untouched by the growth witness that refuted the hinge.
---

**ESTABLISHED.**  Let `H` be a countable group, `L<=H`, and let

```text
Comp(L)   = { s in H : s L s^-1 <= L },
G_comp(L) = <Comp(L)>,
D(H,L)    = << [g z g^-1, l] : g in G_comp(L), z in C_H(L), l in L >>_H
```

be the intrinsic compression-centralizer defect.  Then:

1. if `H` is fd-stable at some `w in D(H,L)` with `w != 1`, then
   `w in Rad_MF(H)` and `H` is **not MF**;
2. if `H` is fd-stable at every element of `D(H,L)`, then
   `D(H,L) <= Rad_MF(H)`;
3. if in addition some subset of `D(H,L)` normally generates `H`, then
   `Rad_MF(H)=H`: every norm-matrix-corona representation of `H` is trivial.

In particular all three hold when `H` is matricially stable in Dadarlat's
point-norm sense.

**Property `(T)` appears nowhere.**  Neither does a spectral gap, a Kazhdan
projection, a trace, a unitary structure on the exact half, a finite central
subgroup, torsion, or a mark of finite order.  This is the abstract
property-`(T)`-free non-MF mechanism in its cleanest form.

## Where the hypotheses are spent, and why one of them is unavoidable

The exact half is spent exactly once, in
`compression-defect-dies-in-finite-dimensions`: conjugation by a one-sided
compressor carries the commutant of the represented `L` injectively into
itself, and finite dimension upgrades injective to surjective.  Nothing else
in that half uses finiteness.

The approximate half is spent exactly once, in
`fd-mark-stability-forces-mf-invisibility`, and some hypothesis of that
strength is **forced**, not chosen.  `bare-self-copy-mf-calibration` gives a
group in which every exact finite-dimensional representation kills the marked
commutator, the group is nevertheless operator-MF, and in the escaping matrix
model the parent and child generated C*-algebras are literally equal.  So
`D(H,L) <= Rad_fd(H)` does not imply `D(H,L) <= Rad_MF(H)`, and no amount of
further algebraic self-copying closes the gap.

Read together with `corona-commutant-no-growth`, which is refuted, this
identifies what property `(T)` was actually doing in the earlier proofs: it
was a **robustness compiler** converting an approximate child commutant into a
controlled parent commutant on a finite-dimensional shadow, not the algebraic
obstruction.  The obstruction was always the exact finite-dimensional
theorem.  Normal generation is downstream of both: it globalizes a killed
local defect and never makes one robust.

## Honest limitation: this is a mechanism, not a construction

The node trades one global hypothesis for another.  Property `(T)` is
available for concrete arithmetic pairs; point-norm stability is not known
for any candidate in this program, and `map-matricial-stability-non-mf`
records that wall in its sharpest form -- proving operator-norm stability
for the Steinberg group would close the weak-MF lane negatively, while
proving weak MF would exhibit an explicit failure of that stability.

So this node is deliberately parked beside the Leavitt program rather than
inside it.  The route the program should actually run replaces the global
stability hypothesis by a *finite-coordinate* one:
`authenticated-coarse-fine-return-forces-mf-collapse`, whose input is a
single operator-norm support row rather than a repair of the approximants.
