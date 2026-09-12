---
rg: 2
id: regular-free-shift-fresh-trajectory-proof
kind: route
title: Place each reduced free-product word on a fresh finite trajectory arbitrarily far out in the enumeration
target: regular-enumerations-can-make-near-shift-free-product
requires: []
artifacts:
  - research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md
---

Fix a finite partial bijection sigma:P->N, a nonidentity reduced
word w in P*<s>, and an integer M. We extend sigma so that w,
evaluated as a partial permutation, is defined at some n>M and
moves n. All prescribed evaluations then persist under extensions.

Write w in alternating nonidentity P syllables and nonzero powers
of s, allowing either kind at the ends, and evaluate right to left.
Choose the initial integer above all values of sigma and sufficiently
far from zero for the initial shift, if any. Pure shift words already
move every sufficiently large integer.

At a P syllable g!=1, its current input u has no assigned P label.
Choose h with h and g*h outside the finite domain assigned so far.
Only finitely many h are forbidden, and infinitude of P gives a
choice; h and g*h differ since the action is free. Assign nu(h)=u.
Choose a fresh output v, assign nu(g*h)=v, and make v so large that
the following shift block, if any, ends at another unassigned integer.
Its endpoint can also avoid all earlier trajectory endpoints. This
is possible because that block has a fixed nonzero exponent and
only finitely many values are forbidden. All intermediate shift
values can be kept nonnegative by taking v large enough. At the
last such choice also ensure the final endpoint differs from n.

Thus every P step is its prescribed regular action and every shift
step is the required translation. If there is only a single P
syllable and no shifts, the same two-label assignment suffices.
The completed finite trajectory proves the extension assertion.

For each pair (w,M), the condition that some n>M is a defined moved
point is open: a witness uses finitely many values of the enumeration
and its inverse. The extension assertion proves density. Intersect
over the countably many pairs. Every nonidentity free-product word
then moves infinitely many points, so its near permutation is not
identity. This gives the asserted faithful canonical map. The space
of bijections between two countably infinite sets is a Polish Baire
space in this topology, so this countable intersection of dense open
sets is dense and comeagre. Equivalently its density follows by the
explicit back-and-forth construction below without invoking category.

For the effective version, the word problem of P produces an
enumeration of distinct elements by retaining the first word for
each new element. It decides free-product normal forms and all the
finite exclusions in the trajectory construction. Schedule all
nonidentity reduced words w and bounds M. Interleave their witness
requirements with two totality requirements: assign a value to the
next as-yet-unassigned P element, and assign a preimage to the next
as-yet-unassigned integer. Each finite stage extends the previous
partial bijection. For a queried group word or integer, simulate
until its assignment occurs. Totality guarantees termination and
gives the claimed computable bijection and inverse.

One may include nu(1)=0 in the initial prescription. There is no
bounded displacement, arithmetic residue rule, or finite-state
assumption in this construction.
