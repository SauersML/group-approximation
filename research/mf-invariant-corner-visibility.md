---
rg: 2
id: mf-invariant-corner-visibility
kind: claim
title: Every MF-visible element is visible in an invariant corner
distinct_from:
  mf-trace-gap-defect-ratio-models: That claim asks for a quantitative rate in a fixed model; this one asks for no rate at all, only that some operator-norm realization see the element tracially.
  mf-finite-normal-tracially-visible: That established claim produces such a corner when the element lies in a finite normal subgroup; this claim asserts one always exists.
  bounded-rank-corners-excluded: That established claim constrains the rank of a detecting corner over a Kazhdan source; this one asserts existence of a corner for an arbitrary element of an MF group, with no Kazhdan data in the hypotheses.
---

Let `G` be a countable MF group, realized by a faithful homomorphism
`u : G -> U(Q)` into a matrix corona, and let `g != 1`.  Then there is such a
realization together with a nonzero projection `P` in `Q` with

```text
u(a) P u(a)^* = P for all a in G,                                 (I1)
limsup Re tr_(r_n)(P u(g)) < 1,                                   (I2)
```

where `(I2)` is computed in the corner `PQP`, itself a matrix corona of the
lifted ranks `r_n`, with its own normalized traces.

## The corner is a device, not a hypothesis

`(I1)`--`(I2)` are equivalent to the corner-free statement

```text
(I') for every finite F and every delta>0 there is an operator-norm local
     model of G on F with defect delta in which Re tr(g) <= 1-c_g,
```

with `c_g>0` independent of `F` and `delta`.  Indeed a corner compression of
a corona realization is again carried by operator-norm local models, with the
corner's own normalized trace (`corner-renormalization-cost` `(C1)`: the
compression costs nothing in operator norm), which is `(I')`; conversely,
given `(I')`, amplify a faithful MF realization and an `(I')`-model by
identity blocks to a common dimension and take their direct sum --- operator
norm data and faithfulness come from the first summand, and the trace is the
average, so `Re tr(g) <= 1-c_g/2` --- and then `P=1` is an invariant corner
satisfying `(I1)`--`(I2)`.

So what this claim really asserts is **elementwise trace-controlled MF**:
that the weak norm-corona property can always be upgraded, one element at a
time, to a model whose trace also sees that element.  The corner is how one
would build such a model, not an extra assumption.  That places it in the
chain

```text
regular character is an MF trace  =>  this claim  =>  mf-implies-hyperlinear
```

--- the first implication because the proof of
`regular-character-mf-trace-implies-group-mf` manufactures exactly such
models, the second by `mf-implies-hyperlinear-via-invariant-corner`.  Both
implications are strict as far as anything known here: the weak
Shulman/Carrion--Dadarlat--Eckhardt convention and Schafhauser's
trace-controlled one are recorded as a priori different in `notes/NOTEPAD.md`,
and no group is known to separate them.

## Position among the open holes

This claim is strictly stronger than the other open hole of the cluster:
`corner-visibility-gives-rate-profile` derives
`mf-trace-gap-defect-ratio-models` from it, because a trace gap bounded below
makes the rate `epsilon_n^2/kappa_n -> 0` automatic.  Anyone choosing between
the two should work the rate claim; this one is worth stating because it
records the structural mechanism and because its known instances below are
proved by construction rather than by rate control.

## Known instances

The claim holds, for every nontrivial element at once, in four families.

* **Residually finite, and more generally LEF.**  The regular representation
  of a finite quotient separating `g` is an exact model with `tr(g)=0`.
* **Amenable.**  `C^*(Gamma)` is nuclear and satisfies the UCT, and its
  canonical trace is faithful, so by Tikuisis--White--Winter that trace is
  quasidiagonal, hence an MF trace, and the proof of
  `regular-character-mf-trace-implies-group-mf` turns it into operator-norm
  models with `tr(g) -> 0`.  This is the one instance where the conclusion is
  a deep theorem rather than a construction.
* **Elements of a finite normal subgroup**, by
  `mf-finite-normal-tracially-visible`.
* **Antipodal elements over a central involution**, by
  `mf-antipodal-sign-corner-visibility`.

Every MF group the repository can currently name falls under one of these, so
the claim is not near a counterexample; the honest reading is that it asks to
extend "the regular character is an MF trace" from the amenable and LEF cases
to all MF groups.

## What the corner may look like

Over a Kazhdan source the shape of an admissible corner is already
constrained: by `bounded-rank-corners-excluded` a detecting corner cannot
have bounded rank once the Kazhdan image has no nontrivial representations
in those dimensions, so the approximate-joint-eigenvector construction is
unavailable there.  Nothing in that obstruction touches the corners which
*are* known to work here --- the isotypic corners of a finite normal subgroup
and the sign corner of a central involution both have rank a fixed fraction
of the ambient dimension.  The two statements are compatible and complementary:
admissible corners must be macroscopic, and the established constructions
produce exactly macroscopic ones.
