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

Let `G` be a countable MF group and let `g != 1`.  Then there exist a matrix
corona `Q`, a faithful homomorphism `u : G -> U(Q)`, and a nonzero projection
`P` in `Q` with

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
converses are unavailable here, but no strictness example is known: the weak
Shulman/Carrión--Dadarlat--Eckhardt convention and Schafhauser's
trace-controlled one are recorded as a priori different in `notes/NOTEPAD.md`,
and no group is known to separate them.

## Position among the open holes

This claim is formally stronger than the other open hole of the cluster:
`corner-visibility-gives-rate-profile` derives
`mf-trace-gap-defect-ratio-models` from it, because a trace gap bounded below
makes the rate `epsilon_n^2/kappa_n -> 0` automatic.  No converse is known.
Anyone choosing between
the two should work the rate claim; this one is worth stating because it
records the structural mechanism and because its known instances below are
proved by construction rather than by rate control.

## Known instances

The following group-wide or elementwise instances are established.

* **Residually finite, and more generally LEF.**  The regular representation
  of a finite quotient separating `g` is an exact model with `tr(g)=0`.
* **Amenable.**  `C^*(Gamma)` is nuclear and satisfies the UCT, and its
  canonical trace is faithful, so by Tikuisis--White--Winter that trace is
  quasidiagonal, hence an MF trace, and the proof of
  `regular-character-mf-trace-implies-group-mf` turns it into operator-norm
  models with `tr(g) -> 0`.  This is the one instance where the conclusion is
  a deep theorem rather than a construction.
* **Semidirect products of an amenable group by a free group.**
  Rainone--Schafhauser, arXiv:1601.06090v2, Theorem 1.4, prove that the
  canonical trace on `C*_lambda(A semidirect F_r)` is an MF trace.  Restricting
  its norm microstates to the canonical group unitaries gives `(I')` for every
  nontrivial element.
* **Elements of a finite normal subgroup**, by
  `mf-finite-normal-tracially-visible`.
* **Antipodal elements over a central involution**, by
  `mf-antipodal-sign-corner-visibility`.
* **Finite central phase-conjugate elements**, by
  `mf-finite-central-phase-corner-visibility`; this includes the antipodal
  case and allows the visible element to have arbitrary order.

These are the instances proved or source-verified here; they do **not** cover every group now
known to be weak MF.  In particular, Shulman's 2026 symmetric-amalgam theorem
produces weak-MF doubles while explicitly controlling no prescribed trace
(`shulman-symmetric-double-has-no-stable-trace-upgrade`).  Visibility of a
nontrivial fold-kernel word in those doubles is precisely extra trace data,
not a consequence of their norm-corona embedding.  The honest reading of the
present claim is therefore that it asks to extend trace-controlled MF from
the amenable/LEF and finite-phase cases to every weak-MF-visible element.

## Literature convention guardrail (checked through August 2026)

The universal statement is not a theorem hidden behind terminology.
Korchagin, arXiv:1704.06906v3, Definition 1, uses the weak embedding
`G -> U(prod M_n/directSum M_n)` and explicitly observes that faithfulness
can be lost after passage to normalized Hilbert--Schmidt norm.  Shulman,
arXiv:2603.13564v2, Definition 3, uses the same weak convention (and flags
the stronger convention separately); her Theorems 10 and 20 establish
norm-corona permanence, not trace selection.  By contrast Schafhauser,
arXiv:2306.02498v2, Definition 1.1, builds normalized-trace convergence and
approximation of the reduced regular representation into the word "MF" and
then correctly concludes that every MF group **in that stronger sense** is
hyperlinear.  That sentence cannot be imported into the present weak
convention.

Thus establishing this claim in general would give a new solution of
`mf-implies-hyperlinear`; no source located in the current literature sweep
provides the missing trace-selection step.  Bachner--Dogon--Lubotzky,
arXiv:2508.17392v3, Proposition 1.6, supplies only the finite-normal-kernel
case already recorded in this cluster.

## What the corner may look like

Over a Kazhdan source the shape of an admissible corner is already
constrained: by `bounded-rank-corners-excluded` a detecting corner cannot
have bounded rank once the Kazhdan image has no nontrivial representations
in those dimensions, so the approximate-joint-eigenvector construction is
unavailable there.  This is only an **unbounded-rank** conclusion, not a
positive-density one.  The isotypic corner of a finite normal subgroup or
the spectral corner of a finite central phase can have rank `o(d_n)` in the
ambient matrices; its own normalized corner trace is exactly why it remains
usable.  Thus the known constructions and the obstruction are compatible:
over a minimally almost periodic Kazhdan source a successful corner must
have ranks tending beyond every fixed bound, but it may still occupy
vanishing ambient density.
