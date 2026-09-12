---
rg: 2
id: stabilizer-corrector-hermitianizes-zero-compression
kind: claim
title: A left corrector in the selected stabilizer makes every zero-compression payload involutive
distinct_from:
  central-marked-two-cycle-zero-compression-cell: that groupifies a zero compression once the selected source is a two-cycle; this proves every zero compression admits such a two-cycle after one existential left correction fixing the source.
  transitive-control-normalizer-forces-projectively-equal-payloads: that normalizes an entire irreducible control algebra and collapses all controlled payload blocks; this corrector need only stabilize one projection.
  tailored-checks-to-common-marked-group-extensions: that asks for the final ordinary-group extension; this reduces its analytic content to wordizing one projection-stabilizer condition.
---

**ESTABLISHED.**  Let `W` be a unitary and `Q` a projection on a Hilbert
space.  Then

```text
QWQ=0                                                     (SCZ1)
```

if and only if there is a unitary `S` such that

```text
SQS^*=Q,                  V=SW=V^*=V^-1,
QVQ=0.                                                     (SCZ2)
```

The forward construction is explicit.  Put

```text
R=W^*QW.
```

Equation `(SCZ1)` and its adjoint give `QR=0`.  Choose the self-adjoint
unitary `V` which swaps the equally dimensional subspaces `QH` and `RH`
using the restriction of `W`, and is the identity on `(Q+R)^perp`.  Set

```text
S=VW^*.                                                   (SCZ3)
```

Then `SQS^*=VRV=Q`, so `S` commutes with `Q`, and `SW=V`.  Conversely, if
`S` stabilizes `Q`, then

```text
QSWQ=S QWQ.                                              (SCZ4)
```

Thus `QVQ=0` is equivalent to `(SCZ1)`.

This removes the Hermitian-dilation obstruction from the selected-corner
problem at the operator level.  Combined with
`central-marked-two-cycle-zero-compression-cell`, an arbitrary payload needs
only:

```text
one existential word s which stabilizes the selected q,
the ordinary involution relator (sw)^2=1,
and the marked two-cycle grading cell for sw.            (SCZ5)
```

The remaining obstruction is exactly the first line of `(SCZ5)`.  If `q`
is the half-space projection `(1-z)/2`, it is the ordinary relation
`[s,z]=1`, but canonical trace fixes that half-space at density `1/2`.  For
the small joint atom `q=(1-y)(1-z)/4`, requiring `s` to commute with both
gradings stabilizes every joint atom and is stronger than the constructed
operator `S`, which is guaranteed to stabilize only `q`.  A finite-packet
normalizer has the same excess covariance and returns to the known
multiplicity-orientation wall.

Accordingly `(SCZ5)` is not yet a common-completion compiler.  It is a
strict reduction: neither an involutive payload nor a Hermitian LCU word is
intrinsically necessary.  The sole missing transducer is an ordinary-word,
payload-compatible stabilizer of one authenticated selected atom.
