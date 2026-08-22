---
rg: 2
id: central-marked-involution-zero-compression-cell
kind: claim
title: Two gradings groupify a selected zero compression for an involutive payload
distinct_from:
  grading-zero-corner-does-not-orient-controlled-payload: that uses one grading and swaps its two halves globally; this localizes the swap to one central marked sector and leaves the complementary sector existentially arbitrary.
  marked-swap-star-compiler: that needs two partial swaps with one common source and orthogonal ranges; this gives one exact selected-corner swap and no source-saturation theorem.
  tailored-checks-to-common-marked-group-extensions: that asks for arbitrary LCU payloads; this closes its final zero-compression gate only when the payload has already been compiled to one involution word.
---

**ESTABLISHED.**  There is a finite ordinary-group cell which expresses a
proper selected-corner zero compression without exchanging the whole ambient
space.  Take involutions `w,y,z` with relations

```text
[y,w]=[y,z]=1,                 wzw=y z.                (MZC1)
```

Put

```text
p=(1-y)/2,                    q=p(1-z)/2.              (MZC2)
```

Then, in every unitary representation,

```text
w q w=p-q,                    q w q=0.                 (MZC3)
```

Thus `w` exchanges the two `z`-atoms only inside the central marked sector
`p`.  On `(1-p)H`, `(MZC1)` merely says that the auxiliary grading `z`
commutes with `w`; choosing `z=1` there permits an arbitrary complementary
action of `w`.  This removes the equal-half constraint on the **whole**
representation in the one-grading construction.

The cell is also complete for exactly the intended class.  If `W=W^*=W^-1`
and `Q` is any projection with

```text
QWQ=0,                                                   (MZC4)
```

then `Q'=WQW` is orthogonal to `Q`.  Set

```text
P=Q+Q',        Y=1-2P,        Z=1-2Q.                  (MZC5)
```

The involutions `Y,Z,W` satisfy `(MZC1)`, and the projections decoded by
`(MZC2)` are precisely `P,Q`.  Spectator summands may be added with `Y=Z=1`
and arbitrary involutive `W`.  Hence the presentation imposes no hidden
condition beyond zero compression and involutivity, up to this harmless
existential choice of gradings.

There is a dimension-free robust estimate.  For exact commuting involutions
`y,z,w`, if

```text
delta=||wzw-yz||_2,
```

then

```text
||q w q||_2 <= delta/2.                                (MZC6)
```

Fixed-packet rounding gives the same conclusion with a universal additive
multiple of the involution and commutator defects.

The selected source is automatically visible at fixed canonical density.
If `y,z,yz` are nonidentity in the presented group, canonical-trace
microstates have

```text
tau(q)=1/4(1-tau(y)-tau(z)+tau(yz)) ->1/4.             (MZC7)
```

Thus this single source does not require a separate finite-packet
saturation theorem.  Exact nontriviality can be certified in the intended
zero-compression witness whenever `Q` is nonzero: then `Q'=WQW` and
`Q+Q'` are nonzero, so `z`, `yz=1-2Q'`, and `y` all act nontrivially.

## Exact boundary

This is a genuine selected-corner transducer, but it is not yet a general
LCU compiler.  The word `w` must itself be an involution.  The standard
Hermitian dilation of a controlled LCU unitary is an additive `2 x 2` block
matrix, not automatically an ordinary group word.  Moreover `(MZC1)` forces
the marked source to lie in a two-cycle of `w`; for a general unitary,
`qWq=0` only makes `q` orthogonal to `WqW^*` and does not make their sum
`W`-invariant.  Therefore this cell strictly narrows
`tailored-checks-to-common-marked-group-extensions` to:

```text
compile the losing check as the selected compression of one involution word.
                                                               (MZC8)
```

No finite Bass--Serre extension or packet-type selection is used in
`(MZC1)`; the payload word occurs in the two-cell itself.  Accordingly the
canonical-extension theorem for fresh stable letters does not refute this
cell.  What remains is the payload-sensitive Hermitian word compiler, not
the zero-compression relation.
