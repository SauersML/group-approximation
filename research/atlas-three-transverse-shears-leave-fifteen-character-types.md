---
rg: 2
id: atlas-three-transverse-shears-leave-fifteen-character-types
kind: claim
title: Three transverse Atlas shears leave exactly fifteen of sixty-four CK character types degenerate
distinct_from:
  atlas-two-transverse-shears-have-determinant-balance-test: that gives the two-dimensional determinant test and its determinant-zero locus; this uses every transverse target available from root 12 in rank five and computes the exact surviving canonical mass.
  atlas-supercritical-pauli-branching-cycle: that asks for a recurrent finite branch network with a dimension contradiction; this classifies one finite affine root packet and proves its remaining types have exact orbit countermodels.
  finite-positive-root-fragments-have-marked-regular-models: that gives a general regular-model firewall for positive-root fragments; this computes the precise 15/64 firewall face for the literal three-shear CK packet.
---

**ESTABLISHED EXACT THREE-SHEAR CLASSIFICATION AND MACROSCOPIC NO-GO.**  Use
all three transverse coefficient-one actors available from root `12`:

```text
S_3=x_23(1),       S_4=x_24(1),       S_5=x_25(1),
D_(r,a)=x_1r(a),        r in {3,4,5}.                  (3TS1)
```

For every coefficient `a`, the literal Steinberg rows give

```text
S_r x_12(a) S_r = x_12(a) D_(r,a).                    (3TS2)
```

The three actors commute, all target-root families commute, and every actor
fixes every target root.  Thus they generate an affine `F_2^3` action on the
joint additive-root character fibers.

Let `p=eE`, `q=fF`.  On one joint target-character sector define

```text
u_r=1 iff D_(r,p) has sign -1,
v_r=1 iff D_(r,q) has sign -1,
w=u+v.                                                  (3TS3)
```

The bit `w_r` is the sign of `D_(r,1)` because `p+q=1`.  A shear word with
exponent vector `k in F_2^3` preserves the marked source sign
`x_12(1)=-1` exactly when

```text
k dot w=0,                                              (3TS4)
```

and exchanges the source `p/q` branches exactly when

```text
k dot u=1.                                              (3TS5)
```

Such a word exists if and only if

```text
u notin span_F2{w}.                                     (3TS6)
```

Hence all marked multiplicity is paired and balanced on `49` of the `64`
target-character types `(u,w)`.  The exact degenerate set is

```text
u=0                 (8 types),
or u=w!=0           (7 further types),                 (3TS7)
```

for a total of `15` types.  On those types every shear word preserving the
marked sign also preserves the `p/q` orientation.

The survivor is macroscopic in the canonical profile.  The six commuting
target roots

```text
D_(r,p), D_(r,q),       r=3,4,5
```

generate `C_2^6`; their joint characters are uniform in the canonical group
trace.  Therefore the degenerate projection has trace

```text
15/64.                                                   (3TS8)
```

The two commuting source roots `x_12(p),x_12(q)` are independent of that
target subgroup.  Intersecting with the marked sign `x_12(1)=-1` halves the
mass, so the ambient canonical trace of the marked degenerate face is

```text
15/128.                                                  (3TS9)
```

There is also a label-only calibration.  The three coefficient-one target
roots `D_(r,1)` form `C_2^3` in the fixed left-regular `A8` label chart.
Their common positive-character face (`w=0`) has exact label trace `1/8`.
Inside the full six-root canonical profile, its uniquely degenerate type
`u=0` has trace `1/64`; the other seven `w=0` types are balanced by
`(3TS6)`.

The `15/64` face is a genuine algebraic survivor, not merely failed
bookkeeping.  On every degenerate target type, the finite affine orbit
decomposes into two inequivalent marked orientations which no word in
`<S_3,S_4,S_5>` connects.  Taking one orbit gives an exact
finite-dimensional model with maximal marked `p/q` imbalance on that type.
The full finite subgroup's regular representation balances the two orbits
globally, as canonical trace requires, but arbitrary external multiplicity
data commuting with this packet can still distinguish them until a relation
outside the three-shear group identifies the orientations.

Thus rank five supplies no fourth independent transverse shear, and all
three available directions still leave fixed positive canonical mass.  The
positive Atlas construction can hide coefficient multiplicity on these
fifteen types; a negative proof must use a non-shear row to couple the two
degenerate orientations.

DERIVATION
atlas-three-transverse-shears-counting-proof
