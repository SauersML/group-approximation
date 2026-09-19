---
rg: 2
id: first-root-parahoric-incidence-has-a-two-to-four-morita-lift
kind: claim
title: The first root-parahoric incidence has an exact two-cycle to four-cycle Morita lift
distinct_from:
  one-root-p3-denominator-fragment-has-finite-regular-leaks: That uses residual finiteness of an abstract one-root Baumslag--Solitar fragment; this computes the literal dyadic action on the native forty-two-branch parahoric shell and identifies its exact source and target sorts.
  p3-denominator-steinberg-word-is-multiplicity-blind: That cancels an arbitrary multiplicity normalizer inside a denominator-conjugated Chevalley commutator; this gives a rectangular partial intertwiner already for the first dyadic root-scaling word.
  raw-denominator-incidence-kills-off-diagonal-shell-orbit: That identifies corresponding branches from two section words after their source has been authenticated; this proves that the root-scaling word alone transports the source to a different branch carrier.
---

# The first native mixed denominator-root word

Put

```text
C=SL_3(Z),
h=diag(2,1,1/2),
D=C cap hCh^(-1),
X=C/D,
u=x_12(1).                                             (RPM1)
```

The smallest relation containing both the denominator and a nonmonomial
root element is

```text
h u h^(-1)=u^2=x_12(2).                                (RPM2)
```

It is parahoric at the target because `u^2 in D`.  The induced action of
`u` on the forty-two branch candidates is completely concrete:

```text
p_(gD) |-> p_(ugD).                                    (RPM3)
```

Let `x_0=D` and `x_1=uD`.  Since `u notin D` but `u^2 in D`, these two
points form a two-cycle:

```text
u:x_0 <-> x_1.                                         (RPM4)
```

There is also a native four-cycle.  Put `y_0=s_23D`.  Then

```text
s_23^(-1)u^2s_23=x_13(2) notin D,                      (RPM5)
```

because the `(1,3)` entry of an element of `D` is divisible by four.
On the other hand `u^4=x_12(4)` acts trivially on `X`: the action factors
through the orbit of the lattice
`4Z e_1 directSum 2Z e_2 directSum Z e_3` modulo four.  Hence

```text
y_0, uy_0, u^2y_0, u^3y_0                              (RPM6)
```

are four distinct points forming a four-cycle.

# Exact rectangular lift

Let `U` be the permutation unitary of `u` on `l^2(X)` and define

```text
R=p_(x_0)+p_(x_1),
Q=p_(y_0)+p_(u^2y_0).                                  (RPM7)
```

On `R`, `U` is the two-point flip.  On `Q`, `U^2` is also the two-point
flip.  The rank-two partial isometry

```text
V delta_(x_0)=delta_(y_0),
V delta_(x_1)=delta_(u^2y_0)                           (RPM8)
```

therefore satisfies exactly

```text
V^*V=R,       VV^*=Q,       VUR=U^2V.                 (RPM9)
```

Thus the compressed form of the literal arithmetic word `(RPM2)` has zero
defect and zero missing-source/range mass on a carrier of trace `1/21`, but
its target is a different two-atom carrier.  Arbitrary equal multiplicities
may be tensored into `(RPM8)`, so this is a genuine rectangular Morita lift,
not a scalar coincidence.

If one incorrectly forces the target to equal `R`, there is a fixed gap:
`U|R` is a flip whereas `U^2|R=I_R`, and for every unitary `W` preserving
`R`,

```text
||W(U|R)W^*-I_R||_2^2=2 tau(R)=2/21.                  (RPM10)
```

The native word does not make that identification.  It sends a depth/root
source sort to the next target sort, exactly as `(RPM9)` records.  Iterating
the relation produces the amenable `BS(1,2)` conductor ray; long rectangular
chains can place their unmatched return at the boundary and dilute it.

Consequently the first mixed denominator-root incidence does **not** force
the affine-Weyl Folner cut to be the genuine source and range of one
stationary shell atom.  It only authenticates a typed edge.  A successful
next word must compare two native paths which return to the same raw atom
and therefore identify `Q` with `R` (or charge their mismatch as first-exit
mass).  Pure root scaling, even on the literal forty-two branches, does not
supply that return.

Nor can one append an integral root or Weyl word to obtain the return.
`first-root-parahoric-target-has-a-distinct-double-coset-type` shows that the
source pair has orbital type `D x_12(1)D`, whereas the target pair has type
`D x_13(2)D`; reduction modulo two separates these double cosets.  The
shortest A2 commutator reaches the target in two edges and leaves the
explicit internal holonomy `x_23(2)`.  It is canonically trace-separated,
but charging it still requires a same-corner compression-to-average
identity.  A literal return of the target pair requires another
denominator/cross-chart edge.
