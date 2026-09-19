---
rg: 2
id: centralized-quotient-shadow-density-dichotomy
kind: claim
title: A relation-centralized finite quotient has zero canonical adjoint density unless its base is finite
distinct_from:
  finite-inclusion-is-free-self-compressor-quotient: That supplies a free self-compressor with a finite parent/child quotient shadow; this proves that centralizing the quotient kernel does not localize that shadow on a macroscopic adjoint carrier.
  non-ce-trace-does-not-promote-to-subgroup-character-gap: That shows projective-kernel equations do not retain finite-dimensional soundness; this computes the exact normalized-adjoint density lost when the projective kernel has infinitely many central characters.
  marked-self-copy-forces-macroscopic-adjoint-excess: That consumes a positive-density child-only sector; this proves the most direct central-relation construction supplies either density zero or no proper self-copy.
---

**ESTABLISHED FIREWALL.**  Let `F` be finitely generated, let
`N normal F` have finite quotient `B=F/N`, and centralize the relation
kernel:

```text
E=F/[F,N],                 A=N/[F,N]<=Z(E).             (RCQ1)
```

For a finite-dimensional unitary representation `pi:E->U(H)`, decompose
with respect to the central characters of the image of `A`:

```text
H=directSum_(chi) H_chi,          d_chi=dim H_chi.      (RCQ2)
```

The largest operator subspace on which the adjoint action kills `A` is

```text
D_pi=directSum_(chi) End(H_chi).                        (RCQ3)
```

On `D_pi`, `Ad pi|F` factors exactly through `B`, because every element of
`N` acts by a scalar on each diagonal character block.  Its normalized
adjoint density is

```text
dim(D_pi)/(dim H)^2=sum_chi (d_chi/dim H)^2.            (RCQ4)
```

Thus the density is precisely the collision probability of the central
character distribution; off-diagonal blocks retain the phase ratio and do
not factor through `B`.

Now take canonical normalized-HS microstates of any group in which the image
`Abar` of `A` remains central in the relevant base image.  If `Abar` is
infinite, the restricted character measures converge to Haar measure on
`dual(Abar)`, which is nonatomic.  Therefore

```text
max_chi d_(chi,n)/d_n ->0,
sum_chi (d_(chi,n)/d_n)^2 ->0.                          (RCQ5)
```

So the exact projective quotient shadow occupies `o(d_n^2)` adjoint
directions and cannot feed macroscopic tracial self-copy collapse.

If `Abar` is finite, then the base image is an extension of the finite group
`B` by the finite group `Abar`, hence is finite.  A conjugate subgroup of a
finite group with the same cardinality is the whole group; it cannot be a
proper self-copy.  Consequently relation centralization has the dichotomy

```text
infinite central kernel  => zero canonical adjoint density,
finite central kernel    => finite base and no proper self-copy.            (RCQ6)
```

Small spectral boxes around one central character do not evade the result.
Shrinking the box makes the quotient error tend to zero but its Haar mass,
and hence its normalized adjoint carrier density, tend to zero as well.
Keeping a fixed positive box leaves a fixed projective-relation error and
does not produce an exact child-fixed projection without an additional
spectral-gap input.

Nor can property `(T)` supply that missing input within this construction.
If `F` is Kazhdan, `kazhdan-relation-centralized-quotient-is-finite` shows
that `E` is automatically finite: the central kernel `A` has finite index in
the Kazhdan quotient `E`, hence is itself Kazhdan, and an abelian Kazhdan
group is finite.  The spectral-gap repair therefore destroys the proper
self-copy algebraically rather than rescuing a positive-density shadow.
