---
rg: 2
id: finite-index-projective-core-yields-central-witness
kind: claim
title: A finite-index finite-phase projective core already gives a nonhyperlinear finite central extension
distinct_from:
  cdi-noncartan-bridge-has-two-exact-gates: that requires the entire named CDI factor to have a projective regular basis; this only requires such a basis on one finite-index subfactor.
  finite-index-extensions-preserve-connes-embeddability: that is the permanence theorem but does not extract a group; this combines it with an explicit finite-phase projective basis to construct the central extension.
  finite-normal-type-corner-is-twisted-group-algebra: that starts from a finite normal subgroup of an already given group; this starts inside an arbitrary non-CE factor and only asks for a finite-index projective core.
---

Let `M` be a non-Connes-embeddable finite factor.  Suppose `N<M` is a
finite-index subfactor with a trace-orthonormal projective unitary basis

```text
{v_g:g in Gamma},
v_g v_h=omega(g,h)v_(gh),
tau(v_g)=0 for g!=e,                                   (FPC1)
```

where `Gamma` is countable and `omega` takes values in one finite phase
group `mu_m`.  Then

```text
N isomorphic_to L_omega(Gamma)                         (FPC2)
```

is non-Connes-embeddable, and the explicit finite central extension

```text
Gamma_tilde=mu_m times_omega Gamma                     (FPC3)
```

is nonhyperlinear.

Thus a finite-cocycle extraction does not require a projective basis for
the whole source factor.  A finite-index projective core is sufficient.
If `Gamma`, its multiplication, and the finite cocycle are recursively
presented, `(FPC3)` is an effective recursive central extension; finite
presentation data remain finite after adjoining the central phase
generator and the twisted relators.

The explicit local algebras in the current MIP-star/BCS constructions do
not satisfy this weaker condition.  Every context algebra and every fixed
Schur--Clifford packet algebra is finite-dimensional.  Its Jones index in
an infinite-dimensional finite factor is infinite.  On the other hand,
using the global native BCS involutions as the projective basis is blocked
by `twisted-group-basis-forces-affine-context-support`: every occupied
context would have to be one affine slice.  No currently cited construction
produces an intermediate diffuse finite-index subfactor with a projective
regular basis, let alone a finite-valued multiplier on it.

This leaves a concrete extraction target strictly weaker than
`effective-nonce-twisted-factor-exists` applied to the entire BCS GNS
factor: find a diffuse finite-index projective core.  Merely packaging more
finite context or packet algebras cannot approach that target, because their
index remains infinite.
