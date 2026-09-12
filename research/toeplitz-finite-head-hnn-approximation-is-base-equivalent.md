---
rg: 2
id: toeplitz-finite-head-hnn-approximation-is-base-equivalent
kind: claim
title: The finite-head Toeplitz HNN approximation question is exactly the base-group question
distinct_from:
  toeplitz-finite-head-extension-preserves-root: that constructs the quotient and its marked root; this computes the mapping-torus quotient and removes the stable letter from both the hyperlinear and sofic questions.
  ascending-hnn-cannot-create-nonhyperlinearity: that gives the forward hyperlinear permanence statement for an arbitrary injective endomorphism; this records the converse by subgroup heredity and applies it to the finite-head quotient together with its exact locally-finite kernel sequence.
  hs-schur-toeplitz-root-defect-collapse: that asks whether every HS ultraproduct representation of the original group kills the root; this identifies the one concrete base group whose hyperlinearity would refute that assertion.
---

Use the notation of `toeplitz-finite-head-extension-preserves-root` and put

```text
G=EL_5(T),
Q=EL_5(k[z,z^(-1)]),
N=ker(G -> Q),
K=<G,s | sgs^(-1)=beta(g)>.
```

Then there is an exact sequence

```text
1 -> N_infinity -> K -> Q x Z -> 1,                       (FHE1)
```

where `N_infinity` is locally finite.  Moreover

```text
K is hyperlinear  <=>  G is hyperlinear,
K is sofic        <=>  G is sofic.                        (FHE2)
```

The marked root `x_12(eta(P))` belongs to the finite residual of `K` but is
nontrivial.  Thus the group is not residually finite.  This does not decide
whether it is LEF: Thom's finitely generated LEF example shows that a
nontrivial finite-residual root is compatible with LEF.

Finally, no approximation obtained by applying `EL_5` to coefficient maps
from `T` into finite or directly finite rings can retain the marked root.
Every such coefficient map kills `eta(P)`.  Consequently the obvious cyclic
periodization of the unilateral shift, and every restricted-wreath model
factoring through such a coefficient periodization, is root-blind.  A
root-preserving LEF, sofic, or hyperlinear model would have to be genuinely
group-theoretic and use the transverse elementary relations without coming
from a finite-ring model.

The remaining question is therefore the explicit one

```text
is EL_5(T) hyperlinear (or sofic)?                          (FHE3)
```

It is an amenable-kernel problem for this particular Toeplitz action, not an
ascending-HNN problem.  Invoking general closure under an amenable normal
subgroup would be circular: that closure direction is false for soficity in
general and is precisely the kind of special action theorem still absent
here.
