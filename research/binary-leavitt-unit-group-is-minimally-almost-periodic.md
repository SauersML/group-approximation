---
rg: 2
id: binary-leavitt-unit-group-is-minimally-almost-periodic
kind: claim
title: The binary Leavitt unit group is minimally almost periodic
distinct_from:
  binary-leavitt-unit-group-has-tt-mod-t: that is Hilbert-space quasi-cocycle rigidity; this says every finite-dimensional unitary representation is trivial.
  openai-leavitt-unit-nonsofic: that excludes permutation approximations; this excludes exact compact matrix representations and uses only the embedded Thompson subgroup plus characteristic-two normal generation.
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies the unit group with elementary groups and proves perfectness; this adds the finite-dimensional representation consequence.
---

Let

```text
L=L_(F_2)(1,2),             Q=L^x.
```

Then every homomorphism

```text
rho:Q -> U(d)
```

is trivial.  Equivalently, `Q` is minimally almost periodic.

Choose a complete binary prefix code with at least three leaves and identify
`Q` with the corresponding elementary group using Leavitt self-similarity and
`GL=EL`.  The standard swap of two leaves is a Thompson cylinder transposition,
so it lies in the embedded copy of `V`.  Every finite-dimensional unitary
representation kills that copy of `V`; in particular it kills the swap.
But in characteristic two that single swap normally generates the whole
rank-at-least-three elementary group.  Hence the representation kills all of
`Q`.

This is stronger than absence of finite quotients and is independent of the
nonsoficity proof.  It will be useful precisely at the hyperlinear fork: any
normal invariant density operator for a Leavitt near representation decomposes
into finite-dimensional invariant eigenspaces, and this theorem forces all of
those eigenspaces to be trivial representations.
