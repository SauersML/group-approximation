---
rg: 2
id: ascending-hnn-base-profinite-closure-telescope
kind: claim
title: The profinite closure of the base in an ascending HNN extension is the entire telescope kernel
distinct_from:
  profinite-twins-opposite-mf: That concerns two different groups with the same profinite completion; this computes the closure of one subgroup inside one HNN group.
artifacts:
  - research/artifacts/ascending-hnn-iterated-coset-solution-2026-08-18.md
---

Let `V=<Gamma,t | t gamma t^-1=alpha(gamma)>` be an ascending HNN extension
of a countable group along an injective endomorphism, and let

`N = union_{r>=0} t^-r Gamma t^r = ker(V -> Z)`.

Then the profinite closure of the base copy `Gamma` inside `V` is exactly `N`:

`cl_prof^V(Gamma) = N`.

Consequently the base copy is a separable subgroup of `V` if and only if
`alpha` is surjective.  In particular, for every **proper** injective
self-embedding the base is never separable in the HNN group.

Equivalently, every finite quotient of `V` identifies the images of all
levels `t^-r Gamma t^r`.  Exact finite quotients of the HNN group therefore
cannot witness the strict compression; finite action models must come from a
different mechanism.
