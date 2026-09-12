---
rg: 2
id: regular-dominating-nuclear-completion-proof
kind: route
title: Pass nuclearity to the reduced quotient and apply Lance amenability
target: regular-dominating-nuclear-completions-cannot-trigger-prs
requires: []
---

Let `A=C^*_pi(G)`.  The weak containment `lambda_G prec pi` is exactly the
kernel inclusion which induces a surjective star homomorphism

```text
A -> C^*_r(G),             pi(g) |-> lambda_G(g).
```

If `A` is nuclear, then its quotient `C^*_r(G)` is nuclear.  Lance's
characterization of amenability for discrete groups therefore makes `G`
amenable.

Every unitary representation of an amenable discrete group is amenable in
Bekka's sense: an invariant mean on `ell^infinity(G)` induces an
`Ad pi(G)`-invariant state on `B(H_pi)` (equivalently, this is the standard
amenability theorem for representations of amenable groups).  In particular
`pi` is amenable.

Thus a regular-dominating nuclear representation completion satisfies
neither the required group nonamenability nor the required representation
nonamenability in the Paulsen--Rahaman--Samei obstruction.  Nuclearity does
supply LLP, but it simultaneously destroys the other hypothesis, proving
the target.
