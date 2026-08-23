---
rg: 2
id: regular-dominating-quotients-preserve-amenable-subgroup-algebras
kind: claim
title: Every regular-dominating representation quotient is faithful on amenable subgroup algebras
distinct_from:
  llp-of-regular-dominating-nonamenable-completion-forces-nonhyperlinear: that consumes an intermediate completion positively once LLP and nonamenability are known; this is an unconditional structural restriction on every such intermediate completion, independent of LLP and hyperlinearity.
  finite-subgroup-near-regular-has-large-regular-core: that rounds the restriction of regular HS microstates to asymptotically regular finite-group packets; this is an exact full-C-star statement saying that no quotient which still dominates the regular representation can delete any local finite-group sector.
  triangle-colimit-llp-reduces-to-relator-local-splitting: that reduces full-algebra LLP of a triangle colimit to local ucp splitting of a global relator extension; this proves why passing to a regular-dominating intermediate quotient cannot simplify that problem by altering any of the finite vertex-group algebras.
---

Let `G` be discrete, let `pi` be a unitary representation with
`lambda_G prec pi`, and write

```text
q_pi : C^*(G) -> C^*_pi(G),
J_pi := ker(q_pi).                                             (RDQ1)
```

**THEOREM.**  For every amenable subgroup `H <= G`, the restriction

```text
q_pi | C^*(H) : C^*(H) -> C^*_pi(G)                           (RDQ2)
```

is injective.  In particular this holds for every finite subgroup, so
every nonzero irreducible central projection of every local finite group
survives in every representation completion to which the regular
representation is weakly contained.

**Proof.**  The canonical map `C^*(H) -> C^*(G)` is injective: induce an
arbitrary representation of `H` to `G` and restrict back to see that its
norm is detected in `C^*(G)`.  Weak containment gives

```text
J_pi subset ker(lambda_G : C^*(G) -> C^*_r(G)).                (RDQ3)
```

As an `H`-representation, `lambda_G|_H` is a direct sum of copies of
`lambda_H`, indexed by right `H`-cosets in `G`.  Therefore

```text
ker(lambda_G) cap C^*(H) = ker(C^*(H) -> C^*_r(H)).            (RDQ4)
```

Amenability of `H` makes full and reduced group C-star algebras equal,
so the right side of `(RDQ4)` is zero.  Equations `(RDQ3)--(RDQ4)` give
`J_pi cap C^*(H)=0`, proving `(RDQ2)`.

**Compiler consequence.**  A Paulsen--Rahaman--Samei candidate
`C^*_pi(G)` cannot be made easier by quotienting out unwanted isotypic
sectors in the finite groups that generate a triangle, graph, or packet
presentation: every such sector remains faithfully present.  Any proper
kernel below the regular kernel is necessarily global--it must involve
relations coupling different local subgroup algebras.  Thus the exotic
LLP route can change the global holonomy/relator algebra, but it cannot
evade the common-carrier or relator-splitting problem by deleting local
finite packets.
