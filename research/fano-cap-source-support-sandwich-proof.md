---
rg: 2
id: fano-cap-source-support-sandwich-proof
kind: route
title: Affinize the cap ranges of the actual positive-support section
target: fano-cap-witness-sections-force-source-affine-safety
requires:
  - rstar-fano-ghost-affine-hull-criterion
  - culf-mastel-rstar-reduction-is-support-blind
---

Let `T` be the solution set of the target pp-gadget, with visible projection
`C`.  For target occurrence `j`, let `S_j` be its range on the chosen witness
section of the actual positive source support `S`.  By hypothesis `S_j` is a
Fano cap after translation.  Put

```text
A_j=Aff(S_j).
```

The Fano criterion gives `A_j subseteq R_*`.  Replace every target occurrence
by the affine equations cutting out `A_j`, and call the resulting affine
solution set `T_aff`.  Every chosen witness remains a solution, while every
solution is still a solution of the original gadget.  Therefore

```text
sigma(S) subseteq T_aff subseteq T.
```

Projection to the visible coordinates gives an affine relation

```text
A=projection_V(T_aff),       S subseteq A subseteq C.
```

Since `Aff(S)` is the least affine relation containing `S`, `(FWS2)` follows.

For a nondeterministic lifted trace, the target context PVM refines each
source atom into finitely many witness atoms.  Faithfulness on its support
ensures that a positive source atom has at least one positive witness atom.
Choosing one such atom for every `phi in S` reduces to the preceding argument.
Equation `(FWS5)` is the direct affine-hull calculation for three one-hot
vectors.

Culf--Mastel Corollary 6.7 supplies exactly the extension relation needed to
form these sections, while Theorem 6.8 invokes it without any restriction on
the source support.  Its constant arity bounds the finite search but adds no
affine identity, completing the audit.

