---
rg: 2
id: abelianized-cover-kernel-is-self-centralizing
kind: claim
title: The abelian kernel of the free abelianized cover is its own centralizer
distinct_from:
  free-abelianized-cover-has-nontrivial-fd-radical: that uses the crossed-word detector only for elements of the finite residual, because that is where its exact finite-dimensional conclusion needs it; this uses the same computation for every nonidentity element and draws a purely group-theoretic conclusion with no representation in it.
  conjugation-image-of-a-torsion-free-mf-group-is-arbitrary: that is a torsion-free MF group whose normal free abelian subgroup has a strictly larger centralizer, which is why it refutes only a permanence principle; this is the property that construction lacks and the reason it does not reach the transfer.
  free-abelianized-cover-is-torsion-free: that is torsion-freeness of the cover; this is the faithfulness of the conjugation action of the base on the kernel.
artifacts:
  - research/artifacts/conjugation-image-obstruction-and-self-centralizing-kernel-2026-09-08.md
---

**ESTABLISHED.**  Let `G` be countable, adjoin a dummy generator `z` with
`q(z) = 1`, and form

```text
F = F(X u {z}),   R = ker q,   E = F/[R,R],   A_E = R/[R,R].
```

Then

```text
C_E(A_E) = A_E.                                                     (SC1)
```

Equivalently, `G = E/A_E` acts **faithfully** on the abelian kernel by
conjugation, so `A_E` is a faithful `ZG`-module and

```text
E / C_E(A_E) = G.                                                   (SC2)
```

This is the structural feature that separates the relation cover from the
construction of
`conjugation-image-of-a-torsion-free-mf-group-is-arbitrary`, whose centralizer
contains a free group.  It is why that construction refutes a permanence
principle without touching `free-abelianized-cover-reflects-mf`: in the cover,
recovering `G` from the conjugation action costs nothing, because the action is
already faithful.

The dummy generator is what makes `(SC1)` hold for an arbitrary presentation:
without it the detector must be built from the given relators and can be
empty.

DERIVATION
abelianized-cover-self-centralizing-proof
