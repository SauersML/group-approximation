---
rg: 2
id: agent-projective-kernel-arbitrary-phase-face-compiler
kind: claim
title: Any CE-empty projective-kernel face gives a finitely presented nonhyperlinear central extension without finite phase
artifacts:
  - research/agent-projective-kernel-arbitrary-phase-face-compiler-proof.md
distinct_from:
  ce-projective-kernel-face-gap-gives-nonhyperlinear-quotient: that uses a finite phase group and a positive central Fourier corner; this permits an arbitrary circle-valued projective character and uses Thom's all-central-characters criterion.
  projective-kernel-face-gap-compactifies-phase-safely: that compactifies separation from finite-dimensional states and preserves a pre-existing finite phase; this compactifies CE-tracial separation and builds a finitely generated central phase group from the finitely many selected values.
---

Let `G` be finitely presented, let `K normal G`, and let

```text
chi:K -> T                                               (APA1)
```

be conjugation invariant.  No finite-image hypothesis is imposed.  If

```text
F_(K,chi)^tr intersect T_CE(G)=empty,                  (APA2)
```

then there is a finitely presented nonhyperlinear group `H` containing a
finitely generated central subgroup `C` and a character `beta in hat C`.

More explicitly, compactness gives `k_1,...,k_m in K` whose finite scalar
face is already CE-empty.  Put

```text
C=<chi(k_1),...,chi(k_m)> <= T                         (APA3)
```

as an abstract finitely generated abelian group and define

```text
H=(C x G)/normalClosure_CxG
     {(chi(k_j)^(-1),k_j):1<=j<=m}.                   (APA4)
```

Then `C` embeds centrally in `H`, `H` is finitely presented, and `H` is
nonhyperlinear.  Thus finite phase is convenient for a literal positive
Fourier corner but is not necessary for the CE-character-face endpoint.

