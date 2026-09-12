---
rg: 2
id: rigid-compression-defect-normalization-dichotomy
kind: claim
title: In every approximation class, killing rigid compression defects is equivalent to normalizing Kazhdan centralizers
distinct_from:
  kt-centralizer-normalization-hs: that is the normalization question in the Hilbert--Schmidt class only; this is the general equivalence, in every metric approximation class, between normalization and the group-level criterion that approximable groups have trivial rigid defect, together with the failure-produces-a-witness construction.
  invariant-size-collapse: that says a conjugation-invariant monotone size forbids strict compression; this assumes no size and relates two approximation-theoretic statements about all representations of all infranormal Kazhdan pairs.
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

**ESTABLISHED.** Let `C` be a metric approximation class: sofic,
hyperlinear, `k`-linear sofic, weakly sofic or weak MF, or any class in which
a countable group is approximable exactly when it embeds, as a group, into a
`C`-ultraproduct. A *rigid pair* in `H` is `Gamma <= G <= H` with `Gamma` and
`G` Kazhdan and `Gamma` infranormal in `G`. Its *rigid defect* is

```text
D_H(G,Gamma) = << [g z g^-1, gamma] : g in G, z in C_H(Gamma), gamma in Gamma >>_H .
```

Put

```text
DD(C):   every C-approximable countable H with a rigid pair has D_H(G,Gamma) = 1;
NORM(C): for every infranormal Kazhdan pair Gamma <= G and every homomorphism
         sigma : G -> U into a C-ultraproduct, sigma(G) normalizes C_U(sigma(Gamma)).
```

Then `DD(C) <=> NORM(C)`.

- `NORM` only has to be checked on trace-preserving (injective) restrictions;
  it then holds for every homomorphism.
- A failure of `NORM` at `(sigma, z)` yields the countable `C`-approximable
  group `<sigma(G), z> <= U`. It contains the rigid pair
  `sigma(Gamma) <= sigma(G)` and has a nontrivial rigid defect.

## Consequences

- **Monotonicity:** `C <= C'` gives `DD(C') => DD(C)`.
- **Separation forcing:**
  - If `DD(C)` holds, no group with a nontrivial rigid defect is
    `C`-approximable.
  - If `DD(C)` fails while `DD(C_0)` holds, a group with a nontrivial rigid
    defect separates `C` from `C_0`.

`DD(sofic)` holds (`sofic-groups-kill-rigid-compression-defects`); it fails
for weakly sofic and for weak MF groups. The hyperlinear row is the win--win
`hyperlinear-groups-kill-rigid-compression-defects`. The full classification
table and the conservation criterion explaining each row are in the artifact.

Derivation: `rigid-compression-defect-normalization-dichotomy-proof`.
