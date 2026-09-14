---
rg: 2
id: fournier-facio-nontrivial-quotients-contain-simple-wreath
kind: claim
title: Every nontrivial homomorphic image of the Fournier--Facio group contains the simple wreath shift faithfully
distinct_from:
  fournier-facio-group-finite-dimensional-shadow: That says every finite-dimensional unitary representation kills the simple factor; this says every nontrivial homomorphism whatsoever, into any group, is injective on the whole wreath product S wr Z.
  defect-normally-generates-torsion-free-quotient: That is the small-cancellation fact that the simple factor normally generates G; this uses it to transport the wreath shift faithfully into every nontrivial quotient.
artifacts:
  - research/artifacts/fournier-facio-hyperlinearity-survivor-audit-2026-09-11.md
---

**ESTABLISHED.**  Let `nu:S wr Z -> G` be the embedding of
`fournier-facio-group-contains-simple-wreath-shift`.  For every group `H` and
every homomorphism `phi:G -> H`:

```text
phi is trivial,   or   phi o nu is injective.                (W8)
```

In every nontrivial image, the images of `Gamma` and of the centralizing
tail `(+)_(k<=0) J_k` still form an internal direct product.

**Consequences.**

- Every nontrivial quotient of `G` contains `S wr Z`, hence `S`.  So if `S`
  is not hyperlinear, `G` has **no** nontrivial hyperlinear quotient: every
  homomorphism from `G` into the unitary group of a finite von Neumann
  algebra embeddable in `R^omega` is trivial.
- Conversely, the positive branch `fournier-facio-group-hyperlinear`, and even
  existence of one nontrivial hyperlinear quotient of `G`, requires the
  chosen simple factor `S` to be hyperlinear.
- Every nontrivial normalized-HS tracial model of `G` restricts faithfully to
  `S wr Z`, which feeds `fournier-facio-regular-models-carry-commutant-shift`.

Proof: `fournier-facio-quotient-wreath-heredity-proof`.
