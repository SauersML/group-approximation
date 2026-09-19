---
rg: 2
id: deligne-maslov-opnorm-sector-is-mf-quotient
kind: claim
title: A Deligne Maslov point-norm sector exists exactly when a twisted fibre has an MF quotient
artifacts:
  - research/deligne-maslov-mf-quotient-equivalence-proof.md
distinct_from:
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that asserts the two sectors are empty; this identifies sector existence exactly with a nonzero MF quotient and does not decide that remaining MF-black-hole question.
  deligne-twisted-fibres-have-no-amenable-trace: that excludes amenable traces on the whole twisted algebra; a nonzero MF quotient can carry a Connes-embeddable but nonamenable trace, so that theorem does not decide this equivalence's alternatives.
---

**ESTABLISHED EXACT REFORMULATION.**  Let `alpha` be either nontrivial
mod-three Maslov multiplier of `Gamma=Sp_4(Z)` and put

```text
A_alpha=C^*(Gamma;alpha).
```

The following are equivalent:

1. there is a finite-dimensional pointwise `alpha`-projective
   asymptotic representation in operator norm;
2. there is a unital star homomorphism

   ```text
   A_alpha -> product_n M_(d_n) / directSum_n M_(d_n);
   ```

3. `A_alpha` has a nonzero MF quotient.

After cutting the remaining central involution, these conditions hold
exactly when at least one of the two full-central-character fibres of
`A_alpha` has a nonzero MF quotient.  Therefore
`deligne-nontrivial-maslov-opnorm-sectors-are-empty` says precisely that
both full-central-character fibres are MF black holes.  It is stronger than
non-MF-ness of either reduced twisted algebra.

DERIVATION
deligne-maslov-mf-quotient-equivalence-proof
