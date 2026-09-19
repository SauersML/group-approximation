---
rg: 2
id: universal-localizations-of-quasi-free-algebras-are-quasi-free
kind: claim
title: Every universal localization of an algebra of Hochschild dimension at most one again has Hochschild dimension at most one
distinct_from:
  quasi-free-algebras-have-no-trdeg-two-subfields: that bounds subfields inside one quasi-free algebra; this says the class of quasi-free algebras is closed under universal localization, so the bound applies after inverting elements.
  leavitt-algebra-hochschild-dimension-at-most-one: that is the instance A = L_k(1,2) (a localization of the free algebra); this is the general base-change statement.
---

**ESTABLISHED** by `quasi-free-universal-localization-base-change` (unreviewed).

Let `k` be a field, `A` a `k`-algebra with `pd_(A^e) A <= 1`, and `σ` any set of maps between finitely generated
projective left `A`-modules. Let `B = σ^(-1) A` be the Cohn (universal) localization. Then `pd_(B^e) B <= 1`.

Special case used downstream: `σ` a set of elements of `A`, i.e. right multiplications `A -> A`, so `B` is the
universal ring in which those elements become invertible. `B` may be the zero ring; the statement is then empty.
