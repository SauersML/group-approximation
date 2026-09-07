---
rg: 2
id: full-mf-collapse-from-word-certificates
kind: route
title: Apply individual word certificates to the generator words
target: full-mf-radical-linear-relator-inequality
requires:
  - mf-radical-words-have-linear-certificates
artifacts:
  - research/artifacts/mf-word-linear-certificates.md
---

## Proof

If every MF homomorphism kills the group, it kills each of the finitely
many generator words. Apply the prerequisite to each generator, take the
union of the finite relation windows and the maximum of their positive
constants. The maximum generator displacement satisfies the resulting
linear inequality. Conversely the inequality kills every generator in
every corona homomorphism, hence every MF homomorphism. For an empty
generating set the group is trivial and the assertion holds with constant
one and empty relation window.

This supplies an alternative complete written proof of the existing
claim. Its conclusion agrees with the existing Lean statement, but the
new tensor proof is not claimed to have been compiled in Lean.
