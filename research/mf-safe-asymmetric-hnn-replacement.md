---
rg: 2
id: mf-safe-asymmetric-hnn-replacement
kind: claim
title: Replace an effective asymmetric HNN identification by MF-safe finite-presentation moves
root: true
distinct_from:
  symmetric-double-weak-mf: that handles two identical copies and one common subalgebra; this must simulate two different embeddings used by effective Higman compilation.
  hnn-extension-finite-presentation-permanence: that preserves finite presentability, not the MF property.
---

Construct an effective finite-presentation gadget that realizes the asymmetric
subgroup identification required by Higman's rope trick while preserving MF
whenever its input vertex groups are MF.  Shulman's symmetric-double and
central-HNN theorems do not currently supply this gadget.

## Attempts

Replacing the HNN step by a symmetric double works only when the two embeddings
agree up to the available symmetry; the general effective identification does
not have that form.
