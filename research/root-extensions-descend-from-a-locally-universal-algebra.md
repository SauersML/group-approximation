---
rg: 2
id: root-extensions-descend-from-a-locally-universal-algebra
kind: claim
title: The tracial root theorem for one locally universal tracial algebra gives it for every separable tracial algebra
distinct_from:
  locally-universal-group-factor-group-is-nonhyperlinear: that turns local universality of a group factor into non-hyperlinearity of the group; this turns a root theorem for any locally universal tracial algebra into the root theorem for all separable tracial algebras.
  some-countable-group-factor-is-locally-universal: that is the existence question for a locally universal group factor; this needs no group structure and applies to any locally universal tracial algebra.
---

**Statement.**  Let `(S, sigma)` be a tracial von Neumann algebra that is
locally universal: every separable tracial von Neumann algebra embeds,
unitally and trace-preservingly, into an ultrapower `S^omega` for some
ultrafilter `omega`.  This is the notion of Arulseelan--Manzoor as pinned on
`locally-universal-group-factor-group-is-nonhyperlinear`.

Suppose the conclusion of
`tracial-algebras-solve-nonsingular-equations-in-extensions` holds for `S`:
for all unitaries of `S` and all nonsingular words there are a trace-preserving
extension of `S` and a root.  Then the same conclusion holds for every
separable tracial von Neumann algebra `M`.

**Consequence.**  The tracial root theorem, and through
`kl-via-tracial-root-extensions` the Kervaire--Laudenbach conjecture, reduces
to a root theorem over one algebra.  Separable locally universal tracial
algebras exist (Arulseelan--Manzoor, crediting Farah--Hart--Sherman Example
6.4, as recorded on `locally-universal-group-factor-group-is-nonhyperlinear`).
That existence statement is not imported as a node here, so the reduction is
stated conditionally on `S`.

**Proof.**  Route `root-extensions-descend-from-locally-universal-proof`.
Elementary; no novelty claimed.
