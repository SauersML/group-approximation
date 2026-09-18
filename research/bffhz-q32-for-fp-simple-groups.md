---
rg: 2
id: bffhz-q32-for-fp-simple-groups
kind: claim
title: For every infinite finitely presented simple group G and n at least 2, the image of Aut_G(G * F_n) acting on Hom_G(G * F_n, G) is finitely presented
distinct_from:
  bffhz-action-image-is-finitely-presented: that is the refuted universal upgrade to computably presented cores; this is the published BFFHZ Question 3.2 with its finitely presented core hypothesis, which that refutation does not touch.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4, the existence of a finitely presented simple MIF overgroup; this is the stronger finite-presentation statement for one explicit actor, which implies it by `q34-from-bffhz-q32-for-fp-simple-groups`.
  a2-kernel-removal-forces-recursive-kernel: that shows a non-recursive set of one-variable mixed identities makes this image not recursively presented; this is the positive statement those obstructions constrain.
  bffhz-q32-forces-finitely-based-mixed-identities: that is an established necessary condition for this statement at one group; this is the open statement itself, for all groups.
---

**OPEN.** Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2, Question 3.2,
verbatim as recorded in `bffhz-action-image-is-finitely-presented` (read from
source 2026-08-17):

> "For G a finitely presented simple group and n≥2, is the quotient of
> Aut_G(G*F_n) by the kernel of its action on Hom_G(G*F_n,G) finitely
> presented?"

That node also records that BFFHZ find it "unclear what to expect, even for
example for Thompson's group T".

## Statement

Let `G` be an infinite finitely presented simple group and `n >= 2`. Put
`A = Aut_G(G * F_n)`, `X = Hom_G(G * F_n, G) ≅ G^n` with `A` acting by
precomposition, and `K = ker(A ↷ X)`. Then `A/K` is finitely presented.

Finite simple groups are excluded only to keep the actor centerless. They embed in
Thompson's `V`, so they are irrelevant to Question 3.4.

**Equivalent form.** `A` is finitely presented because `G` is centerless (BFFHZ
Proposition 1.1, as used in `a2-kernel-removal-recursive-kernel-proof` (c)). A
quotient of a finitely presented group is finitely presented exactly when its
kernel is the normal closure of finitely many elements. So the statement says:
`K` is normally finitely generated in `A`.

## What it gives and what it needs

- **Gives Question 3.4.** Route `q34-from-bffhz-q32-for-fp-simple-groups`: the
  image `A/K` is a type (A) actor containing `G`.
- **Needs recursive mixed identities.** If `J_1(G)` is not recursive, the
  statement fails for `G` (`a2-kernel-removal-forces-recursive-kernel` (c)).
- **Needs finitely based mixed identities.** If `J_(n-1)(G)` is not finitely
  based over overgroups, the statement fails for `(G, n)`
  (`bffhz-q32-forces-finitely-based-mixed-identities`). For `J_1(G)` it fails
  for every `n`. A witness is the open claim
  `fp-simple-group-with-non-finitely-based-mixed-identities`.
- **MIF groups.** If `G` is MIF then `K = 1` (BFFHZ, as recorded in
  `relative-automorphism-action-is-highly-transitive`), so the statement holds
  for `G` trivially. Every open case is a non-MIF group such as Thompson's `T`.

## Attempts

1. **Necessary conditions only (2026-09-17, lane `c-mif`).** The two obstructions
   above are the whole known theory of this statement for non-MIF groups. Neither is
   shown to be sufficient. The free-group analogue in
   `bffhz-q32-forces-finitely-based-mixed-identities` ("Not claimed") explains why the
   finite basis condition alone need not give normal finite generation of `K`.
