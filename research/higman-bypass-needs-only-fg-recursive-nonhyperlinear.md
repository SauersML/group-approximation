---
rg: 2
id: higman-bypass-needs-only-fg-recursive-nonhyperlinear
kind: claim
title: A finitely generated recursively presented nonhyperlinear group already yields a finitely presented one
distinct_from:
  direct-sharp-actor-wreath-forces-actor-fp: that obstructs finite presentation of the direct lamp host; this shows that direct finite presentation is unnecessary once the host is recursively presented.
  bffhz-action-image-is-finitely-presented: that seeks a finitely presented actor envelope; this bypasses that actor-level requirement by applying Higman only after the nonhyperlinear marked host has been constructed.
---

ESTABLISHED.

Let `G` be a finitely generated recursively presented group.  If `G` is not
hyperlinear, then there exists a finitely presented nonhyperlinear group.

Indeed, Higman's embedding theorem embeds `G` in a finitely presented group
`H`.  Hyperlinearity is hereditary to subgroups: restrict a hyperlinear
finite-set approximation of `H` to any prescribed finite subset of `G`.
Consequently

```text
H hyperlinear  ==>  G hyperlinear.
```

The contrapositive proves that `H` is nonhyperlinear.

This observation changes the groupification target for the expanding-character
actor route.  One does **not** need a finitely presented sharply 2-transitive
actor, a finitely generated point stabilizer, or a finitely presented lamp
extension.  It is enough to construct the marked lamp group as one finitely
generated recursively presented group and prove the normalized-HS mark
collapse there.  Higman embedding is applied only after that proof, so it need
not preserve the action, lamp module, property `(T)`, or the marked word's
presentation geometry.  It only preserves the embedded nonidentity marked
element, and subgroup heredity transfers the obstruction.

The recursive-presentation hypothesis cannot simply be omitted.  A finitely
generated subgroup of a finitely presented group is recursively presented, so
it is also a necessary effectivity condition for this particular embedding
bypass.
