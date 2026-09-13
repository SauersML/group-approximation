---
rg: 2
id: grigorchuk-ascending-hnn-extension-is-finitely-presented
kind: claim
title: Lysionok's substitution gives a finitely presented ascending HNN extension of the first Grigorchuk group
distinct_from:
  grigorchuk-group-is-just-infinite-torsion-not-fp: that records properties of the first Grigorchuk group itself; this records the finitely presented ascending HNN extension built from it.
---

**ESTABLISHED** (literature import, `grigorchuk-ascending-hnn-extension-is-finitely-presented-citation`).

Let `G = < a, c, d >` be the first Grigorchuk group (`b = cd`). The substitution
`phi(a) = aca`, `phi(c) = cd`, `phi(d) = c` induces an injective endomorphism of
`G`, and the ascending HNN extension

```text
H = < a, c, d, t | a^2, [d, d^a], [d^{ac}, d^{aca}], a^t = aca, c^t = cd, d^t = c >
```

is finitely presented (Grigorchuk 1998, the first finitely presented amenable
group that is not elementary amenable). Moreover `phi(G) <= St_G(1)`, so `phi`
is not surjective.
