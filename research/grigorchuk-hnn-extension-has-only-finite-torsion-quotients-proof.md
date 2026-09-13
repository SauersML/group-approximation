---
rg: 2
id: grigorchuk-hnn-extension-has-only-finite-torsion-quotients-proof
kind: route
title: Apply the just-infinite base theorem to the first Grigorchuk group and Lysionok's substitution
target: grigorchuk-hnn-extension-has-only-finite-torsion-quotients
requires:
  - just-infinite-base-hnn-has-only-finite-torsion-quotients
  - grigorchuk-group-is-just-infinite-torsion-not-fp
  - grigorchuk-ascending-hnn-extension-is-finitely-presented
---

The first Grigorchuk group `G` is infinite and just-infinite
(`grigorchuk-group-is-just-infinite-torsion-not-fp`). Lysionok's substitution
`phi` is an injective endomorphism that is not surjective
(`grigorchuk-ascending-hnn-extension-is-finitely-presented`). So no power of
`phi` is the identity, and item 1 of
`just-infinite-base-hnn-has-only-finite-torsion-quotients` gives that every
torsion quotient of `H = G*_phi` is finite. Item 2 gives the same conclusion
from finite presentability of `H` and non-finite presentability of `G`.

For the "in particular": let `g in H \ N`, where `N` is the kernel of
`H -> Z`, `G -> 0`, `t -> 1` (the normal closure of `G`). Put `Q = H/<<g>>`, and
let `k != 0` be the image of `g` in `Z`. The image of `N` in `Q` is torsion,
since it is an increasing union of images of conjugates of the torsion group
`G`. It is normal with cyclic quotient of order dividing `|k|`. Every element
of `Q` has a power in that image, so `Q` is torsion. `Q` is finitely presented,
as a quotient of the finitely presented `H` by one normal generator. By the
first paragraph, `Q` is finite.
