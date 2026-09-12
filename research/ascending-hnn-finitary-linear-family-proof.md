---
rg: 2
id: ascending-hnn-finitary-linear-family-proof
kind: route
title: Build the HNN extension as a direct limit, verify finite orbits and infinite motion, and apply the action theorem
target: ascending-hnn-finitary-linear-family-is-sofic-non-mf
requires:
  - compression-action-theorem-for-finitary-linear-extensions
  - finitary-linear-extension-sofic-and-no-finite-normal-subgroup
artifacts:
  - research/artifacts/compression-finitary-linear-action-theorem-2026-09-08.md
---

Section 3 of the artifact. Build `V` explicitly, so that no normal-form
citation is needed. Let `N` be the direct limit of
`L --alpha--> L --alpha--> ...`, with `[l,j] = [alpha(l), j+1]` and
multiplication in a common stage; injectivity embeds each stage. Then
`[l,j] |-> [alpha(l), j]` is an automorphism with inverse
`[l,j] |-> [l,j+1]`, and `V = N x| <u>` with `u` implementing it has
the displayed presentation, because in any group satisfying those
relations `[l,j] |-> u^-j l u^j` is well defined and inverts the
universal map. So `L_j = u^-j L u^j` increase with union `N`.

`L` is commensurated by `L` and by `u`, hence by `V`, using
transitivity of commensurability. So every `L_j`-orbit on `V/L` is
finite, of size `[L_j : L_j cap gLg^-1]`. Since `B` lies in every
conjugate of `L`, it lies in each `L_j`, and `L_j/B` acts
faithfully with finite orbits, so it is residually finite and sofic.
Every finitely generated subgroup of `N/B` sits in some `L_j/B` and
has finite orbits, and `Q/(N/B)` is `Z`. The second prerequisite then
gives soficity, and, once infinite motion is checked, the absence of
finite normal subgroups; transitivity plus finite generation of `Q`
gives finite generation.

For the first prerequisite, the image of `L` is Kazhdan as a quotient
of `L`; compression stays proper because `B <= uLu^-1`, so the image
of `uLu^-1` has index `[L : alpha(L)] > 1`; the coset `L` is fixed
by that image; and `uL` is not, since `ell uL = uL` would put `ell`
in `uLu^-1`, so any `ell` in `L \ uLu^-1` witnesses it. The action
theorem applies and delivers the non-MF conclusion and both identities.

Infinite motion: `tau(gL) = gu^-1L` is well defined because
`uLu^-1 <= L`, is surjective, and is `Q`-equivariant; the height
homomorphism `V -> Z` descends to heights on `X` that `tau`
decreases. If `q` moves `x` and `tau^m(y) = x`, then `qy = y`
would give `qx = tau^m(qy) = x`, so `q` moves `y`; surjectivity
supplies such `y` at every height above `x`.

The vertex set and parent map are those of the Bass--Serre tree, but no
tree-action theorem is used.
