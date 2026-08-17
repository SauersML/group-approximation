---
rg: 2
id: nonsofic-hyperbolic-via-kun-thom-centralizer
kind: route
title: Contrapose the Kun--Thom centralizer theorem against a hyperbolic Kazhdan pair
target: nonsofic-hyperbolic-group
requires: []
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Kun--Thom Theorem B (August 2026) says that for a **sofic** group `G` with
property (T) and an infranormal `Γ ≤ G` with property (T), the centralizer
`C_G(Γ)` is normal in `G`.  Contraposed, it is an obstruction: a Kazhdan pair
whose centralizer is not normal certifies non-soficity of the ambient group.

The attack: find a hyperbolic group `G` with property (T) — there are many,
cocompact lattices in `Sp(n,1)` and random groups in the density model at
density in `(1/3, 1/2)` among them — carrying an infranormal Kazhdan subgroup
`Γ` with `C_G(Γ)` non-normal.
That would be a non-sofic hyperbolic group, and hence also a
non-residually-finite one.  The appeal of the route is that it needs no
construction at all, only an example of a configuration, and that this
repository already carries the theorem in verified form.

Dead: by `kun-thom-centralizer-normality-automatic-in-hyperbolic`, in a
hyperbolic group `C_G(Γ)` is normal for **every** infranormal Kazhdan
subgroup, sofic or not.  The obstruction's hypothesis is unsatisfiable in the
hyperbolic category, so the contraposition can never fire there.  The
underlying reason is a mismatch of scale: Theorem B detects an *infinite*
centralizer being moved around, and hyperbolic groups have no infinite
centralizers of non-elementary subgroups to move.

**What survives the demolition.**  Theorem B keeps its force everywhere this
program actually uses it, on wreath-type ambient groups where the centralizer
is the whole lamp group.  What dies is the hope that a 2026 obstruction
imported unchanged reaches a category nobody could reach before.
