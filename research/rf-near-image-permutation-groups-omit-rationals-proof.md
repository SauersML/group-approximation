---
rg: 2
id: rf-near-image-permutation-groups-omit-rationals-proof
kind: route
title: Direct proof, since the rationals meet the finitary symmetric group trivially and have no finite quotients
target: rf-near-image-permutation-groups-omit-rationals
requires: []
---

Direct proof. Not independently reviewed.

Let `D <= Γ` with `D ≅ (Q,+)`. The group `D ∩ FSym(X)` is a subgroup of the
locally finite group `FSym(X)`, so it is a torsion group, and it lies in the
torsion-free group `D`. So `D ∩ FSym(X) = 1`, and `D` embeds in
`Γ* = Γ/(Γ ∩ FSym(X))`. That contradicts the hypothesis on `Γ*`.

If `Γ*` is residually finite, it has no subgroup isomorphic to `(Q,+)`: a
nontrivial divisible group has no nontrivial finite quotient (a finite
quotient of order `m` is killed by `m`, and `D = mD`), so every finite
quotient of `Γ*` kills it.

Each group listed in the statement contains the unipotent or translation
subgroup `{x -> x + b}` or `[[1, b], [0, 1]]`, `b ∈ Q`, which is `≅ (Q,+)`;
for `PGL_n(Q)` its image is still `≅ (Q,+)`, since it meets the scalars
trivially.

For the examples: the Houghton map `g -> (t_i)` is a homomorphism because
translation amounts add under composition on each ray outside a finite set.
Its kernel consists of the permutations that are eventually the identity on
every ray, i.e. the finitary ones. The eventual-agreement map `g -> l(g)` is
well defined because two elements of `L` that agree outside a finite set
differ by a finitary element of `L`, which is trivial. It is a homomorphism
because `l(g)l(h)` and `gh` agree outside `F_h ∪ h^-1 F_g`, where `F_g`,
`F_h` are the finite sets on which `g`, `h` differ from `l(g)`, `l(h)`.
