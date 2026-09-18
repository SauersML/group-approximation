---
rg: 2
id: simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group
kind: claim
title: An infinite simple Kazhdan subgroup of a finite germ extension of V embeds in a single singular isotropy germ group, which is finitely presented whenever Belk--Hyde--Matucci Theorem 2.1 certifies finite presentation
distinct_from:
  almost-v-fw-subgroups-act-through-finitely-many-germs: that proves the germ reduction for every FW subgroup, up to finite index and with a kernel inside a conjugate of V; this specializes it to simple inputs, where the finite-index step and the kernel disappear and the whole input lands injectively in one germ group at a singular point.
  bhm-singfix-condition-forces-fp-germ-groups: that shows the one-point SingFix hypothesis of Theorem 2.1 forces singular germ groups to be finitely presented; this combines it with the germ reduction to locate where a simple Kazhdan input must sit.
  boone-higman-iff-simple-kazhdan-decidable-inputs: that reduces Boone--Higman to simple Kazhdan decidable inputs; this records what that reduction demands of the finite-germ-extension engine.
---

**ESTABLISHED** by `simple-kazhdan-germ-extension-germ-group-proof` (lane proof,
elementary from landed nodes, not independently reviewed; no novelty claimed).

Let `V` act on the Cantor set `C = {0,1}^N`, let `E` be a finite germ extension of `V`
in the sense of Belk--Hyde--Matucci (arXiv:2407.03149), and let `S <= E` be an infinite
simple group with property (T).

1. **One point, one germ group.** There is a point `y ∈ sing(E)` fixed by `S` such that
   the germ map `S -> (E)_y` is injective. So `S` embeds in the single isotropy germ
   group `(E)_y` at a singular point.
2. **Finite presentation.** If `E` is certified finitely presented by Theorem 2.1 of
   Belk--Hyde--Matucci (hypothesis (2) at `n = 2`), then `(E)_y` is finitely presented.
   It contains the infinite Kazhdan group `S`, so it is neither amenable nor a-T-menable.

**Consequence for the germ engine.** By `boone-higman-iff-simple-kazhdan-decidable-inputs`,
a proof of `boone-higman-conjecture` through finite germ extensions of `V` certified by
Theorem 2.1 must, for every infinite finitely generated simple Kazhdan group `S` with
solvable word problem, produce such an extension with `S` inside one finitely presented
singular germ group `(E)_y`. The engine cannot spread `S` over the `V`-local part or over
several singular points: all of `S` is carried by one finitely presented germ group. This
is a structural requirement, not a refutation. Finitely presented overgroups of `S` exist
(Higman), and the open question is whether they arise as singular germ groups of
certified extensions.

## Scope

- Only property (T) of `S` is used, through `V` having the Haagerup property. Property
  FW would suffice if `V`'s proper action on a CAT(0) cube complex (Farley) were used
  instead; that variant is not claimed here.
- Nothing is said about extensions of `V` whose finite presentation is proved by other
  means than Theorem 2.1.
