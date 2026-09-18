---
rg: 2
id: finitely-coded-unit-groups-act-residually-finitely
kind: claim
title: In a finitely coded Cantor groupoid of any rank, each unit group acts on its object boundary through a residually finite group, so the unit slot of the coded-host machine carries only residually finite inputs
distinct_from:
  self-similar-hosts-contain-only-residually-finite-groups: that is the case of one object and a free monoid, i.e. a self-similar group on a regular tree; this is every finitely coded groupoid (finitely many objects, degree map to N^k with UFP*, locally finite modulo units), of every rank.
  finitely-coded-cantor-actions-give-type-a-hosts: that allows arbitrary unit groups in the positive machine and notes that universal reach needs complex unit groups; this shows those unit groups always act residually finitely, so complexity entering through units is carried by residually finite groups.
  finite-k-graph-full-groups-have-exponential-word-problem: that bounds the word problem when the unit groups are finite; this constrains which infinite unit groups can occur at all.
---

**ESTABLISHED.** Lane proof, elementary, not independently reviewed; no priority claimed.

## Setting

`ℭ` is a finitely coded category in the sense of `finitely-coded-cantor-actions-give-type-a-hosts`:
- a left cancellative small category with finitely many objects;
- a degree map `d : ℭ -> N^k` satisfying UFP*, whose invertibles are exactly the degree-zero morphisms;
- for each object `v` and degree `p`, only finitely many morphisms of degree `p` with target `v` up to right multiplication by units;
- morphisms of every degree.

Assume the boundary `∂Ω(v)` of each object is *path-like*, as for k-graphs and their Zappa–Szép products in `finite-k-graph-boundary-groupoid-standard-facts`:
- for each degree `p`, each boundary point `ζ` lies in exactly one cylinder `Z(x)` with `d(x) = p` and `t(x) = v`;
- `ζ` is the intersection of these cylinders over all `p`.

Let `U_v = ℭ*(v, v)` act on `∂Ω(v)` by left multiplication, and let `Ū_v` be its image in `Homeo(∂Ω(v))`.

## Statement

`Ū_v` is residually finite, for every object `v`. So every group placed in a finitely coded host through the unit slot is residually finite. This includes:
- the self-similar group `H` in a Röver–Nekrashevych group `V_d(H)`;
- the finite germ classes in Zappa–Szép lattice codings.

Hence a finitely presented simple group, and more generally any group that is not residually finite, can only sit in such a host as elements that are not units.

## Proof

Fix `v` and a degree `p`, and let `𝒵_p` be the set of cylinders `Z(x)` with `t(x) = v` and `d(x) = p`.
- **Finiteness.** `𝒵_p` is finite: `Z(x) = Z(xu)` for units `u`, and there are finitely many `x` of degree `p` modulo right units.
- **Units permute `𝒵_p`.** A unit `u` maps `Z(x)` onto `Z(ux)`. Here `d(ux) = d(u) + d(x) = p` because units have degree zero, and `t(ux) = v`. This depends only on how `u` acts on `∂Ω(v)`, so it defines a homomorphism `Ū_v -> Sym(𝒵_p)`.
- **The kernels.** Let `K_p` be the kernel of this homomorphism. It is a normal subgroup of finite index.
- **Trivial intersection.** An element of every `K_p` maps each cylinder `Z(x)` to itself. By path-likeness it then fixes every boundary point, since a point is the intersection of its cylinders of all degrees. So it is the identity of `Ū_v`.

A group whose finite-index normal subgroups have trivial intersection is residually finite. ∎

**Lesson for general BH.**
- **Where complexity can come from.** The coded-host machine gets universal reach, and hence unbounded word-problem complexity, only through its unit groups. Those are always residually finite.
- **Where the input must sit.** The inputs that carry the general conjecture are infinite simple groups (`boone-higman-iff-infinite-simple-inputs`). They must therefore live in a coded host as non-unit elements. Their complexity must be supplied by residually finite unit groups, such as hard residually finite self-similar groups, whose actions are then spread over non-unit bisections.
