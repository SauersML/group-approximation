---
rg: 2
id: set-transitive-coset-shifts-have-only-constant-minimal-sets
kind: claim
title: If a group moves every finite subset of Ω into every infinite subset, every nonempty closed invariant subset of A^Ω contains a constant configuration, so no free or infinite minimal subsystem exists
distinct_from:
  cornulier-regime-coset-sfts-are-quantum-rigid: that makes coset shifts with finitely many pair types quantum rigid; this shows the known such actions carry no free and no infinite minimal subsystem at all.
  gjs-countable-groups-have-free-minimal-subflows: that gives free minimal subflows of the ordinary Bernoulli shift 2^Γ; this rules them out for generalized Bernoulli shifts over set-transitive actions.
---

**ESTABLISHED (lane proof, elementary, unreviewed; no priority claimed).**

## Statement

Let a group `Λ` act on an infinite set `Ω` with property **(IS)**: for every finite `F ⊆ Ω` and every
infinite `S ⊆ Ω` there is `g ∈ Λ` with `gF ⊆ S`. Let `A` be finite and `Z ⊆ A^Ω` nonempty, closed and
Λ-invariant. Then:
1. `Z` contains a constant configuration, which is fixed by all of `Λ`;
2. every minimal closed invariant subset of `A^Ω` is a single constant configuration;
3. `Λ` acts freely on no nonempty closed invariant subset of `A^Ω`.

## Proof

Take `z ∈ Z`. Since `A` is finite and `Ω` infinite, some letter `α` has `S = z^(-1)(α)` infinite. For a
finite `F ⊆ Ω`, (IS) gives `h` with `hF ⊆ S`. Put `g = h^(-1)`. Then `(g.z)(ω) = z(g^(-1)ω) = z(hω) = α`
for `ω ∈ F`. Taking `F` along an exhaustion of `Ω`, a limit point of the `g.z` is the constant `α`, and it
lies in `Z` since `Z` is closed. Parts 2 and 3 follow, because a constant is fixed by every element.

## Where (IS) holds

- **Highly transitive actions,** by k-transitivity for `k = |F|`. Examples: `V` on dyadic points,
  `CT_P(Z)` on `N_0`, and the Hull–Osin actions of acylindrically hyperbolic groups.
- **Actions preserving a linear or cyclic order and transitive on increasing tuples.** Here any `|F|`
  points of `S` are order-isomorphic (or cyclically so) to `F`. Examples: `F` and `T` on dyadics.
- **Where it fails.** Actions with a nontrivial invariant pair relation that some infinite set avoids.
  - `V × V` on pairs of dyadics fails (IS): take `S` a line.
  - Its coset shift is still not free-minimal, by the same canonization in each coordinate (recorded
    as a remark, not claimed).
  - The two-sided action of `F_2 × F_2` on `F_2` fails (IS): take `S = <b>` and `F = {1, a}`, since
    no conjugate of `a` is a power of `b`.

## Lesson for general BH

Rigid coding and free coding pull in opposite directions. Homogeneity of the coding set (IS), which
is what makes type (A) actors and their coset shifts rigid for free, puts Λ-fixed points into every
orbit closure. A free minimal quantum-rigid SFT must live on a coset space with an invariant pair
relation that some infinite set avoids, and so with infinitely many pair types. The two-sided free
group escapes (IS), but its natural cyclic descent collapses to finite subshifts
(`two-sided-free-group-coset-sfts-collapse-under-cyclic-descent`), so the stabilizers must also fix a
direction.
