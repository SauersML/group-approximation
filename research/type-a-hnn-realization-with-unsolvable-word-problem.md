---
rg: 2
id: type-a-hnn-realization-with-unsolvable-word-problem
kind: claim
title: Some type (A) actor together with one permutation conjugating a finitely generated orbit-finite subgroup onto another generates a group with unsolvable word problem
distinct_from:
  permutation-hnn-realization-of-type-a-actor-is-a2: that proves the HNN realization is of type [A_2] and has a recursive kernel when the edge groups have finite index; this asks for an instance, necessarily with infinite-index edge groups, whose image has unsolvable word problem.
  stable-permutation-hnn-of-type-a-actor-is-type-a: that concludes type (A) when the realization is injective, and then the image is the finitely presented HNN extension itself; this asks for a non-injective realization whose image has unsolvable word problem.
  some-a2-action-has-a-nonrecursive-kernel: that allows any type [A_2] action; this asks for a witness of one specific shape.
---

**OPEN.** There exist:
- a type (A) action `Γ ↷ X`, as in `type-a-action-gives-boone-higman-for-subgroups`;
- finitely generated subgroups `D_1, D_2 <= Γ`, with `D_1` having finitely many
  orbits on `X`;
- an isomorphism `ψ : D_1 -> D_2`;
- a permutation `π in Sym(X)` with `π d π^-1 = ψ(d)` as permutations for all
  `d in D_1`,

such that the permutation group `<Γ, π> <= Sym(X)` has unsolvable word problem.

**Why it matters.** By `permutation-hnn-realization-of-type-a-actor-is-a2` (a), the
HNN extension `Γ*_ψ` acting through `t -> π` is of type `[A_2]`, with kernel recursive
iff `<Γ, π>` has solvable word problem. So an instance establishes
`some-a2-action-has-a-nonrecursive-kernel` (route
`nonrecursive-a2-kernel-from-unsolvable-hnn-realization`). That refutes
`a2-action-kernels-are-recursive` and establishes
`a2-pair-with-non-removable-kernel-exists`.

**Sufficient test.** By (c) of the same node, it suffices that
`C_Γ(π) = {γ in Γ : γπ = πγ}` be non-recursive. This set is always co-r.e., because
the action is computable. It contains `D` when `D_1 = D_2 = D` and `ψ` is the
identity.

**Necessary features.**
- `D_1` and `D_2` do not both have finite index in `Γ` (same node, (b)).
- `π` does not normalize `Γ` (Attempt 1).
- The certificate argument of `a2-kernel-recursion-ascends-normal-orbit-finite-chains`
  (1) must fail. Every kernel element `k` commutes exactly with `Γ ∩ k^-1Γk`, which
  is computed along the Britton normal form of `k` as an iterated intersection of
  conjugates of `D_1` and `D_2`. So a witness needs such intersections that contain
  no orbit-finite subgroup from any r.e. certified family. Typically they would be
  subgroups with infinitely many orbits on `X`.

## Attempts

**Attempt 1 (2026-09-16): `π` normalizes `Γ`.** Take `D_1 = D_2 = Γ` and `ψ`
conjugation by `π`. Then `Γ*_ψ = Γ x|_ψ Z` is the one-generator normalizer cover of
`normalizer-extension-of-type-a-actor-is-a2-cover`. `<Γ, π>` has solvable word
problem by `a2-kernel-recursion-ascends-normal-orbit-finite-chains` (4). This includes
the swap `π` of the two copies in the product actor `Γ_0 x Γ_0 ↷ X_0 ⊔ X_0`, where the
image is `Γ_0 ≀ Z/2`. Dies.

**Attempt 2 (2026-09-16): finite-index edge groups.** Here every kernel element
centralizes a finite-index subgroup of `Γ`, and finite-index subgroups are certified by
coset tables. The kernel is recursive
(`permutation-hnn-realization-of-type-a-actor-is-a2` (b)). Dies.

**Attempt 3 (2026-09-16): Boolean translation on clopen sets.** Let `Γ = V` act on the
set `Clop(C)` of all clopen subsets of the Cantor set. Checked only at sketch level:
- `V` is finitely presented, the action is faithful, and point stabilizers are
  `≅ V x V` or `V`.
- Orbits of two-element subsets are determined by which Boolean atoms are empty.

Let `D = Stab_V(U_0)` for a proper nonempty clopen `U_0`. It is orbit-finite, since
orbits are determined by the emptiness pattern relative to `U_0`. Let
`π(W) = W Δ U_0`, which commutes with `D`.

Now identify `Clop(C)` with the `F_2`-vector space `C(C, F_2)`. `V` acts linearly and
`π` is a translation, so `<V, π>` lies in the affine group `C(C, F_2) x| V`. There an
element has a computable normal form: a clopen set, as a finite dyadic union, together
with an element of `V`. So the word problem is solvable. Dies.

**Attempt 4 (2026-09-16): Houghton group, sketch only.** Let `Γ = H_3` on its three
rays. Take `D = <t>` for a translation `t` whose three translation lengths are all
nonzero, which gives finitely many `D`-orbits. Let `π` shift each of the finitely many
infinite `D`-orbits independently along itself, which commutes with `D`.

Each element of `<H_3, π>` is eventually a residue-class translation on each ray,
modulo a common modulus, and differs from that eventual form only inside a computable
bounded region. This suggests a solvable word problem, but the argument was not written
out in full. Not a witness; probably dies.

**Attempt 5 (2026-09-16): regular affine actors, sketch only.** Let `Γ = D x| A` act
affinely on `D`, with `D` regular, and let `π` be right multiplication by `n in D`.
Then:
- `C_Γ(π) = D x| Stab_A(n)`;
- `<Γ, π> <= (λ(D) ρ(D)) x| A`, whose word problem reduces to those of `D` and `A`.

Dies whenever those are solvable, which they are, since `Γ` is of type (A) and so has
solvable word problem.

**What to try next.**
1. Choose `D_1 = D_2 = Stab_Γ(x_0)` in a type (A) actor that has finitely many orbits
   on pairs but infinitely many on triples. Then `D ∩ γDγ^-1 = Stab(x_0, γx_0)` can
   have infinitely many orbits, which is exactly where certificates can fail.
   - Here `C_(Sym X)(D)` is controlled by the groups `N_D(H)/H` for the two-point
     stabilizers `H`.
   - One wants these to contain something like `F_2 x F_2`, so that `C_Γ(π)`
     meets a Mikhailova subgroup.
2. The amalgam version: `Γ_1 *_C Γ_2 ↷ X` for two type (A) actors on the same set
   sharing a finitely generated orbit-finite `C`. The tree argument gives type
   `[A_2]` with image `<Γ_1, Γ_2>`, but this was not written up as a node.
