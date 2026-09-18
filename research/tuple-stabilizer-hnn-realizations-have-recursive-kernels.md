---
rg: 2
id: tuple-stabilizer-hnn-realizations-have-recursive-kernels
kind: claim
title: A permutation HNN realization over pointwise tuple stabilizers has a recursive kernel whenever the actor has uniformly computable orbit-finite generating data for its tuple stabilizers
distinct_from:
  permutation-hnn-realization-of-type-a-actor-is-a2: that proves recursion of the kernel when both edge groups have finite index, by certifying with finite actions; this proves it for edge groups that are pointwise stabilizers of finite tuples, of infinite index, by certifying with tuple stabilizers.
  overgroups-of-finite-bi-index-subgroups-are-recursive: that kills only the centralizer test on stabilizer realizations; this kills the whole kernel problem for them under a uniformity hypothesis on the actor.
  a2-kernel-recursion-ascends-normal-orbit-finite-chains: that is the general certificate principle; this is an application in which every kernel element is shown to commute exactly with the pointwise stabilizer of an explicitly computable tuple.
  type-a-hnn-realization-with-unsolvable-word-problem: that asks for a realization with unsolvable word problem; this shows its "What to try next" item 1 needs an actor without uniform tuple-stabilizer data.
---

**ESTABLISHED** by `tuple-stabilizer-hnn-realization-kernel-proof`
(not independently reviewed; no novelty claimed).

**Setting.** Let `Γ ↷ X` be of type (A), as in
`type-a-action-gives-boone-higman-for-subgroups`, with a fixed finite generating set
and fixed orbit representatives, so that points are encoded by words and indices.
For a finite tuple `T` of points, write `Stab_Γ(T)` for its pointwise stabilizer.

**Uniform tuple-stabilizer data (UTS).** There is an algorithm that, given a finite
tuple `T` of encoded points, outputs:
- a finite set `A_T` of words, each representing an element of `Stab_Γ(T)`;
- a finite set `Y_T` of encoded points,

such that `<A_T>.Y_T = X`. In particular every `Stab_Γ(T)` has finitely many orbits
on `X`.

**Statement.** Assume UTS. Let:
- `T_1, T_2` be finite tuples, and `D_i = Stab_Γ(T_i)`;
- `D_1, D_2` be finitely generated;
- `ψ : D_1 -> D_2` be an isomorphism;
- `π in Sym(X)` satisfy `π d π^-1 = ψ(d)` as permutations for all `d in D_1`.

Then `D_1` is orbit-finite, so `L = Γ*_ψ ↷ X` through `t -> π` is of type `[A_2]`
by `permutation-hnn-realization-of-type-a-actor-is-a2` (a). Its kernel `K` is
recursive, and `<Γ, π> <= Sym(X)` has solvable word problem.

**The mechanism.** Take a kernel element `k` with reduced form
`γ_0 t^(e_1) γ_1 ... t^(e_n) γ_n`. Then `Γ ∩ k^-1 Γ k = Stab_Γ(T_k)` for the explicit
tuple

```text
T_k = union over j of ρ(u_j)^-1 (T_(σ_j)),    u_j = γ_j t^(e_(j+1)) ... t^(e_n) γ_n,
```

where `σ_j = 1` if `e_j = +1` and `σ_j = 2` if `e_j = -1`, and `ρ` is the action map.
This tuple is computable from `k`, and `k` commutes in `L` with every element of
`Stab_Γ(T_k)`. UTS supplies the certificate for principle (1) of
`a2-kernel-recursion-ascends-normal-orbit-finite-chains`.

**Consequence (obstruction).** A witness for
`type-a-hnn-realization-with-unsolvable-word-problem` with tuple-stabilizer edge
groups ("What to try next" item 1 of that node, including `D = Stab_Γ(x_0)`) needs
an actor that fails UTS. That means one of:
- some tuple stabilizer has infinitely many orbits on `X`, i.e. infinitely many
  orbits on tuples of some fixed length extending a given configuration;
- some tuple stabilizer has no finite orbit-covering generating data;
- such data exist for every tuple but cannot be computed uniformly.

This confirms the node's heuristic and makes it necessary: a witness must have
infinitely many orbits on some `X^m`, or non-uniform stabilizer data.

**Not claimed.**
- No specific actor is proved to satisfy UTS. Thompson's `V` on a dyadic orbit is
  expected to satisfy it, since it is highly transitive with finitely generated
  tuple stabilizers, but explicit uniform generators were not written.
- Edge groups that are not tuple stabilizers are not covered.
