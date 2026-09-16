---
rg: 2
id: permutation-hnn-realization-of-type-a-actor-is-a2
kind: claim
title: Without injectivity, an HNN extension of a type (A) actor realized by one more permutation is a type [A_2] actor with free kernel, recursive when both edge groups have finite index
distinct_from:
  stable-permutation-hnn-of-type-a-actor-is-type-a: that assumes the realization is injective and concludes type (A); this drops injectivity, concludes type [A_2] with a free kernel that meets every conjugate of the actor trivially, and studies when that kernel is recursive.
  normalizer-extension-of-type-a-actor-is-a2-cover: that extends the actor by a free group of permutations normalizing it; this adds one permutation that conjugates one orbit-finite subgroup onto another and need not normalize the actor.
  a2-kernel-recursion-ascends-normal-orbit-finite-chains: that is the general certificate principle for kernels of type [A_2] actions; this constructs a family of type [A_2] actions and applies the principle to the finite-index case.
---

**ESTABLISHED** by `permutation-hnn-realization-of-type-a-actor-is-a2-proof`.

**Setting.** Let `Γ` act on `X` of type (A), in the sense of
`type-a-action-gives-boone-higman-for-subgroups`:
- the action is faithful;
- `Γ` is finitely presented;
- point stabilizers are finitely generated;
- there are finitely many orbits of two-element subsets.

Let `D_1, D_2 <= Γ` be finitely generated, with `D_1` having finitely many orbits on
`X`. Let `ψ : D_1 -> D_2` be an isomorphism, and let `π in Sym(X)` satisfy
`π d π^-1 = ψ(d)` as permutations for every `d in D_1`. Put

```text
L = Γ*_ψ = < Γ, t | t d t^-1 = ψ(d), d in D_1 >,
```

let `ρ : L -> Sym(X)` extend the action of `Γ` by `t -> π`, and let `K = ker ρ`.
**No injectivity of `ρ` is assumed.**

**(a) Type [A_2] with free kernel.**
- `L ↷ X` through `ρ` is of type `[A_2]` in the sense of Fournier-Facio--Wu--Zaremsky
  (arXiv:2603.24687): `L` is finitely presented, point stabilizers are finitely
  generated, and there are finitely many orbits on `X x X`.
- Its image is `<Γ, π> <= Sym(X)`.
- `K ∩ gΓg^-1 = 1` for every `g in L`, so `K` is a free group.
- `K` is recursive iff `<Γ, π>` has solvable word problem.

**(b) Finite-index edge groups.** If `D_1` and `D_2` both have finite index in `Γ`,
then `K` is recursive, so `<Γ, π>` has solvable word problem.

**(c) Centralizer reduction.** The map sending a word `γ` in the generators of `Γ` to
the word `γ t γ^-1 t^-1` many-one reduces `C_Γ(π) = {γ in Γ : γπ = πγ}` to `K`. So if
`C_Γ(π)` is not recursive, then `K` is not recursive, and `<Γ, π>` has unsolvable
word problem.
