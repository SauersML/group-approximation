---
rg: 2
id: kazhdan-quotient-sofic-iff-injective-block-representation
kind: claim
title: A quotient by a normal Kazhdan subgroup is sofic iff some sofic approximation moves the kernel's expander blocks injectively
distinct_from:
  kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient: that is the case where the quotient has no nontrivial homomorphism into a universal sofic group, so every block representation is trivial; this constructs the block representation for every quotient and shows that soficity of the quotient is exactly the existence of an injective one.
  sofic-quotients-by-kazhdan-normal-subgroups-are-sofic: that is the open permanence statement for all sofic groups and Kazhdan kernels; this is an unconditional block-level reformulation of soficity of one quotient, which that claim would have to supply.
  flexible-p-stability-passes-to-fg-normal-quotients: that descends genuine permutation actions to the orbit set of a finitely generated kernel; this descends arbitrary sofic approximations to the expander blocks of a Kazhdan kernel, where no genuine action is available.
---

**ESTABLISHED.** Let `1 -> N -> G -> Q -> 1` be exact with `G` countable and
sofic, and `N` infinite and Kazhdan with finite symmetric generating set `S`.

**(a) Block representation.** Let `sigma_n : G -> Sym(X_n)` be a sofic
approximation. Edit `o(|X_n|)` edges of the `S`-graphs of `sigma_n|N` into a
disjoint union of blocks with a uniform Cheeger constant
(`kun-expander-decomposition-formalized`). Then elements of `G` map blocks
almost onto blocks, and this induces a homomorphism

```text
tau_sigma : Q -> S_U        (S_U the universal sofic group along U)
```

with `tau_sigma(gN)` sending the `k`-th point of a block `B` to the `k`-th point
of the block `beta_g(B) ≈ sigma(g)B`. It is well defined up to conjugation in
`S_U`:
- two uniform-Cheeger edits agree on all but `o(|X_n|)` points;
- a change of block orderings conjugates `tau_sigma` by a blockwise permutation.

**(b) Criterion.** `Q` is sofic if and only if some sofic approximation
`sigma` of `G` has `tau_sigma` injective.

**Consequences.**
- `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient` is the case
  where `tau_sigma` is trivial for every `sigma`.
- `sofic-quotients-by-kazhdan-normal-subgroups-are-sofic` is equivalent to:
  for every such extension with `G` sofic, some sofic approximation of `G`
  moves the kernel's blocks by an injective representation of `Q`.
- A proof of that permanence claim must therefore *construct* new approximations
  of `G`. A single approximation can have trivial `tau_sigma` even when `Q` is
  sofic: in the coset models `G -> Sym(G/K_n)` of a residually finite `G`, the
  `N`-blocks are the `NK_n`-cosets. There `tau_sigma` is the action of `Q` on
  finite quotients of `Q`, and it is injective only along chains separating
  the elements of `Q`.
- The product construction in the proof of (b) needs a sofic approximation of
  `Q` itself, so it is circular as a route to permanence.

Derivation: `kazhdan-quotient-block-representation-proof`.

The criterion is a reformulation. It does not settle permanence and makes no
claim of novelty beyond packaging Theorem 6 of
`research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md` for
arbitrary quotients.
