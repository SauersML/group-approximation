---
rg: 2
id: leavitt-kazhdan-cover-rf-iff-kernel-rf
kind: claim
title: A torsion-free hyperbolic cover of the binary Leavitt unit group is residually finite exactly when its kernel is
distinct_from:
  hyperbolic-kazhdan-cover-of-leavitt-unit-group: that constructs the Belegradek--Osin cover and shows the kernel fills every finite image; this computes the cover's finite quotients, profinite completion and residual finiteness from the kernel alone.
  rips-kernel-without-finite-quotients: that asks for a finite-quotient-free kernel over any finitely presented non-residually-finite quotient; this shows that over the Leavitt quotient the kernel condition is equivalent to the cover having no finite quotient, so the quotient contributes no residual-finiteness failure.
  acyclic-quotientless-extension-completion-is-kernel-completion: that is the general extension lemma with no geometry; this applies it to hyperbolic covers of the Leavitt unit group and adds the centralizer argument, which needs hyperbolicity and torsion-freeness.
artifacts:
  - research/artifacts/hyperbolic-no-finite-quotient-leavitt-cover-2026-09-12.md
---

**ESTABLISHED.** Put `R = L_(F_2)(1,2)`. Let

```text
1 -> N -> G -> R^x -> 1
```

be exact, with `G` torsion-free word-hyperbolic and `N` finitely generated.
The Belegradek--Osin cover in `hyperbolic-kazhdan-cover-of-leavitt-unit-group`,
built on a torsion-free cocompact `Sp(2,1)` lattice, is one such extension.
Then:

1. **Finite quotients.** The finite quotients of `G` are exactly the groups
   `N/K` with `K <= N` normal in `G` and of finite index in `N`. The inclusion
   induces `N^ ≅ G^`.
2. **Quotient-freeness.** `G` has a nontrivial finite quotient iff `N` has one.
3. **Residual finiteness.** `G` is residually finite iff `N` is.

**What this pins down.** Simplicity, acyclicity and nonsoficity of `R^x`
contribute nothing to the residual finiteness of such a cover. Every finite
image of `G` is a finite image of `N`, and a finite-residual element of `G`
forces one in `N`.

So a negative answer to Gromov's question through this cover is exactly a
non-residually-finite kernel `N`. That kernel is an infinite normal subgroup
of infinite index in a hyperbolic group, and a quotient of the lattice.
Belegradek--Osin say nothing about its finite images.

Proof in `leavitt-kazhdan-cover-rf-iff-kernel-rf-proof`. No novelty claimed.
Not Lean-verified and not independently reviewed.
