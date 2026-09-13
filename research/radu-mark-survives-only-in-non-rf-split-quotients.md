---
rg: 2
id: radu-mark-survives-only-in-non-rf-split-quotients
kind: claim
title: A quotient of Radu's lattice that keeps the mark and maps onto a finite-index subgroup of its arithmetic quotient is not residually finite, splits over the free kernel, and conjugates the mark's root to its inverse
distinct_from:
  radu-square-lamp-forces-reflections-in-finite-actions: that proves every finite-index normal subgroup of Q contains a sign-reversing slab element; this consumes that fact to constrain arbitrary, possibly infinite, quotients of Gamma_R in which (xz)^4 survives.
  radu-delta-squared-orbit-is-signed-permutation-module: that computes the sign character of the xz-slab on <(xz)^2> and its parity lemma for finite quotients of G_2; this applies the same sign to every quotient of Gamma_R whose kernel surjects, modulo the free kernel, onto a finite-index subgroup of Q.
  radu-bmw-lattice-sofic: that is the soficity root; this is a structural statement about quotients, in particular about the amenable quotients a residual-amenability proof of soficity would need.
---

**ESTABLISHED.**  Notation of `radu-delta-squared-orbit-is-signed-permutation-module` and
`radu-horizontal-quotient-is-arithmetic-lattice`: `Γ_R` is Radu's BMW lattice, `δ = xz`,
`K = Λ_v = ker(ρ : Γ_R → Q)` is the free kernel, `Q` the cocompact arithmetic lattice in
`PGL_2(Q_2) × PGL_2(Q_2)`, `H_Γ = <a,b,c,x,z>` the xz-slab and `ψ'` its sign character.

Let `N ◁ Γ_R` be a normal subgroup with `δ^4 ∉ N` and `M := NK` of finite index in `Γ_R`.
Put `B := K/(N ∩ K)`. Then:

1. **Not residually finite.** `Γ_R/N` is infinite and not residually finite.
2. **Splitting.** `M/(N ∩ K) = K/(N ∩ K) × N/(N ∩ K)`, an internal direct product. So
   `B ≅ M/N`, a finite-index normal subgroup of `Γ_R/N`, and `B` is finitely generated.
3. **Sign reversal.** Some `k ∈ K` satisfies `k δ^2 k^(−1) ≡ δ^(−2)` modulo `N`. So the image of
   `δ^2` in `B` is conjugate in `B` to its inverse, `δ^4` maps into `[B,B]`, and `B` is not abelian.

**Consequence for amenable quotients.** If `Γ_R/N` is amenable and `ρ(N)` has finite index in `Q`,
then 1–3 hold. With `radu-arithmetic-quotient-normal-subgroups-finite-or-finite-index` (OPEN here:
the normal subgroup theorem for `Q`, not yet pinned at source), every amenable quotient of `Γ_R`
satisfies that hypothesis. An amenable quotient in which the mark survives is then a finitely
generated amenable group that is not residually finite and is virtually a non-abelian quotient `B`
of the free kernel, in which `δ^2` is conjugate to `δ^(−2)`. In particular no amenable quotient
whose kernel image `B` is abelian keeps the mark. This answers, in the negative direction only, the
"balance in amenable quotients" blocker recorded in
`research/artifacts/radu-lattice-b2-anchored-gadget-2026-09-12.md` §4: such a quotient must be
non-residually-finite and non-abelian on the kernel.

Proof in `radu-mark-split-quotient-proof`.
