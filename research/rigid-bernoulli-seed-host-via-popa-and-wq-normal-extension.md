---
rg: 2
id: rigid-bernoulli-seed-host-via-popa-and-wq-normal-extension
kind: route
title: Untwist the containment cocycle on the Kazhdan subgroup by Popa superrigidity, spread the untwisting along infinite conjugate intersections, and kill the kernel by mixing
target: rigid-bernoulli-seed-relations-embed-their-group-in-the-host
requires:
  - popa-bernoulli-cocycle-superrigidity
  - kun-thom-nonsofic-wreath
  - sofic-passes-to-subgroups
---

# Proof

**0. Diffuse extension.** Every nontrivial standard probability space is a factor of `([0,1],Leb)`. So
`H ↷ (Z,ζ)` is a factor of `H ↷ Z̃ := ([0,1],Leb)^H`. Call the factor map `π : Z̃ → Z` and the measure `ζ̃`.
`Z̃` is mixing, so every infinite subgroup of `H` acts mixingly, hence weakly mixingly and ergodically.

**1. Containment cocycle.** Let `c(h,z)` be the unique `g ∈ G` with `θ(h·z) = g·θ(z)`. As in Step 1 of
`simple-kazhdan-bernoulli-host-via-popa-superrigidity`, `c : H × Z → G` is a measurable cocycle, by
essential freeness of `G ↷ X`. Put `c̃(h,z̃) := c(h,π(z̃))`, a cocycle for `H ↷ Z̃`.

**2. Popa on `H_0`.** Choose right coset representatives `T`, so that `H = ⊔_(t∈T) H_0 t`. Then
`x ↦ (h_0 ↦ (x_(h_0 t))_(t∈T))` conjugates `H_0 ↷ Z̃` to the Bernoulli shift of `H_0` with base
`([0,1]^T, Leb^⊗T)`. That base is standard and non-atomic, so it is isomorphic to `([0,1],Leb)`, and the
restricted action is the diffuse Bernoulli shift of `H_0`.
That shift is s-malleable, and it is weakly mixing because `H_0` is infinite. `H_0` has property (T), so it
is an infinite rigid subgroup of itself and w-normal in itself. Theorem 0.1, quoted in
`popa-bernoulli-cocycle-superrigidity`, gives a measurable `φ : Z̃ → G` and a morphism `ρ_0 : H_0 → G` with
`c̃(h,z̃) = φ(h·z̃) ρ_0(h) φ(z̃)^(-1)` for `h ∈ H_0` and a.e. `z̃`. With the opposite convention, replace `φ` by
`φ^(-1)`.
Define `c'(h,z̃) := φ(h·z̃)^(-1) c̃(h,z̃) φ(z̃)` for all `h ∈ H`. It is a cocycle, and `c'(h,·) = ρ_0(h)` a.e.
for `h ∈ H_0`.

**3. Spreading the untwisting.** Let `E` be the set of `h ∈ H` for which `c'(h,·)` is essentially constant,
and let `ρ(h)` be that constant. By the cocycle identity `E` is a subgroup containing `H_0`, and
`ρ : E → G` is a morphism.

*Lemma.* Let `S <= E` be a subgroup and `a ∈ H` with `S_a := S ∩ a^(-1)Sa` infinite. Then `a ∈ E`.

*Proof.* Put `f := c'(a,·)`. For `h ∈ S_a` both `h` and `aha^(-1)` lie in `S`. The cocycle identity gives
`c'(ah,z̃) = f(h·z̃)ρ(h)`, and, from `ah = (aha^(-1))a`, also `c'(ah,z̃) = ρ(aha^(-1))f(z̃)`. So

```text
f(h·z̃) = ρ(aha^(-1)) · f(z̃) · ρ(h)^(-1)      (h ∈ S_a, a.e. z̃).
```

So `f` is equivariant from `Z̃` to the countable set `G`, on which `S_a` acts by
`h·x = ρ(aha^(-1)) x ρ(h)^(-1)`. The measure `f_*ζ̃` is `S_a`-invariant on a countable set, so each of its atoms
has a finite `S_a`-orbit. Over one such orbit, the indicators of the fibres of `f` span a finite-dimensional
`S_a`-invariant subspace of `L²(Z̃)`. `S_a` is infinite, hence weakly mixing on `Z̃`, so those indicators are
constant. So `f` is essentially constant and `a ∈ E`. ∎

Now induct on `β`. Suppose `H_β <= E` and `a` is one of the generators of `H_(β+1)`. Then
`H_β ∩ a^(-1)H_βa = a^(-1)(H_β ∩ aH_βa^(-1))a` is infinite, so `a ∈ E` by the Lemma, and `H_(β+1) <= E`.
Limit stages are unions. So `E = H`, and `ρ : H → G` is a morphism with `c' = ρ`.

**4. The equivariant map.** Put `ψ(z̃) := φ(z̃)^(-1)·θ(π(z̃)) ∈ X`. For all `h` and a.e. `z̃`:

```text
ψ(h·z̃) = φ(h·z̃)^(-1) c(h,π(z̃)) · θ(π(z̃)) = c'(h,z̃) φ(z̃)^(-1) · θ(π(z̃)) = ρ(h)·ψ(z̃).
```

**5. Finite kernel.** Suppose `ker ρ` is infinite. It acts ergodically on `Z̃` (Step 0) and `ψ` is
`ker ρ`-invariant, so `ψ` is essentially constant, say `x_0`. Then `θ(π(z̃)) = φ(z̃)·x_0 ∈ G·x_0` for a.e.
`z̃`. Since `θ_*π_*ζ̃ = μ_A`, the countable set `G·x_0` has full `μ_A`-measure.
That is impossible, because `μ` has no atoms. `H` is infinite and acts essentially freely, so a.e. `H`-orbit
in `Z` is infinite. `θ` maps it injectively into one `G`-orbit, so `G` is infinite. An atom of `μ` would then
have an infinite `G`-orbit, by freeness, of equal masses. So `ker ρ` is finite. ∎

# Consequences

**1** holds because `ρ(H) ≅ H/ker ρ` is a subgroup of `G`.

**2** is Step 2's coset computation with `H` in place of `H_0` and `H'` in place of `H`. The same `θ` carries
the smaller relation into `R_G|_A`.

**3. Wreaths.** Write `W = A_W ⋊ G_1` with `A_W = ⊕_(G_1/Γ) Z/2Z`, where `G_1` permutes coordinates.
`Γ` is infinite: a finite `Γ` equals each of its compressions, so the compressors would normalize it, and they
generate `G_1`. `[G_1:Γ] = ∞`: an infranormal subgroup of finite index is normal (Step 0 of
`kun-thom-free-nonsofic-action-proof`).

* *wq-normality in one step.* For `b ∈ A_W` and `g ∈ G_1`, `(b,1)(0,g)(b,1)^(-1) = (b − g·b, g)`, so
  `G_1 ∩ bG_1b^(-1) = Stab_(G_1)(b)`. For `b = δ_Γ` this contains `Γ`, so it is infinite. Every `g ∈ G_1` has
  `G_1 ∩ gG_1g^(-1) = G_1`. The `G_1`-translates of `δ_Γ` are the `δ_(gΓ)`, so `G_1` and `δ_Γ` generate `W`,
  and `H_1 = W`.
* *No nonzero lamp has a finite orbit.* Suppose `b ≠ 0` has a finite `G_1`-orbit. Then some finite-index
  subgroup fixes every coset in the finite support of `b`, so it lies in a conjugate of `Γ`, which
  contradicts `[G_1:Γ] = ∞`.
* *Finite normal subgroups.* Let `N ⊴ W` be finite. `N ∩ A_W` is a finite `G_1`-invariant set of lamps, so it
  is `0`. Then `[N,A_W] <= N ∩ A_W = 0`, so each `(b,g) ∈ N` has `g` acting trivially on `G_1/Γ`. `N` projects
  injectively onto a finite normal subgroup `N̄ <= G_1`. Write `N = {(β(n),n) : n ∈ N̄}`. Since `N̄` acts
  trivially on `A_W`, `β` is a morphism, and `β(gng^(-1)) = g·β(n)`. The centralizer of `n` has finite index,
  because `N̄` is finite and normal. So `β(n)` has a finite orbit and `β(n) = 0`.
  So `N = N̄ <= G_1` acts trivially on `G_1/Γ`, hence `N <= Γ`. Then `W/N = A_W ⋊ (G_1/N)` is the wreath
  `(Z/2Z) wr_(Ḡ/Γ̄) Ḡ` with `Ḡ = G_1/N` and `Γ̄ = Γ/N`. Both are Kazhdan, as quotients of Kazhdan groups.
  `Γ̄` is infranormal, since images of compressors compress it and generate `Ḡ`. It is not normal, because
  `Γ` is not normal and contains `N`. By Kun--Thom Theorem A, `W/N` is not sofic.

**Calibration.** With `G = H` the morphism is the identity. For a sofic seed group the theorem gives
nothing: `ρ` can be injective whenever `G` contains `H`, which is the co-induction setting of
`groups-containing-kun-thom-pair-have-nonsofic-actions`.
