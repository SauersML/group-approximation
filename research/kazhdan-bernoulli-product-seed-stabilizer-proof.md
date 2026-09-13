---
rg: 2
id: kazhdan-bernoulli-product-seed-stabilizer-proof
kind: route
title: Untwist the containment cocycle to a cocycle of τ by the product clause of Popa's theorem, restrict it to stabilizers where it is a morphism, and bound the kernel by ergodicity of the Bernoulli fibre
target: kazhdan-bernoulli-product-seed-stabilizers-embed-in-host
requires:
  - popa-bernoulli-cocycle-superrigidity
  - popa-oe-superrigidity
---

# Proof

**0. Diffuse extension.** Coordinatewise factor maps `([0,1],Leb) → (Y_0,ν_0)` give an `H`-factor map
`π : Z̃ := ([0,1],Leb)^H → Z`. Put `Π := π × id_W`, an `H`-equivariant measure-preserving map
`Z̃ × W → Z × W`.

**1. Containment cocycle.** By essential freeness of `G' ↷ X`, `c(h,ξ)` := the unique `g ∈ G'` with
`θ(h·ξ) = g·θ(ξ)` is defined off a null set, measurable, and satisfies the cocycle identity. This is the argument of
Step 1 of `simple-kazhdan-bernoulli-host-via-popa-superrigidity`. `c̃(h,ξ̃) := c(h,Π(ξ̃))` is a cocycle for the
diagonal action on `Z̃ × W`.

**2. Popa, product clause.** The shift on `Z̃` is a Bernoulli action with diffuse base, hence s-malleable, and it is
weakly mixing because `H` is infinite. `H` is infinite with property (T), so it is an infinite rigid subgroup of
itself, w-normal in itself, and the restriction to it is weakly mixing. The "More generally" clause of Theorem 0.1,
quoted verbatim in `popa-bernoulli-cocycle-superrigidity`, applies to the product of this shift with the arbitrary
action `τ`. It gives a measurable `φ : Z̃ × W → G'` and a cocycle `v : H × W → G'` of `τ` with

```text
c̃(h,ξ̃) = φ(h·ξ̃) · v(h,w) · φ(ξ̃)^(-1)      for all h and a.e. ξ̃ = (z̃,w).
```

With the opposite convention, replace `φ` by `φ^(-1)`.

**3. Equivariance.** Put `ψ(ξ̃) := φ(ξ̃)^(-1)·θ(Π(ξ̃))`. For all `h` and a.e. `ξ̃`,

```text
ψ(h·ξ̃) = φ(h·ξ̃)^(-1) c(h,Π ξ̃)·θ(Π ξ̃) = v(h,w) φ(ξ̃)^(-1)·θ(Π ξ̃) = v(h,w)·ψ(ξ̃).
```

**4. Stabilizer morphisms.** `H` is countable, and `θ` is injective on some conull `E ⊆ Z × W`. By Fubini there is a
conull `W_0 ⊆ W` such that every `w ∈ W_0` satisfies three conditions:

* **(i)** `v(hh',w) = v(h,h'·w)·v(h',w)` for all `h,h' ∈ H`;
* **(ii)** for every `h ∈ H`, `ψ(h·z̃, h·w) = v(h,w)·ψ(z̃,w)` for a.e. `z̃`;
* **(iii)** the section `E_w = {z : (z,w) ∈ E}` is `ζ`-conull.

Fix `w ∈ W_0`. For `h,h' ∈ S_w`, (i) gives `v(hh',w) = v(h,w)·v(h',w)`, so `ρ_w := v(·,w)|_(S_w)` is a morphism.
By (ii), `ψ(h·z̃, w) = ρ_w(h)·ψ(z̃, w)` for `h ∈ S_w` and a.e. `z̃`.

**5. Finite kernel.** Let `B := {w ∈ W_0 : ker ρ_w is infinite}`. It is measurable, since it is a countable Boolean
combination of the sets `{w : h·w = w, v(h,w) = 1}`. Suppose `ω(B) > 0`, and take `w ∈ B`.

* `N_w := ker ρ_w` is infinite and acts freely on the index set `H` by translation, so all its orbits there are
  infinite. By Popa's criterion (`popa-oe-superrigidity`), the shift on `Z̃` restricted to `N_w` is weakly mixing,
  hence ergodic.
* `z̃ ↦ ψ(z̃,w)` is `N_w`-invariant a.e., so it is essentially constant, say `x_w`. So `θ(π(z̃), w) = φ(z̃,w)·x_w`
  lies in the countable set `G'·x_w` for a.e. `z̃`. The set `{z : θ(z,w) ∈ G'·x_w}` is measurable and its
  `π`-preimage is conull, so it is `ζ`-conull.
* By (iii), `θ(·,w)` is injective on a conull subset of `Z`, and it maps that subset into a countable set. So a conull
  subset of `Z` is countable. But `ζ` has no atoms, because `H` is infinite and the base is nontrivial.

This is a contradiction. So `ω(B) = 0`. ∎

**Calibration.** For trivial `τ`, `v` is a morphism `H → G'` and Step 5 is Step 5 of
`rigid-bernoulli-seed-host-via-popa-and-wq-normal-extension`. For essentially free `τ`, every `S_w` is trivial and
Steps 4 and 5 are empty, which is why such products stay open.
