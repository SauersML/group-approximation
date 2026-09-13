---
rg: 2
id: radu-square-lamp-forces-reflections-in-finite-actions-proof
kind: route
title: Push the edge-lamp host through a finite permutation module with Z/32 coefficients; the mark survives unless the square has a reflection in the stabilizer
target: radu-square-lamp-forces-reflections-in-finite-actions
requires:
  - radu-metabelian-quotient-embeds-in-edge-lamp-wreath
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - radu-delta-squared-orbit-is-signed-permutation-module
artifacts:
  - research/artifacts/radu-edge-lamp-host-and-square-firewall-2026-09-13.md
---

# Proof

**Item 1.** Put `K = Stab_Q(p) ⊇ C_χ` and `N = ker(Q → Sym Ω)`, so `N ⊆ K`. Let `Ψ` be the composite

```text
Γ_R → G_2 → C_1(Y) ⋊ Q → C_1^xz(Y) ⋊ Q → Z[Q/C_χ] ⋊ Q → (Z/32)[Q/K] ⋊ Q/N.
```

* The first two arrows are the embedding of `radu-metabelian-quotient-embeds-in-edge-lamp-wreath`.
* The third projects onto the `Q`-invariant summand spanned by `{x,z}`-edges.
* The fourth is `e ↦ e − ē`.
* The last pushes forward along `gC_χ ↦ gK` and reduces mod 32.

Every arrow is a homomorphism, and the target is finite. Let `H = D_4 ∩ K`. The points `gK`, `g ∈ D_4`,
coincide exactly along cosets of `H`. By item 2 of the embedding claim, `(xz)^4 ↦ 2Σ_(g∈D_4) ε(g) gK`.

Suppose `ε|_H = 1`. Then this sum equals `2|H| Σ_(gH) ε(g)[gK]`, with coefficients
`±2|H| ∈ {±2, ±4, ±8, ±16}`, all nonzero mod 32. But `(xz)^4` lies in the finite residual of `Γ_R`
(`radu-bmw-lattice-embeds-in-titz-witzel-kernel`, item 2), so its image in a finite group is trivial,
a contradiction. Hence `H` contains `g` with `ε(g) = −1`. The elements of `D_4` with `ε = −1` are
`x, z, c, xzc`.

**Item 2.** Apply item 1 to the point `C_χN` of `Q/C_χN`. Some reflection `g ∈ D_4` lies in `C_χN`.
Write `g = kn` with `k ∈ C_χ` and `n ∈ N`. Then `n = k^(−1)g ∈ H_Q ∩ N`. Since `ψ'` restricts to `ε`
on `D_4` and is trivial on `C_χ`, `ψ'(n) = ψ'(g) = −1`.

If `ker ψ'` were closed, it would be a union of cosets of `H_Q ∩ N` for some `N`, so `H_Q ∩ N` would
lie in `ker ψ'`. It does not.

**Item 3.** `ρ` factors through a finite group, so the orbit `Q·f ⊂ B^A`, with
`(q·f)(s) = f(ρ(q)^(−1)s)`, is finite. The point `f` is fixed by `a, b, cac, cbc`, all involutions.
Item 1 gives a reflection `g` with `g·f = f`, so `f∘ρ(g)^(−1) = f`, and `g^(−1) = g`.

In an orbit approximation of `Q ↷ Q/C_χ`, the colouring `s ↦ π_s(C_χ)` is invariant under the four
generators of `C_χ` on the good set, and it differs from its translate by every `g ∈ D_4 \ {1}` there.
With zero invariance defect on all of `A`, this contradicts item 3. ∎
