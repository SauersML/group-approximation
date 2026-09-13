---
rg: 2
id: radu-edge-coset-action-not-sofic-via-stability
kind: route
title: Correct an orbit chart to a genuine action, round the colouring onto C_chi-orbits with the Cheeger constant, and meet the square firewall
target: radu-edge-coset-action-is-not-sofic
requires:
  - radu-arithmetic-quotient-is-flexibly-permutation-stable
  - radu-horizontal-lattice-expands-on-finite-actions
  - radu-square-lamp-forces-reflections-in-finite-actions
---

Conditional route, modelled on `codense-tau-coset-soficity-forces-permutation-instability`. The
codensity input there is image equality `ρ(C) = ρ(A)`. Here it is the weaker reflection statement of
`radu-square-lamp-forces-reflections-in-finite-actions`.

Suppose `φ : Q → Sym(A)` is `(F, ε)`-multiplicative and an `(F, E, ε)`-orbit approximation of
`Q ↷ Q/C_χ`. Take `F ⊇ {a, b, cac, cbc} ∪ D_4` and `E ⊇ D_4·C_χ`.

1. **Stability.** By `radu-arithmetic-quotient-is-flexibly-permutation-stable`, after padding `A` by
   `o(|A|)` points there is a genuine action `ρ` with `d_H(ρ(s), φ(s)) ≤ η(ε) → 0` on generators,
   hence on the finitely many words of `F`.
2. **The colouring.** Put `f(s) = π_s(C_χ)` on the good set, and arbitrary elsewhere. Equivariance
   gives `f(ρ(h)s) = f(s)` for `h ∈ {a,b,cac,cbc}` off a set of size `ε'|A|`, with `ε' = O(ε + η)`.
   Injectivity gives `f(ρ(g)s) ≠ f(s)` for `g ∈ D_4 \ {1}` off a set of the same size.
3. **Rounding.** On each `ρ(C_χ)`-orbit `O`, let `P_O` be a colour class meeting `O` most, and set
   `f' = colour(P_O)` on `O`. With the uniform Cheeger constant `h > 0` of
   `radu-horizontal-lattice-expands-on-finite-actions`,
   `Σ_P |∂(P ∩ O)| ≥ h Σ_P min(|P ∩ O|, |O \ P|) ≥ h |O \ P_O|`, summed over the colour classes `P`.
   The left side is twice the number of disagreeing edges in `O`. Summing over orbits and the four
   generators gives `d(f, f') = Σ_O |O \ P_O| ≤ 8ε'|A|/h`. `f'` is exactly `C_χ`-invariant.
4. **Firewall.** By item 3 of `radu-square-lamp-forces-reflections-in-finite-actions`, `f'∘ρ(g) = f'`
   for some reflection `g`. So `f(ρ(g)s) = f(s)` off at most `16ε'|A|/h` points. This contradicts
   step 2 once `ε'` is small.

So no orbit approximations with `ε → 0` exist.
