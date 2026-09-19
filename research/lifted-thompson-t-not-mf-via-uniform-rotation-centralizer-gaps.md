---
rg: 2
id: lifted-thompson-t-not-mf-via-uniform-rotation-centralizer-gaps
kind: route
title: T-bar is not MF once the corona gaps of r_k in the rotation centralizers C_T(r_k) beat the rounding error at one level per displacement
target: lifted-thompson-t-is-not-mf
requires:
  - central-power-quotient-gaps-converge-to-the-extension-gap
  - lifted-thompson-t-quotients-are-rotation-centralizers
  - lifted-thompson-t-mf-radical-dichotomy
  - rotation-centralizer-rotation-gaps-are-uniform
---

**Proof.** Fix a finite presentation `T̄ = ⟨S | R⟩` with `z ∈ S`. `T̄` is finitely presented
(item 4 of `lifted-thompson-t-mf-radical-dichotomy`), and adjoining the generator `z` with one
defining relator keeps the presentation finite.
1. By `lifted-thompson-t-quotients-are-rotation-centralizers`, `z` is central, `⟨⟨z^{2^k}⟩⟩ =
   ⟨z^{2^k}⟩`, and `G_{2^k} = ⟨S | R ∪ {z^{2^k}}⟩ ≅ C_T(r_k)` with `z ↦ r_k`. This identifies
   the gaps named in `rotation-centralizer-rotation-gaps-are-uniform` with the gaps
   `δ_{2^k}(c)` of `central-power-quotient-gaps-converge-to-the-extension-gap`.
2. (UG) is condition (d) of item 3 of that claim for `M = {2^k : k ≥ 0}`.
3. So condition (a) holds: `z ∈ Rad_MF(T̄)`, which is `lifted-thompson-t-is-not-mf`. ∎

## Comparison with the eigencorner route

- `lifted-thompson-t-not-mf-via-central-eigencorners` needs a spectral projection of `ρ(z)` in
  `ρ(T̄)' ∩ Q`. That prerequisite has no live route, and the recorded attempts die on the arc
  part of `sp(ρ(z))`. This route never cuts the spectrum of `ρ(z)`. It moves the whole
  difficulty to finite tuples in which `z` has exact finite order.
- The price is quantitative. Qualitative fullness of each `C_T(r_k)` (equivalently of `T`, by
  item 4 of `central-eigencorners-die-over-full-radical-quotients`) is not enough. Uniformity
  in `k` is needed, and it cannot be weakened to any rate slower than `Lπ 2^{-k}` (item 4 of the
  gap claim).
- The prerequisite is equivalent to the target, so this route loses nothing. It is a
  reformulation, not a reduction to something known to be weaker. Its use is that it states
  the target entirely inside the torsion quotients, where finite-order spectral cutting is
  exact.
