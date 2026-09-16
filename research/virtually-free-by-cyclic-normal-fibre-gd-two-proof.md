---
rg: 2
id: virtually-free-by-cyclic-normal-fibre-gd-two-proof
kind: route
title: Normal fibres and centers are free normal subgroups with tree-acting quotients
target: virtually-free-by-cyclic-normal-fibre-gives-gd-two
requires: [free-by-virtually-cyclic-torsion-free-groups-have-gd-two]
artifacts:
  - research/artifacts/eg-special-case-virtually-free-by-cyclic-2026-09-16.md
---

## Why sufficient

This is Theorem B and Corollaries B1--B3 of the cited artifact. Each case produces a free
normal subgroup `N ⊲ G` whose quotient acts on a tree without inversions and with finite
stabilizers. The required claim then gives `gd G = cd G ≤ 2`.

**(i) Normal fibre.**
- Take `N = ker χ`. It is free and normal in `G` by hypothesis.
- `G/N` contains `H/N ≅ Z` with finite index, so it is virtually cyclic, which the required
  claim covers.

The sub-cases:
- If `H ⊲ G` and `ψ∘c_g = ±ψ` for all `g`, then `g^{-1}Fg = ker(ψ∘c_g) = F`.
- If `b_1(H) = 1`, each `ψ∘c_g` is a surjection `H → Z` in a rank-one lattice, so it is `±ψ`.
- If `χ` is `G`-invariant, `ker χ` is normal. Moreover, by restriction--transfer, `χ` extends
  to `G → Q`. Its kernel is torsion-free and virtually `ker χ`, hence free by Serre and
  Stallings--Swan.

**(ii) Periodic monodromy.**
- Let `H ⊲ G` be the normal core of a finite-index `F_n × Z`, with `n ≥ 2`.
- A central `(w, t^k) ∈ H` has `w` commuting with a finite-index subgroup of `F_n`. That
  subgroup is nonabelian, so `w = 1`. Hence `Z(H) = H ∩ (1 × Z) ≅ Z`.
- `Z(H)` is characteristic in `H`, so it is normal in `G`.
- `H/Z(H)` projects isomorphically onto a finite-index subgroup of `F_n`, so `G/Z(H)` is
  finitely generated and virtually free.
- By Karrass--Pietrowski--Solitar, J. Austral. Math. Soc. 16 (1973), recalled and not fetched,
  `G/Z(H)` acts on a tree without inversions and with finite stabilizers. Take `N = Z(H)`.

If `φ^k = inn(a)` in `F_n ⋊_φ Z`, then `a^{-1}t^k` centralizes `F_n`, so `⟨F_n, a^{-1}t^k⟩` is
an `F_n × Z` of index `k`.
