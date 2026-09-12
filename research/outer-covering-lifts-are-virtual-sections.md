---
rg: 2
id: outer-covering-lifts-are-virtual-sections
kind: claim
title: Lifting outer classes to automorphisms of a finite-index subgroup is the same as splitting Aut to Out over them
distinct_from:
  finite-central-extension-rf-iff-virtually-splits: that decides residual finiteness of a finite central extension by virtual splitting; this identifies covering-lift constructions with virtual sections of Aut(N) to Out(N) for groups with unique roots, and has no residual finiteness content.
  birman-exact-sequence-does-not-virtually-split: that is the literature theorem that one such extension, the Birman sequence in genus at least four, has no virtual section; this is the elementary equivalence that turns every covering-lift construction into a virtual section.
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

**ESTABLISHED.** No novelty is claimed; both parts are elementary.

**(i) Algebraic form.** Let `N` be a group with unique roots (`x^k = y^k` with
`k ≥ 1` forces `x = y`). Let `H ≤ N` have finite index and `L ≤ Out(N)`.
Suppose `λ: L → Aut(H)` is a homomorphism such that, for every `f ∈ L`, some
`φ ∈ Aut(N)` representing `f` satisfies `φ(H) = H` and `φ|_H = λ(f)`.
- Then `φ` is unique.
- `σ(f) := φ` is a homomorphism `L → Aut(N)` lifting the inclusion
  `L ≤ Out(N)`, so `Aut(N) → Out(N)` splits over `L`.
- Conversely, a splitting over `L` is such a `λ`, with `H = N`.

Free groups and fundamental groups of closed orientable surfaces of genus
`≥ 2` have unique roots.

**(ii) Topological form.** Let `Σ` be a closed orientable surface of genus
`g ≥ 2`, `π: Σ̃ → Σ` a finite unbranched covering, `P ⊂ Σ̃` finite and
nonempty, and `L ≤ Mod(Σ)` of finite index. Let `λ: L → Mod(Σ̃, P)` be a
homomorphism such that each `λ(f)` has a representative `F` covering some
representative `f′` of `f`, i.e. `π∘F = f′∘π`. Then the Birman exact sequence

    1 → π1(Σ, x) → Mod(Σ, x) → Mod(Σ) → 1

splits over a finite-index subgroup of `L`. Conversely, a section over a
finite-index subgroup is such a `λ`: take the trivial cover and `P = {x}`.

Conventions:
- `Mod` is the group of orientation-preserving mapping classes.
- `Mod(Σ̃, P)` consists of isotopy classes, rel `P`, of homeomorphisms
  preserving `P` setwise.
- `λ` is not assumed injective.

**What this says about Boone--Higman.**
- **BFFHZ template.** The one-puncture step of arXiv:2503.21882v2 Section 4
  (`punctured-surface-mcgs-satisfy-permutational-boone-higman`) is a covering
  lift of this shape over a punctured surface.
- **Closed surfaces.** Run over a closed surface, any such construction is
  exactly a virtual section of the Birman sequence. For genus at least four
  Chen--Salter exclude it (`closed-mcgs-have-no-covering-lift-to-marked-covers`).
- **Out(F_n).** Any construction assigning, on a finite-index subgroup of
  `Out(F_n)`, automorphisms of a finite-index subgroup `H ≤ F_n` that extend
  to representatives is exactly a virtual section of `Aut(F_n) → Out(F_n)`.
  See `out-free-groups-virtually-embed-in-aut-free-groups`.

The derivation is `outer-covering-lifts-virtual-sections-proof`.
