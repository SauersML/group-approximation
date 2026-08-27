---
rg: 2
id: atlas-kernel-window-length-nine-proof
kind: route
title: A surviving retraction to the direct product certifies insufficiency below length nine
target: atlas-kernel-window-length-nine
requires: [atlas-relator-central-sufficiency]
---

# A surviving retraction to the direct product certifies insufficiency below length nine

**The screen.**  Suppose `T ⊆ R̄` finite and `φ : P̄ ↠ F` a nontrivial
finite quotient with `T ⊆ ker φ`.  If `N̄ ≤ ⟨⟨T⟩⟩` held, then by
`atlas-relator-central-sufficiency` the group `V = P̄/⟨⟨T⟩⟩` would be a
perfect central extension of the infinite simple `Q` (simplicity of
`Q = L_{F₂}(1,2)^×`: recorded via Preusser in the repo's source-verified
imports), and `φ` would factor through a nontrivial finite quotient of
`V`.  But a perfect `V` with central `Z` and `V/Z` infinite simple has
none: for `M ⊴ V` of finite index, the image of `M` in `V/Z` is normal,
hence trivial or everything; if everything then `MZ = V` and
`V/M ≅ Z/(Z ∩ M)` is an abelian quotient of a perfect group, trivial; if
trivial then `M ≤ Z` and `V/M` surjects onto the infinite `V/Z`,
contradicting finiteness.  So no such `φ` may exist for a usable `T`.

**The computation.**  The retraction `(p₁,p₂) : A₈ * A₈ ↠ A₈ × A₈`
(identity on each factor) is such a `φ` whenever it kills `T`.
`experiments/atlas_relator_projection_screen.py` and
`experiments/atlas_relator_finite_quotient_screen.py` verify by exact
arithmetic that all `20 / 264 / 2,734` spanning-tree generators at
half-radius `2 / 3 / 4` die under it, while at half-radius `5` exactly
`234` of `27,256` survive with nontrivial projections (reproducing the
committed `experiments/atlas-kernel-radius5-summary.json` count
`27,022 + 234`); the shortest survivor has X-length `9`.  Reproduction:
`python3 experiments/atlas_relator_finite_quotient_screen.py --radius 4`
(seconds) and `--radius 5` (minutes).

**Closing the length gap.**  Proposition 4 of
`notes/FALSE_RECURSIVE_ATLAS_EXHAUSTION.md` states that the half-radius-`r`
spanning-tree set generates, as a subgroup, every kernel element of
X-length `≤ 2r`.  A homomorphism killing the generators kills the
subgroup, so every kernel element of X-length `≤ 8` dies under
`(p₁,p₂)`.  Any `T` of such words has `T ⊆ ker(p₁,p₂)`, and the screen
applies with `F = A₈ × A₈`.  Sharpness and the `L₀ ≥ 9` reading are
immediate from the length-9 survivor.  Full derivation and tables:
`research/artifacts/atlas-relator-extraction-2026-08-15.md` §(b).
