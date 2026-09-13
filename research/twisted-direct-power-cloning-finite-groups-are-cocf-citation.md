---
rg: 2
id: twisted-direct-power-cloning-finite-groups-are-cocf-citation
kind: route
title: "Import: V_(G,theta) is coCF (Berns-Zieve-Fry-Gillings-Hoganson-Mathews Thm 4.3)"
target: twisted-direct-power-cloning-finite-groups-are-cocf
requires: []
artifacts:
  - research/artifacts/zp-lehnert-2-16-2026-09-13.md
---

Literature import, not a reproof.

R. Berns-Zieve, D. Fry, J. Gillings, H. Hoganson, H. Mathews, *Groups with
context-free co-word problem and embeddings into Thompson's group V*,
arXiv:1407.7745v2 (3 Dec 2014), Theorem 4.3: for every finite group `G` and
homomorphism `θ: G → G`, `V_(G,θ)` is coCF.

Proof read from the PDF (2026-09-13, §4, pp. 11–12): a pushdown automaton `P`
with a loading, reading, and clean-up phase accepts a language `𝓛_P` with
`CoWP(V_(G,θ)) = (𝓛_P)°`, the cyclic shift of `𝓛_P`. Context-free languages
are closed under cyclic shift (Maslov, *Problemy Peredači Informacii* 9 (1973)
81–87), so `CoWP(V_(G,θ))` is context-free and `V_(G,θ)` is coCF. The class of
coCF groups is generating-set independent (Holt–Rees–Röver–Thomas, J. London
Math. Soc. 71 (2005) 643–657).

`V_(G,θ)` is the Thompson-like group of the twisted direct-power cloning system
`G_n = S_n ⋉ G^n` (Berns-Zieve et al. Def. 2.11, `H = S_∞ ⋉_φ (⊕G)`; the same
family appears in Zaremsky, arXiv:1606.08762, Example 3.1 variation), so this
is a cloning system on finite groups.
