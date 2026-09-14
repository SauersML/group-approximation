---
rg: 2
id: kazhdan-marked-limits-eventually-uniform-expanders
kind: claim
title: Every sequence of finite marked groups converging to a Kazhdan group is eventually a uniform expander family, for any marking
distinct_from:
  finite-simple-groups-converge-to-simple-kazhdan-group: that constructs specific approximants of G_X as quotients of EL_3 over a free algebra, with the elementary marking; this says that EVERY finite approximation of ANY Kazhdan group, for ANY finite generating set, eventually expands.
  primitive-binary-words-give-four-regular-simple-expanders: that is one explicit four-regular family with an absolute gap; this is the marking-free transfer from (T) of the limit to all its finite approximations.
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part1.md
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part3.md
---

**ESTABLISHED (unreviewed).** Let `G` have property (T) with finite generating set `T`. There are `κ > 0` and a finite set
`R_0` of relators such that, if `(Q_k, T_k) → (G, T)` in the space of marked groups with `Q_k` finite, then for all large `k`:
- `Q_k` is a marked quotient of the Kazhdan group `F(T)/⟨⟨R_0⟩⟩`;
- the normalized adjacency operator of `Cay(Q_k, T_k)` has spectrum in `[−1, 1 − κ^2/(2|T^±|)]` on `ℓ^2_0(Q_k)`.

If `G` is infinite, then `|Q_k| → ∞`, so these Cayley graphs form a family of expanders.

For the note: every sequence of finite groups converging to `G_X`, for every finite generating set of `G_X`, is
eventually an expander family. The expander sentence then needs no choice of models or marking.

Credit: an immediate consequence of Shalom's openness of (T) plus Margulis' argument. The sofic version is Kun,
arXiv:1606.04471 (Bowen's conjecture). Folklore level; claimed only as a recorded lemma.

Route: `kazhdan-marked-limits-eventually-uniform-expanders-proof`.
