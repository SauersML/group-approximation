---
rg: 2
id: subset-stable-marker-flip-regrouping-proof
kind: route
title: Flip one coset of the normal subgroup at a time; each flip reads only other cosets and leaves the flip set unchanged
target: subset-stable-marker-flips-are-virtually-formalizable
requires:
  - structurally-reversible-automata-are-formalizable
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
---

Sections 5.1–5.2 of the artifact.
- **Each piece is a track shear.** `tau_t` flips cell `g in Nt` when the marker at `g` holds, and that
  marker reads the cells `gw`. By normality, `gw in Nt` iff `w in N`, so `tau_t` reads only other
  tracks. It commutes with left translation by `N`, so it is an `N`-automaton.
- **The word equals `tau`.** `tau_(t_1)` flips `F(x) ∩ Nt_1 ⊆ F(x)`, so by hypothesis the flip set
  stays `F(x)`. Inductively the word flips each cell of `F(x)` once.
- **Involution.** `F(tau x) = F(x)`, so `tau o tau = id`.
- **Formal pair.** Track shears are formal involutions, so by the prerequisite (with regrouping) the
  reversed word is a two-sided formal inverse.
- **The example.** For the six-cell marker rule and any `S ⊆ F(x)`:
  - a marker at `j in F(x)` reads no cell of `F(x)`, by Lemma 2.1 of the refutation artifact;
  - a marker at `j notin F(x)` near a flipped `i` needs a `0` at `i − 1` or `i + 1`, and those cells
    hold `1` and are not in `F(x)`, so they don't flip.
  So the flip set survives partial flipping, and `{±1, ±2, ±3}` avoids `4Z`.
