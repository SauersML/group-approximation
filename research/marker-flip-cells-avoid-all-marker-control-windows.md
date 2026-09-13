---
rg: 2
id: marker-flip-cells-avoid-all-marker-control-windows
kind: claim
title: For the integer marker involution, no flipped cell lies in the control window of any active marker
distinct_from:
  binary-left-inverse-pairs-need-not-be-formalizable: that refutes plain one-track formalizability of this marker over the integers and uses that markers within distance 3 exclude each other; this records the sharp distance bound 5 with the full case table and the invariance of the marker set under partial flips.
  subset-stable-marker-flips-are-virtually-formalizable: that formalizes marker flips after regrouping, assuming the flip set survives partial flipping (checked for this marker in its artifact, Section 5.2); this is the stand-alone Boolean disjointness statement for the integer marker, with no regrouping.
  injective-binary-automata-are-stably-formalizable: that is the open stable-formalizability hub; this is one structural input, not a decision.
artifacts:
  - research/artifacts/marker-stable-formalization-residue-2026-09-12.md
---

**ESTABLISHED** (passed by w3-vf-nonlinear on 62f488374; the proof gap and case texts it flagged are
fixed here). Let `tau` be the marker involution on `{0,1}^Z`: flip cell `i` exactly when
`(x_(i-3), x_(i-2), x_(i-1), x_(i+1), x_(i+2), x_(i+3)) = (0,0,1,1,0,0)`. Write `m_i = L_i R_i` with
`L_i = (1+x_(i-3))(1+x_(i-2)) x_(i-1)` and `R_i = x_(i+1)(1+x_(i+2))(1+x_(i+3))`. The control window
`C_i = {i-3, i-2, i-1, i+1, i+2, i+3}` omits `i`. Let `M(x)` be the set of markers.

**Statement.** On every Boolean configuration:
1. two markers are at distance `>= 5`, and the bound is sharp;
2. no marker lies in the control window of another marker;
3. `M(x + 1_S) = M(x)` for every `S ⊆ M(x)`. In particular `M(tau x) = M(x)` and `tau^2 = id`.

**Proof of 1.** A marker at `i` fixes `x_(i-3) = x_(i-2) = 0`, `x_(i-1) = x_(i+1) = 1` and
`x_(i+2) = x_(i+3) = 0`. A marker at `i + d` with `1 <= d <= 4` needs:
- `d = 1`: `x_(i+2) = 1`, the first cell of its right context;
- `d = 2`: `x_(i-1) = 0`, the first cell of its left context;
- `d = 3`: `x_(i+2) = 1`, the `1` of its left context `001`;
- `d = 4`: `x_(i+1) = 0`, the first cell of its left context.

Each contradicts the marker at `i`. The pattern is symmetric under reflection about the marker, which
rules out `d = -1, ..., -4`. For sharpness, `0,0,1,*,1,0,0,1,*,1,0,0` on cells `i-3, ..., i+8` has
markers at `i` and `i + 5`.

**Proof of 2.** Every cell of `C_i` is within distance 3 of `i`.

**Proof of 3.** Put `x' = x + 1_S`.
- If `i ∈ M(x)`, then `C_i` contains no marker by 2, so `x` and `x'` agree on `C_i` and `i ∈ M(x')`.
- If `i ∈ M(x') \ M(x)`, then `x` and `x'` differ on `C_i`, so some `j ∈ S ⊆ M(x)` lies in `C_i`.
  By the first case `j ∈ M(x')`. So `x'` has markers `i` and `j` at distance `<= 3`, contradicting 1
  for `x'`.

**Use.** This is a Boolean fact. Formally, in the free ring `F_2[X]`, the substitution
`x_j -> x_j + m_j` perturbs `m_i` through every `j ∈ C_i`. So the one-ancilla Bennett word has a
formally nonzero, Boolean-vanishing residue, whose lowest-degree part comes from the adjacent cells
`j = i -+ 1`; see `one-ancilla-marker-residue-is-supported-on-window-overlaps`.

## Attempts

- Distances `d = 5, 6, 7` are all realizable, so the bound is sharp. For `d = 5` the windows `C_i` and
  `C_(i+5)` share `{i+2, i+3}`. That overlap is a Boolean feature only and does not locate the formal
  residue.
- Verified by w3-vf-nonlinear (PASS, 62f488374). Both of its notes are applied above: the reverse
  inclusion in 3, and the `d = 1` and `d = 3` case texts.
