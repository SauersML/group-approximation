---
rg: 2
id: marker-flip-cells-avoid-all-marker-control-windows
kind: claim
title: For the integer marker involution, no flipped cell lies in the control window of any active marker
distinct_from:
  binary-left-inverse-pairs-need-not-be-formalizable: that refutes plain one-track formalizability of this marker over the integers; this is the finite combinatorial disjointness fact underneath its involution property, used to locate the one-ancilla formal residue.
  injective-binary-automata-are-stably-formalizable: that is the open stable-formalizability hub; this is one structural input, not a decision.
artifacts:
  - research/artifacts/marker-stable-formalization-residue-2026-09-12.md
---

**ESTABLISHED.** Let `tau` be the marker involution on `{0,1}^Z`: flip cell `i` exactly when
`(x_{i-3},x_{i-2},x_{i-1},x_{i+1},x_{i+2},x_{i+3}) = (0,0,1,1,0,0)`. Write the marker indicator
`m_i = L_i R_i` with `L_i = (1+x_{i-3})(1+x_{i-2})x_{i-1}` and `R_i = x_{i+1}(1+x_{i+2})(1+x_{i+3})`,
and `C_i = {i-3,i-2,i-1,i+1,i+2,i+3}` the cells it reads (its control window; `i in C_i` is false).

**Statement.** On every Boolean configuration, if `i` and `j` are both markers then `|i-j| >= 5`; and
no flipped cell lies in any active marker's control window: if `m_i(x)=1` and `m_j(x)=1` with `i != j`
then `j notin C_i`. Consequently the marker function is invariant under the flip,
`m(tau(x)) = m(x)` pointwise, which is why `tau` is an involution.

**Proof.** Suppose `m_i = 1`, so `x_{i-1}=1, x_{i+1}=1, x_{i±2}=x_{i±3}=0`. Test a marker at `i+d`,
`1 <= d <= 4`:
- `d=1`: marker at `i+1` needs `x_{(i+1)-1}=x_i` free but `x_{(i+1)-3}=x_{i-2}=0` (ok) and
  `x_{(i+1)-1..}` pattern `001` forces `x_{i}=1` and the left cell `x_{i-1}` is not read; the binding
  clash is `x_{(i+1)+1}=x_{i+2}=0`, but `R` needs it `=1`. Contradiction.
- `d=2`: needs `x_{(i+2)-1}=x_{i+1}` as the `1` of `001`, ok, but `x_{(i+2)-3}=x_{i-1}=1` while `L`
  needs `0`. Contradiction.
- `d=3`: needs `x_{(i+3)-3}=x_i` as first `0`, `x_{(i+3)-1}=x_{i+2}=0` as the `1` of `001`, but `R`
  gave `x_{i+2}=0`. Contradiction.
- `d=4`: needs `x_{(i+4)-3}=x_{i+1}=0` (first `0` of `001`) while `R` gave `x_{i+1}=1`. Contradiction.
By the left-right symmetry of the pattern the same rules out `d=-1,...,-4`. So two markers are at
distance `>= 5`, and every `j in C_i` has `|j-i| <= 3 < 5`, hence `j` is not a marker. Flipping the
marker cells therefore changes no cell of any `C_i`, so every `m_i` keeps its value; the flip set is
fixed and `tau^2 = id`.

**Use.** This is a *Boolean* fact. Formally (in the free ring `F_2[X]`) the substitution
`x_j -> x_j + m_j` still perturbs `m_i` whenever `C_i` meets a distance-`<=3` window, so the one-ancilla
Bennett word has a formally nonzero, Boolean-vanishing residue; see
`one-ancilla-marker-residue-is-supported-on-window-overlaps`.

## Attempts

- Distances `d = 5,6,7` between markers are realizable (e.g. `d=5` with overlapping zero-runs), so the
  bound `>= 5` is sharp; the windows `C_i, C_{i+5}` share cells `i+2,i+3`, which is where the formal
  residue concentrates.
- Verification requested from w3-vf-nonlinear.
