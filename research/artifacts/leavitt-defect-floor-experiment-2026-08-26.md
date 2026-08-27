# Numerical defect floor of the truncated binary-Leavitt Steinberg relations (2026-08-26)

Script: `leavitt_defect_floor2.py` (scratchpad; run on MSI sioux/acn112,
CPU torch 2.x, L-BFGS with strong-Wolfe line search, 300 iterations).

## Setup

Vocabulary `V_2 = { s_u t_v : |u|+|v| <= 2 }` (17 monomials of
`L_(F_2)(1,2)`), generators `X_ij(m)` for the six root positions of `St_3`
and `m in V_2` (102 unitaries of size `d`).  Relator families, all
vocabulary-closed (3528 relators):

* F1 involution `X^2=1`; F2 same-root commuting; F3 Leavitt fold
  `X_ij(s_u t_v)=X_ij(s_u0 t_v0)X_ij(s_u1 t_v1)`; F4 disjoint-root
  commuting; F5 Heisenberg `[X_ij(m),X_jk(m')]=X_ik(mm')` whenever `mm'`
  lies in `V_2` or is zero (products of length `>2` impose nothing).

The mark `X_02(1)` is pinned to `diag(+1^(d-k),-1^k)`, `k=frac*d`.  The
loss is the sum of normalised Hilbert--Schmidt defects `||w-1||_2^2/d`;
per-family operator-norm defects and all normalised traces are reported.
Initialisation: every free generator at a random involution
`exp(i*pi*P)`, `P` a random projection of rank about `d/2`, plus noise.

## Results

| d | frac | seeds | final loss | traces of all free generators | defect location |
|---|---|---|---|---|---|
| 4 | 1/2 | 0 | 16.000 | all `1` | 8 relators with RHS = mark |
| 16 | 1/2 | 0,1,2 | 16.000 | all `1` | same 8 relators, op-norm 2 each |
| 16 | 1/4 | 0,1,2 | 8.000 | all `1` | same |
| 32 | 1/2 | 0,1,2 | 16.000 | all `1` | same |
| 32 | 1/4 | 0,1,2 | 8.000 | all `1` | same |
| 64 | 1/2 | 0,1,2 | 16.000 | all `1` | same (about 4 min per run) |
| 64 | 1/4 | 0,1,2 | 8.000 | all `1` | same |

The loss values are exactly `8 * ||Z-1||_2^2/d = 8 * 4k/d`: every run
converges to the **trivial representation** with the pinned mark left
alone, and the entire defect sits on the seven Heisenberg relators
`[X_01(t_v),X_12(s_v)]=X_02(1)` (`|v|<=2`) and the fold
`X_02(1)=X_02(e_00)X_02(e_11)`.  Families F1, F2, F4 and the remaining F5
relators are satisfied exactly.

## Reading

1. **The sterile basin is the global attractor at these sizes.**  Any
   configuration realising the mark relators needs, on the mark's `-1`
   eigenspace, a Pauli-type representation of the Heisenberg pairing
   between the seven commuting `X_01(t_v)` and the seven commuting
   `X_12(s_v)`; the constrained part of that pairing has `F_2`-rank at
   least 3--4 once the prefix-related pairs are included, so the `-1`
   space needs dimension `>= 8--16` and `d >= 32--64` at `frac=1/2`, with
   all six root positions imposing the same simultaneously.  Random
   involution starts are nowhere near such configurations and L-BFGS
   descends to the trivial representation in about two minutes.
2. **Blind optimisation is not a viable probe of the endpoint.**  The
   nontrivial approximants, if they exist at a given radius, form a
   measure-zero target; the experiment measures the optimiser, not the
   defect floor.  A useful experiment must start from constructed exact
   representations of the finite vertex groups (the six ordered
   unipotent radicals of `steinberg-group-is-glued-over-the-permutohedron`)
   and optimise only the gauges, i.e. measure hexagon holonomy directly.
3. **Even that is expected to be uninformative at feasible radius.**  The
   radius-`r` hexagon colimit is strictly freer than `St_3(R)` (missing
   relators between center-type and side-type occurrences), so exact
   finite models with a nontrivial mark plausibly exist for small `r`,
   matching the finite-window model fences already in the graph; the
   obstruction is asymptotic in the radius and no effective bound is
   known, which is exactly the content of the open leaf
   `leavitt-regular-character-is-not-mf`.
4. The truncated group `Gamma_2` is perfect (every generator is a
   commutator of two generators via `1=t_0s_0`, `s_0=1*s_0`, etc.), so it
   has no nilpotent quotients and its class-2 quotient kills the mark;
   finite quotients, if any, are perfect and a search for them by
   coset/quotient algorithms is not feasible at this presentation size.

Resource note: six concurrent runs at 8 threads each, about 2--3 minutes
per run up to `d=32`; no job left running.

## Radius-one hexagon smoke test and scope correction

The follow-up `hexagon_holonomy.py` probe was audited before use.  Its first
version accidentally called a span enumerator on all `32` values of a map
from `F_2^5`, causing a `2^32` loop.  Replacing that line by the set of the
already-enumerated image values removed the stall.  A bounded MSI smoke test

```text
python3 hexagon_holonomy.py 1 0 20
```

then returned

```text
loss0 = 1.9949
loss  = 1.8191103630525847
operator-norm defect = 1.9999999020060122
time = 49.3 seconds.
```

This is optimizer calibration only, not a lower bound: L-BFGS is nonconvex
and twenty iterations do not exhaust the gauge space.

More importantly, the probe does **not** use the regular local Heisenberg
packet.  Its center has dimension `16`, but the code retains only one
central-character extension for each of `32` coarse characters, and only a
`32`-dimensional diagonal selection in each chosen sector.  Thus its total
dimension is `1024`.  The regular packet uses all `2^16` central characters
and has dimension `2^10` in every central sector.  Multiplicity `m` merely
duplicates the thin packet, and the code never checks survival of the marked
root.  Therefore neither success nor failure of this optimization decides
`leavitt-regular-character-is-not-mf`; the exact fence is recorded in
`radius-one-hexagon-probe-omits-regular-packet`.
