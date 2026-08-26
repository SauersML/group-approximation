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
