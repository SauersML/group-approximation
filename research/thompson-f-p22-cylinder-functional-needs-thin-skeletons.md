---
rg: 2
id: thompson-f-p22-cylinder-functional-needs-thin-skeletons
kind: claim
title: The doubling ratio of Guba's monomial sets is the infimum of an exactly computable Boltzmann-cylinder functional, and generic refinement of that functional stalls far above the optimum carried by thin families
distinct_from:
  thompson-f-monomial-doubling-ratio-is-a-finite-computation: that computes the exact expansion ratio in each fixed degree D; this computes a different, degree-free functional on cylinder partitions of the critical Boltzmann local limit, whose values are asymptotic ratios of explicit families and already lie below every exact degree-12 value.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills automaton-computed lower bounds for expansion; this concerns upper bounds for the doubling ratio, meaning candidate cardinality certificates for P_(2,2), not proofs of expansion.
  thompson-f-p21-cardinality-certificate-in-degree-eleven: that exhibits one finite certificate for P_(2,1); this gives degree-free asymptotic certificates (27/14 < 2 already with 64 cells for S_(2,4)) and measures how slowly generic refinement moves for S_(3,5).
  thompson-f-cardinality-certificates-need-tower-degree: that bounds the degree of cardinality certificates for large d; this is a d = 2 computation where no degree bound is available, and its obstruction concerns the refinement strategy, not the degree.
artifacts:
  - experiments/thompson-f-p22-2026-09-17/tuples_model.py
  - experiments/thompson-f-p22-2026-09-17/local_limit.py
  - experiments/thompson-f-p22-2026-09-17/adaptive_limit.py
  - experiments/thompson-f-p22-2026-09-17/cells.cpp
  - experiments/thompson-f-p22-2026-09-17/vine_partition.py
  - experiments/thompson-f-p22-2026-09-17/show_optimal.py
---

**OPEN** (computation done; the reduction and completeness argument below are written as a proof sketch, with
no route node and no independent review; no priority claimed).

Let `M` be the positive monoid of `F`. Let `S = S_(m+1,m+d+1)` be Guba's set of normal forms
`x_(i_1) ... x_(i_d)` with `i_t <= m + t - 1`. Put `n = m + d + 1` and `k = m + 1`, and
`h(S) = inf { |S Y| / |Y| : Y ⊆ M finite, nonempty }`. The special cases are:
- `S_(3,5)`, the nine monomials of `P_(2,2)`, is `S(5 -> 3)`;
- `S_(2,4)` is `S(4 -> 2)`;
- `X_m = {x_0, ..., x_m}` is `S(m+2 -> m+1)`.

Guba's cardinality method solves `P_(2,2)` exactly when `h(S_(3,5)) < 2`
(`thompson-f-nonamenable-iff-some-monomial-set-doubles`).

## Statement

1. **Tuple reduction.** In the forest model, `s Y` adds the `d` carets of `s` on top of the roots of `y`.
   So every `s ∈ S` is one of the ways to add `d` carets to roots `0..n-1` leaving `k` roots, and it does
   not change the tail `(t_n, t_(n+1), ...)`. Hence `h(S) = inf |S A| / |A|` over finite nonempty
   `A ⊆ T^n`, where `T` is the set of finite binary trees and `S` acts as these `T^n -> T^k` maps.
   This is checked against normal-form multiplication in `tuples_model.py`.
2. **Cylinder functional.** A *cell* is an `n`-tuple of partial trees built from leaves, carets,
   `*` (an arbitrary finite tree) and exactly one `G` (a subtree holding more than half of all carets).
   A cell has mass `4^(-carets) 2^(#*)`. A finite refinement tree of cells (`* -> leaf | (*,*)`,
   `G -> (G,*) | (*,G)`) is a partition `P`. Image cells (`k`-tuples) are refined on demand until every
   split of an image cell lands in a single cell of `P`. Then
   `R(P) = min over nonempty unions A of cells of 4^d μ_k(S A) / μ_n(A)`.
   This is an exact rational, computed by min cut plus Dinkelbach iteration.
   - Claim: `h(S) <= R(P)` for every `P`.
   - Sketch: let `A_N` be the tuples with `N` carets whose top structure lies in `A`. Catalan
     asymptotics `C_(N-j)/C_N -> 4^(-j)` and `Σ_c C_c 4^(-c) = 2` give `|A_N| ~ μ_n(A) C_N` and
     `|S A_N| ~ μ_k(S A) C_(N+d)`. Tuples near the giant threshold, and giant vertices both of whose
     children are small, have vanishing density. Domination holds because the giant keeps at least
     `N/2` carets.
3. **Completeness.** `inf_P R(P) = h(S)`.
   - Sketch: `h(S)` is an infimum over homogeneous `A ⊆ T^n_D`. Replace the last leaf of the last entry
     of every `a ∈ A` by `G`. The splits do not move leaves, so `S(A^G) = (S A)^G`.
   - The cells `a^G` occur in some finite partition and have equal mass `4^(-D)`. Their images have
     mass `4^(-D-d)`, so `R(P) <= |S A| / |A|`.
   - So the one-giant regime cannot be killed as a class: `R(P) < 2` for one finite `P` is a certificate
     for `P_(2,2)`.
4. **Computed values.** These are exact rationals from `adaptive_limit.py` and `cells.cpp`. The two
   programs agree on every S_(2,4) round they share, including cell counts.

   | set | exact `Λ(12)` (finite computation) | best `R(P)` | cells | image cells |
   |---|---|---|---|---|
   | `S_(3,5)` | 2.667568 | `20143/8698 ≈ 2.315820` | 3802 | 19,121,603 |
   | `S_(2,4)` | 1.947612 | `74363/40802 ≈ 1.822533` | 34459 | 5,248,569 |
   | `X_2` | 1.478234 | `151/105 ≈ 1.438095` (uniform depth 2) | | |

   **`S_(3,5)`**, neighbour refinement (`cells 5 3 1 6`):

   | cells | `R(P)` |
   |---|---|
   | 160 | `349/148 ≈ 2.358108` |
   | 286 | `2.351211` |
   | 526 | `2.340229` |
   | 996 | `2.335784` |
   | 1929 | `2.322272` |
   | 3802 | `2.315820` |

   Image cells grow roughly like cells^1.5. The next round ran out of memory with 15 GB.

   **`S_(2,4)`**:
   - 64 cells give `27/14 < 2`, a degree-free asymptotic certificate for `P_(2,1)`.
   - 4519 cells give `1.843894`, 17493 give `1.831163` and 34459 give `1.822533`.
5. **Obstruction to generic refinement (control case `X_1`, where `h = 1`).**
   - The family `{(L_i, leaf, R_j) : i + j = D}`, with left and right vines `L` and `R`, has ratio
     `(D+2)/(D+1)`, so `h(X_1) = 1`. It has Boltzmann mass `4^(-D)`.
   - The partition that resolves only these vine cells (`vine_partition.py`) has `O(D^2)` cells and gives
     `R = (3D+7)/(3D+4)`: 13/10, 19/16, 31/28, 55/52 and 103/100 at 28, 84, 292, 1092 and 4228 cells.
   - Every generic strategy tried stalls:
     - mass-threshold partitions: 1.1909 at 12288 cells;
     - neighbour refinement: stuck at `14/11` for 13 rounds, up to 8214 cells;
     - refining the chosen cells: 1.197730 at 41844 cells;
     - caterpillar partitions of every entry: 1.157532 at 304842 cells.
   - So the optimum of the functional is carried by thin skeletons of vanishing mass, and generic
     refinement is off by orders of magnitude in cell count. Extrapolating the generic `S_(3,5)` data
     (about 0.04 gained per 24-fold increase in cells) carries no evidence about whether `h(S_(3,5)) < 2`.

## Attempts

- **Generic refinement toward `R < 2` for `S_(3,5)`.**
  - The fitted slope `d log(R-1) / d log(cells)` is about `-0.019` for S_(2,4) (64 to 34459 cells) and
    about `-0.010` for S_(3,5) (160 to 3802 cells).
  - Taken at face value, pushing `R-1` for S_(3,5) from `1.316` below `1` needs more than `10^11` times
    as many cells.
  - Dies at step 5: the same strategies are also far from optimal for `X_1`, where the answer is known. The
    bottleneck is locating the thin skeleton, not the size of the computation.
- **Decomposition left open.** A cylinder certificate for `P_(2,2)` splits into two steps.
  - (i) Guess a thin skeleton family for `S_(3,5)`, the analogue of the vine pairs for `X_1`, such as
    vine or comb patterns across the five roots together with Belk–Brown-type complete layers.
  - (ii) Evaluate the partition that resolves it with `cells.cpp` or `vine_partition.py`, which optimises over
    everything around the skeleton exactly.

  Step (i) can fail on its own, since no such skeleton may exist if `F` is non-amenable. Step (ii) is a
  finite computation.
- **Linear algebra common multiples** (item (b) of the lane). Not run here. The degree-free functional
  concerns only the cardinality method.
