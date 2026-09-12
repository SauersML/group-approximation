# Thompson V: calibrating the normalized-HS model probe

Date: 2026-09-12. Lane `q34-v-models`. All computation ran on MSI (msismall, one core per job),
using `experiments/thompson-v-models/{calibrate_hs.py, basin_hs.py, hop_hs.py}`.

This follows up `research/artifacts/thompson-v-model-probes-2026-09-12.md`. That probe's
normalized-HS descent on the Bleak--Quick presentation of `V` plateaued at a maximal relator
defect of about 1.15 for `d` up to 72, but it was never run on a presentation with known exact
solutions. So the plateau could not be read as evidence about `V`.

## 1. Setup: three relator sets, one optimizer

The parametrization and optimizer are exactly those of `hs_probe.py`:

- `u = W_u D6 W_u^*` and `v = W_v D3 W_v^*`, with balanced 6th and 3rd root spectra. So
  `u^6 = v^3 = 1` hold exactly, and `u^3` sits at squared energy 2;
- Riemannian gradient descent on the mean squared normalized-HS defect of the other five
  relators, from Haar-random starts.

The three relator sets are:

| set | relators | exact far-from-trivial models? |
| --- | --- | --- |
| `V` | the five Bleak--Quick words (lengths 16, 69, 31, 25, 35) | unknown; this is the question |
| `planted` | the same words raised to their orders in `S_5` | yes, at every `d = 6k` |
| `null` | random reduced words of the same lengths | none expected |

**Why the planted set has exact solutions.** Take `x` of cycle type `(2)(3)` and `y` a 3-cycle
generating `S_5`. Raise each relator word to `m_i` = order of `r_i(x,y)` in `S_5`; the powers
are `(1,2,3,3,1)` or `(1,2,3,3,3)` depending on the seed. The 6-dimensional irreducible
representation `Lambda^2(standard)` of `S_5` has character 0 on `(12)(345)` and all its powers,
and on 3-cycles, so `rho(x)` and `rho(y)` have exactly balanced spectra. Hence `rho`, and its
direct sums at `d = 6k`, solve the planted set exactly. `basin_hs.py` builds `rho` and checks the
mean squared defect: `1.2e-14`. The planted words are longer than `V`'s (total length 357 against
176), so this is a conservative control.

## 2. Descent from Haar starts: no signal distinguishes the sets

2000 iterations, 3 seeds per cell (`calibrate_hs.py`):

| d | planted: max HS defect, min mean sq | V: max HS defect, min mean sq | null: max HS defect, min mean sq |
| --- | --- | --- | --- |
| 6 | 1.15--1.31, 0.66 | 1.17--1.28, 0.62 | 1.18--1.39, 1.20 |
| 12 | 1.09--1.24, 0.62 | 1.18--1.19, 0.79 | 1.16--1.25, 1.15 |
| 24 | 1.01--1.23, 0.56 | 1.11--1.17, 0.78 | 1.14--1.19, 1.09 |
| 48 | 1.06--1.24, 0.59 | 1.13--1.15, 0.76 | 1.18--1.20, 1.17 |

- **No run solved the planted set,** even though exact solutions exist at every `d` in the table.
  Its best maximal defect is about 1.0, no better than `V`.
- **The maximal defect plateaus agree** across all three sets, at about 1.0--1.4.
- **One weak difference:** the mean squared defect of `V` (0.62--0.79) is close to the planted
  set's (0.56--0.66) and well below null (1.09--1.20). Part of this is structural: two planted
  words hold in `S_5` with power 1, and `(u^3 v)^4` is short. It is not evidence of models.

## 3. Basin of the planted solution

`basin_hs.py`: start from `W_exact * exp(eps A)` with `A` a random skew-Hermitian matrix of
operator norm 1, descend 1500 iterations, and call a run solved when the max HS defect < 0.05.
Five trials per cell.

| d | eps = 0.01 | 0.1 | 0.3 | 1 | 3 |
| --- | --- | --- | --- | --- | --- |
| 6 | 5/5 | 5/5 | 5/5 (median 0.004) | 0/5 (median 1.29) | 0/5 (median 1.28) |
| 12 | 5/5 | 5/5 | 5/5 (median 0.003) | 0/5 (median 1.25) | 0/5 (median 1.25) |

The exact solution attracts descent only from perturbations of operator norm at most about 0.3.
From norm 1 on, descent lands on the same plateau as from Haar starts.

## 4. What this shows

- **The Haar-start plateau of `hs_probe.py` carries no information about `V`.** The same
  optimizer, from the same kind of start, misses existing exact models of a longer relator set
  at every dimension probed, and lands on a plateau indistinguishable from `V`'s. The earlier
  table (`d <= 72`, plateau about 1.15) is therefore not evidence against HS models of `V` of
  small dimension. It is also not evidence for them.
- **The planted basin is narrow:** roughly an operator-norm ball of radius 0.3--1 around the
  solution. From norm 1 on, the landscape is dominated by a generic plateau near 1.25.
- **A calibrated search must first solve the planted control from generic starts.** Section 5
  reports the basin-hopping test of that.

## 5. Basin hopping

`hop_hs.py`: descend 1500 iterations from a Haar start. Then run 40 hops; each hop perturbs the
best model by `exp(0.7 A)` and re-descends 400 iterations. A run is solved when the max HS defect
drops below 0.05. Three seeds per cell.

| d | planted: solved, max HS defect, mean sq | V: solved, max HS defect, mean sq |
| --- | --- | --- |
| 6 | 0/3, 0.69--1.32, 0.24--0.42 | 0/3, 1.06--1.21, 0.61--0.68 |
| 12 | 0/3, 0.84--1.28, 0.49--0.62 | 0/3, 1.06--1.10, 0.65--0.72 |
| 24 | 0/3, 0.92--1.22, 0.55--0.65 | 0/3, 1.09--1.17, 0.74--0.83 |

- **No run solved the planted control,** so hopping at this strength is still uncalibrated.
- **Hopping lowers the planted defect** at `d = 6` (mean squared 0.66 to 0.24--0.42) but does not
  reach the basin of the exact solution.
- **`V` barely moves.** That difference is too weak to read as evidence in either direction:
  the planted words are longer, and some of them hold in `S_5` with power 1.

## 6. Permutation (Hamming) calibration

`calibrate_perm.py` uses the same annealer as `perm_probe.py`, with relators reversed to match
the matrix convention. The left regular action of `S_5` solves the planted set exactly at
`n = 120` (checked: cost 0.0). Best cost is the mean fraction of points moved by the five
relators, over 60000 annealing steps and 2 seeds per cell:

| n | planted | V | null |
| --- | --- | --- | --- |
| 120 | 0.84--0.91 | 0.57--0.58 | 0.93 |
| 240 | 0.90--0.91 | 0.72--0.73 | 0.95 |

- **The annealer never finds the exact planted permutation model.** Its cost there is close to
  the null floor.
- **`V` scores lower than both,** matching `perm_probe.py`: `(u^3 v)^4` and the length-25 relator
  are easy to satisfy exactly. This is not evidence of sofic models of `V`.
- **So the earlier permutation costs for `V`** (0.54--0.70 at `n = 36..144`) carry no information
  about soficity.

## Scope

- **No proof in either direction.** A numerical search can refute nothing and certify nothing
  here. `V` is simple, so it has no finite exact models at all, and every model is approximate.
- **The structured spatial ansätze are already fenced on main:**
  - cylinder projections in normalized trace (`thompson-v-hyperlinear`, "Models cannot be
    spatial");
  - truncations of the Cantor action in the Hamming setting
    (`thompson-v-cantor-orbits-have-no-folner-sets`);
  - covariant Cantor representations
    (`thompson-v-covariant-cantor-representations-are-not-amenable`).
  Any model must be non-spatial.
