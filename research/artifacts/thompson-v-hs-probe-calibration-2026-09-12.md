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

Results pending: jobs `q34-v-models-hop-planted` and `q34-v-models-hop-V` (`hop_hs.py`,
`eps = 0.7`, 40 hops, `d = 6, 12, 24`, 3 seeds). This section will be filled when they finish.

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
