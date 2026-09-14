# Thompson's F: nonspatial witnesses and the rate of relator stability (2026-09-14)

**Verdict: not decided.** Soficity of `F` is equivalent to a vanishing ratio of relator defect to
commutator separation, so nonsoficity is one linear inequality. Unions, products and torus factors
cannot lower the ratio. Pairs on which a fixed nontrivial element of `F` nearly vanishes satisfy the
inequality with explicit linear constants. Exact enumeration and a heuristic search bound `ρ_F` from above; they
decide nothing.

Claims:
- `thompson-f-sofic-iff-defect-to-separation-ratio-vanishes` (items 1–5), with proof route;
- `thompson-f-almost-kernels-force-linear-commutator-bounds`, with proof route.

Conventions are those of `research/artifacts/thompson-f-spatial-permutation-models-2026-09-13.md`, §1:
`R_1 = bAABaaBAba`, `R_2 = bAAABaaaBAAbaa`, commutator word `abAB`. A word is a product with the last
letter acting first, and capitals are inverses. `m_1, m_2, m_c` are the numbers of points moved by
`R_1(A,B)`, `R_2(A,B)` and `A B A^-1 B^-1`. So `t = m_c/n`, `D = max(m_1,m_2)/n` and `D_+ = (m_1+m_2)/n`.

## 1. What a witness must satisfy

A witness for `thompson-f-is-sofic` in the one-commutator form is a family `(A_k, B_k)` with `D → 0`
and `t ≥ ε`. Collected from main and from this lane:
- **Regular component.** Its fixed-point character is `t τ_reg + (1-t) χ_ab` with `t ≥ ε`
  (`thompson-f-sofic-iff-relator-system-unstable`).
- **Far from spatial actions.** Every labelling by points, intervals, `k`-configurations or the Cantor set
  has following error at least `min(ε/8, ε²/(24k²))` (`thompson-f-spatial-permutation-models-almost-commute`).
- **No single F-set.** If the family follows one `F`-set with error `→ 0`, that `F`-set carries a
  mean-free amenable action (`thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived`).
- **Every element moves (new).** For every nontrivial `w`,
  `liminf d(w(A_k,B_k),1) ≥ ε/M_w`, with the constant of
  `thompson-f-almost-kernels-force-linear-commutator-bounds`. In the limit the character gives moved
  mass `≥ t` for all `g ≠ e`.
- **Only the ratio matters (new).** Any family with `D/t → 0` is a witness after coordinatewise powers.
  Neither the defect nor the following error has to tend to 0
  (`thompson-f-sofic-iff-defect-to-separation-ratio-vanishes`).

## 2. The rate criterion

`ρ_F = inf D/t` over all `n` and all pairs with `t > 0`.
- **Criterion.** `F` is sofic exactly when `ρ_F = 0`. Equivalently, `F` is not sofic exactly when
  `d(AB,BA) ≤ C max_j d(R_j(A,B),1)` for all pairs, and then the best `C` is `1/ρ_F`.
- **Mechanism.** Coordinatewise powers multiply fixed-point proportions. A pair with separation `t` and
  ratio `ρ`, raised to the power `m = ⌈K/t⌉`, has separation `≥ 1 - e^-K` and defect `≤ (K+1)ρ`.
- **Envelope.** `E(τ) = inf{D : t ≥ τ}` satisfies `ρ_F τ ≤ E(τ) ≤ ρ_F (1 + ln(1/(1-τ)))`.
- **Certificates.** Every single pair `(A,B)` with `t > 0` certifies `ρ_F ≤ D/t`. So §4 and §5 give
  checkable upper bounds on `ρ_F`, hence lower bounds `C ≥ 1/ρ` on any nonsoficity constant.
- **What changed for construction searches.** The landed exact profiles aimed at `D → 0` at fixed
  separation. The target is now the ratio at any scale. In particular a spatial model need not follow
  the true action well, provided its relator defect is small compared with its separation.

## 3. Closure: block and tensor mixing is no route

For `r ∈ (0,1]` the pairs with `D_+ ≥ r t` are closed under disjoint unions (weighted averages) and
coordinatewise products. The proof is a corner argument for a bilinear term; see the proof route, item 4.
- **Landed blocks.** `x_0`-ray windows have `D_+/t ≈ 1.98` (`M = 32`: `(0.0751+0.0769)/0.0769`),
  truncations `D_8` `≈ 1.81`, and perturbed commuting pairs `≈ 3.99`. Every union, product or torus
  factor built from them keeps `D_+ ≥ t`.
- **Not covered.** Skew products (cocycle extensions `(s,u) ↦ (As, α(s)u)`) and graph surgery that glues
  blocks along shared points. There the moved counts do not factor.

## 4. Exact small-n profile

**Method.**
- `rho.c` in `research/artifacts/hl-f-sofic-relator-instability-2026-09-14-search/`, C with OpenMP, run
  on one MSI compute node with 32 cores, as job 780822.
- `A` runs over one permutation per cycle type, since simultaneous conjugation preserves all counts, and
  `B` over all of `Sym(n)`.
- **Calibration.**
  - The independent brute force `brute.py` loops over all pairs with no reduction. At `n = 3, 4, 5` it
    reproduces the minima, and at `n = 5` the class-size-weighted totals: 13560 separating pairs, none
    with `m_1+m_2 < m_c`, 1440 with equality, and 1200 with `max < m_c`.
  - The same script checks that `R_1` and `R_2` fix every point of `D_17` for `x_0, x_1`, so they are
    the identity, while `abAB` moves 65535 of those points.

**Exact minima over all `A, B ∈ Sym(n)` with `m_c > 0`.**

| n | pairs checked | min `(m_1+m_2)/m_c` | min `max(m_1,m_2)/m_c` |
|---|---|---|---|
| 3 | 18 | 1 | 1 |
| 4 | 120 | 1 | 1 |
| 5 | 840 | 1 | 3/5 |
| 6 | 7920 | 2/3 | 1/2 |
| 7 | 75600 | 2/3 | 3/7 |
| 8 | 887040 | 2/3 | 3/7 |
| 9 | 10886400 | 4/7 | 3/7 |
| 10 | 152409600 | 1/2 | 2/5 |
| 11 | 2235340800 | 1/2 | 2/5 |
| 12 | 36883123200 | 1/2 | 1/3 |

**Certificates.** Each argmin is one pair, and every certificate is recounted by `analyze.py`.
- **Sum ratio 1/2, `n = 10`.** `A = [1,2,3,4,0,6,7,8,9,5]`, `B = [3,4,5,1,7,8,9,0,6,2]` (images of
  `0..9`), with `m_1 + m_2 = 4` and `m_c = 8`.
- **Max ratio 1/3, `n = 12`.** `A = [1,2,3,0,5,6,7,4,9,8,11,10]`, `B = [4,5,8,9,1,0,10,2,3,11,7,6]`,
  with `max(m_1,m_2) = 3` and `m_c = 9`.

So `ρ_F ≤ 1/3`, and every nonsoficity constant in the max form satisfies `C ≥ 3` (in the sum form,
`C ≥ 2`).

**Lower envelope** (`n = 12`): the least `max(m_1,m_2)` for each exact `m_c`.

| m_c | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|
| least `m_1+m_2` | 3 | 4 | 4 | 4 | 4 | 4 | 6 | 7 | 7 | 8 |
| least `max(m_1,m_2)` | 3 | 3 | 3 | 3 | 3 | 4 | 3 | 4 | 4 | 4 |

**Reading.**
- Small blocks beat every landed spatial family, whose max ratios are about 1, by a factor of 3.
- The least defect grows much more slowly than `m_c` up to `n = 12`. It is tempting to read this as a
  decreasing ratio, but at these sizes the relators of lengths 10 and 14 wrap around cycles of length
  at most 12, so coincidences dominate. Nothing here says how `ρ*(n)` behaves as `n → ∞`, and by §2
  unions and products of these blocks never do better than `1/3`.

## 5. Heuristic search for larger n

**Method.** `anneal_ratio.c`: Metropolis search on `log(max(m_1,m_2)/m_c)`. The moves compose `A` or `B`
with a random transposition, and a penalty keeps `m_c ≥ frac · n`. All runs used MSI compute nodes.
- **Calibration.** At `n = 6` all three seeds reach the exact minimum `1/2`.
- **Job 781073.** Random starts for `n = 8..128`, 3·10^6 steps, `frac ∈ {0.25, 0.5, 0.75}`, 4 seeds.
- **Job 781712.**
  - Seeded starts for `n = 16..64` with 3·10^7 steps: the exact `n = 12` block, or the best `n = 16` pair,
    padded with fixed points. Padding leaves all counts unchanged.
  - Random starts for `n = 16..32`.

**Best max ratios found.**

| n | random, 3·10^6 steps | seeded or random, 3·10^7 steps |
|---|---|---|
| 8 | 3/7 | |
| 10 | 2/5 | |
| 12 | 4/11 | |
| 16 | 1/3 | **4/13** |
| 20 | | **4/13** |
| 24 | 11/24 | 1/3 |
| 32 | 14/29 | 1/3 (seeded), 14/32 (random) |
| 48 | 27/48 | 1/3 |
| 64 | 40/64 | 1/3 |
| 96 | 74/95 | |
| 128 | 113/128 | |

**Certificate.** `cert.x16.txt` in the search directory, from run `sa.16.c16.2`, is a pair on 16 points
with `m_1 = m_2 = 4` and `m_c = 13`, recounted by `analyze.py`. So `ρ_F ≤ 4/13`, and every nonsoficity
constant in the max form is at least `13/4`.

**Reading.**
- **Coincidence pairs.** In every certificate `ab^-1`, `a^-1ba` and `a^-2ba^2` move almost every point, so
  none of them separates supports the way `x_0 x_1^-1` and `x_2`, `x_3` do in `F`. Their defects are
  small because of coincidences on short cycles, and no mechanism that scales with `n` is visible.
- **Flat above n = 20.** Seeded runs never beat the seed's `1/3`, while random starts get worse as `n`
  grows. That is search failure, not a trend, since fixed-point padding keeps `1/3` at every `n`.
- **What it shows.** It is evidence that unstructured search sits near `0.3`. It is no evidence about
  `ρ_F = 0`: a witness family would need structure that single transpositions do not find.

## 6. Construction and obstruction attempts

- **Sofic approximations of relatives of `F`.**
  - Subgroups of sofic groups are sofic, so a known sofic group containing `F` would already decide the
    question. None is known.
  - Quotient maps `G → F`, for example from `G = <a,b | R_1>`, only relocate the problem. A sofic
    approximation of `G` controls `R_1` and leaves the defect of `R_2` free, and by §2 that defect,
    compared with the separation, is the whole question.
- **Random repairs of non-amenable Schreier graphs.** Truncating a Schreier graph with Cheeger constant
  `h` leaves at least an `h` fraction of boundary points to repair. By §2 what counts is the relator
  defect the repair creates relative to the separation it keeps. The landed truncation profiles have
  `D_+/t ≈ 1.8`, and random matchings are no better. §5 tests unstructured pairs directly.
- **Obstructions.**
  - `thompson-f-almost-kernels-force-linear-commutator-bounds` proves the linear inequality on every
    class where a fixed nontrivial word is almost trivial: generators of bounded order, almost laws.
  - Spectral gap: a family with uniform spectral gap and `D → 0` has an ergodic limit action, while the
    free part and the part on which `F'` acts trivially are invariant. So the limiting separation is
    0 or 1. This is recorded as a remark and not landed. It needs the dichotomy for countably
    additive limit measures, which is proved on main only for means.

## 7. Exact gap

1. **The one number.** Decide whether `ρ_F = 0`.
   - Equivalently: are there permutation pairs whose relator defect is an arbitrarily small fraction of
     their commutator separation?
   - Nonsoficity is exactly `d(AB,BA) ≤ C max_j d(R_j(A,B),1)` for all pairs, and the certificates of §4
     force `C ≥ 3`.
2. **Shape of a positive answer.** A family with `D/t → 0` must satisfy all of these:
   - it is not a union or product of blocks with `D_+ ≥ r t`, `r ≤ 1` (§3). In particular, no union
     or product of the `n ≤ 12` blocks goes below `1/3`;
   - every fixed nontrivial word `w` moves at least a `t(1 - N_w ρ)/M_w` fraction of points
     (`thompson-f-almost-kernels-force-linear-commutator-bounds`);
   - once amplified to separation `≥ 1/2`, it is far from following any spatial action (landed bound)
     and cannot follow one `F`-set with error `→ 0` unless `F` has a mean-free amenable action.
3. **Shape of a negative answer.** A proof of nonsoficity must prove the linear inequality. So far it is
   proved only on pairs where some fixed nontrivial word nearly vanishes, and those constants are
   not computed. For spatial following models there is only the landed square-root bound, which is in
   terms of following error. No rate in terms of relator defect is proved for them.
4. **Not covered by §3.** Skew products and graph surgery, which glue blocks along shared points. These are
   the only mixing constructions left for pushing below the small-block ratios.
5. **Numerics.** Exact for `n ≤ 12`, heuristic beyond (§5). They certify upper bounds on `ρ_F` and
   decide nothing about `ρ_F = 0`.
