# hl-ghb7-central-survival (2026-09-14)

**Lane goal.** Decide `ghb7-flexibly-hs-stable` for `G = G_{HB_2}(7)` in either direction, through
the refutation premise `ghb7-finite-index-z-extension-center-survives` (route
`ghb7-instability-via-visible-central-extension`) or through (HA).

**Verdict.** Not decided. The premise is reduced to an exact combinatorial statement and to degree-two
goodness. Small-quotient survival indices were computed on MSI as calibration only (section 3).

## 1. Landed reductions (c5202d522)

- `ghb7-normal-subgroup-b2-is-orbit-euler-count`: for a finite quotient `φ : G → Q` with `N = Ker φ`,
  `b_2(N;Q) = |Q|(1 − Σ_x 1/|φ<x>| + Σ_i 1/|φ X_i|) − 1`, since `b_1 = 0` by (T) and rational
  cohomology is that of the orbit complex. `K_7 = Ker(G → Z/7, a,b,c ↦ 1)` has `b_2 = 6`; the
  `(Z/7)^2` and `(Z/7)^3` kernels have `b_2 = 30` and `216`.
- `z-extension-centre-orders-are-restricted-evaluation-indices`: in a central `Z`-extension `K~`
  with class `c`, the orders of `z` in finite quotients are exactly the indices
  `e(N) = [Z : c(i_* H_2(N;Z))]` over finite-index `N <= K` (five-term sequence plus cyclic quotients
  of preimages).
- `ghb7-centre-survival-iff-unbounded-orbit-cycle-indices`: vertex groups have exponent 7 (unipotent
  in characteristic 7), so the equivariant spectral sequence has a single `d_2` of exponent 7 and
  `m_ω(N) | e(N) | 7·m_ω(N)` with `m_ω(N) = [Z : ω(p_* Z_2(N\Y;Z))]`. The premise holds iff some
  integer 2-cochain `ω` on some `K\Y`, nonzero on `Z_2(K\Y)`, has unbounded `m_ω` over finite
  quotients of `G`.

## 2. Landed goodness criterion (776aaf5b6)

- `degree-two-inflation-onto-makes-z-extension-centres-survive` (ESTABLISHED): if every class in
  `H^2(K;Z/n)` is inflated from a finite quotient, every central `Z`-extension of `K` keeps its
  centre at every order `n` in some finite quotient. Proof: reduce mod `n`, inflate the class from
  `K/N`, identify the reduced extension with the pullback of the finite extension, project.
- OPEN `ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity`, with route
  `ghb7-centre-survival-via-degree-two-goodness` into the premise and conditional route
  `ghb7-degree-two-inflation-via-hyperbolic-goodness` from `every-hyperbolic-group-is-good`.
- **Reading.** Flexible HS stability of `G` forces every finite-index subgroup with `b_2 >= 1` to fail
  degree-two goodness for some `n`. If every hyperbolic group is good, `G` is not flexibly HS stable
  and this stability route to `non-hyperlinear-group` is dead. Compare
  `hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class`, which reaches non-goodness
  from stability only under hyperlinearity.

## 3. Calibration computations (MSI)

**What is computed.** For a finite quotient `φ : G → Q` through which `G → Z/7` (`a,b,c ↦ 1`)
factors, `N = Ker φ <= K_7`. The script builds the orbit complex `N\Y` (2-cells `Q`, 1-cells `Q/<φx>`,
`∂(q) = [q<b>] + [q<c>] − [q<a>]`), an integer basis of `Z_2(N\Y)`, pushes it to
`Z_2(K_7\Y) = {sum-zero vectors in Z^7}`, and reports the elementary divisors of the quotient lattice.
For a primitive integer cochain `ω` on `K_7\Y`, `m_ω(N)` divides the largest divisor.

**Checks built in.** Every basis vector is certified to be a cycle. `rank Z_2(N\Y)` equals the Euler
count `b_2(N;Q)` of `ghb7-normal-subgroup-b2-is-orbit-euler-count`. The matrix images of `a, b, c`
satisfy all 11 CCKW relators, which calibrates the commutator convention. Exact integer arithmetic.

| quotient `Q` | `\|Q\|` | 1-cells | 0-cells | `b_2(N)` | divisors of `Z_2(K_7\Y)/p_*Z_2(N\Y)` |
|---|---|---|---|---|---|
| `Z/7`, `a,b,c ↦ 1` | 7 | 3 | 3 | 6 | `1,1,1,1,1,1` |
| `(Z/7)^2`, `a ↦ e_1`, `b ↦ e_2`, `c ↦ 4e_1+4e_2` | 49 | 21 | 3 | 30 | `1,1,1,1,7,7` |
| `(Z/7)^3` | 343 | 147 | 21 | 216 | `1,1,1,1,7,7` |
| `X_1`, `c,b` identity, `a ↦` element 1 of `X_1` | 2401 | 1029 | 345 | 1716 | `1,1,1,1,7,7` |

Run: `orbit_survival.py` (`ABELIAN_EXIT=0`) and `retraction_survival.py` on MSI, in
`/scratch.global/sauer354/hl-ghb7-central-survival/`. The retraction run hit its 3600 s timeout
(`RETRACTION_EXIT=143`) after the first retraction onto `X_1`. The remaining retractions onto `X_1`,
`X_2` and `X_0` were not computed.

**Reading.** On these 7-group quotients the survival index is at most 7 for every primitive `ω` on
`K_7\Y`, which is the exponent-7 slack of the spectral sequence, not growth. A finite list cannot
decide unboundedness; this calibrates the pipeline and shows no growth among 7-group quotients up to
order 2401.

## 4. Cairn (MSI, fresh clones in /scratch.global, python3.12, clones deleted)

- **At origin/main containing 776aaf5b6** (`ANC2_OK`):
  - `degree-two-inflation-onto-makes-z-extension-centres-survive` is ESTABLISHED via its direct proof.
  - `ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity` and
    `ghb7-finite-index-z-extension-center-survives` are OPEN, with the new routes wired as intended.
    Every leaf except `every-hyperbolic-group-is-good` shows ✓.
  - `ghb7-is-not-flexibly-hs-stable` is OPEN through `ghb7-instability-via-visible-central-extension`.
  - Full `check` exits 4 on foreign errors that were already on main; no line names this lane's ids.
- **At origin/main containing c5202d522** (`ANC1_OK`): `ghb7-normal-subgroup-b2-is-orbit-euler-count`,
  `z-extension-centre-orders-are-restricted-evaluation-indices` and
  `ghb7-centre-survival-iff-unbounded-orbit-cycle-indices` are all ESTABLISHED via their direct proofs.

## 5. Exact gap

- **Refutation:** degree-two goodness (or just unbounded cycle indices `m_ω`) for one finite-index
  subgroup of `G` with `b_2 >= 1`. No goodness theorem is known for hyperbolic Kazhdan groups, which
  admit no cocompact cubulation.
- **Stability:** (HA) for the triangle, which would force every such subgroup to be non-good in
  degree two, a profinite statement of Gromov-question strength.
- Neither computation of finitely many quotients can decide unboundedness.
