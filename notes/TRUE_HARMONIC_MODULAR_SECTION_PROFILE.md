# Exact full-plane modular section profiles at all cuspidal primes below 100

Date: 2026-08-11

## 1. Outcome

The selected exact correction section modulo `64` has now been exhausted on
the entire rank-two cuspidal harmonic plane at every prime level below `100`
where that plane is nonzero:

`p=53,61,79,89.`                                          `(HSP0)`

There is no bad linear combination hidden between the two basis vectors in
any of the four charts.  Exact compact screens also give

`dim_Q H_2=0 at p=73,97,`                                 `(HSP0a)`

so those originally suggested levels have no harmonic plane to profile.

For every nonzero

`(a,b) in (Z/64Z)^2`,                                      `(HSP1)`

let `c_(a,b)` be the centered compact harmonic vector and let `x_(a,b)` be
the centered correction obtained by taking the same modular combination of
the two deterministic sparse-module solutions.  Define

`R_corr(a,b)^2`
` = (||x_(a,b)||^2/N_corr)/(||c_(a,b)||^2/N_compact)`       `(HSP2)`

and, since the canonical compact and correction coordinates are disjoint,

`R_full(a,b)^2`
` = (||c_(a,b)||^2+||x_(a,b)||^2)/N_full`
`   --------------------------------------- .`              `(HSP3)`
`              ||c_(a,b)||^2/N_compact`

Exact exhaustive enumeration of all `4095` nonzero pairs gives

| level | `max R_corr` | `max R_full` | maximizing `(a,b)` |
|---:|---:|---:|---:|
| `p=53` | `0.5995627747` | `0.5478061944` | `(30,11)` |
| `p=61` | `0.5970593451` | `0.5456367818` | `(4,22)` |
| `p=79` | `0.5857626329` | `0.5357145726` | `(3,16)` |
| `p=89` | `0.5917473955` | `0.5409425563` | `(21,61)` |

The exact squared maxima are

`p=53:`
`  max R_corr^2 = 1131231/3146893,`
`  max R_full^2 = 16465846/54869395;`                       `(HSP4)`

`p=61:`
`  max R_corr^2 = 129389/362963,`
`  max R_full^2 = 17773712/59699523.`                       `(HSP5)`

`p=79:`
`  max R_corr^2 = 1982787554/5778736035,`
`  max R_full^2 = 2068060676/7206034815;`                   `(HSP5a)`

`p=89:`
`  max R_corr^2 = 187429788/535261373,`
`  max R_full^2 = 3321184328/11349864635.`                  `(HSP5b)`

Thus the worst selected correction ratio remains below `0.60` across the
complete prime-level cuspidal sample below `100`, after testing every
direction and every two-adic scale represented modulo `64`.  The largest
value occurs at the first cusp `p=53`; there is no monotone growth signal.

## 2. Exactness and scope

The profiler reconstructs the integral correction matrix and the two
integral harmonic demands, solves both congruences by exact sparse
`Z/64Z` module elimination, and verifies

`x_i A = b_i mod 64`                                      `(HSP6)`

against the original integer matrix.  Linearity then proves `(HSP6)` for
all modular combinations.  Norms are integer sums of squares, and maxima
are compared as exact rational numbers; floating-point arithmetic is used
only to print decimal square roots and distribution summaries.

This is deliberately **not** described as a minimum-norm computation.
The sparse elimination selects one deterministic modular section.  Hence
`(HSP4)--(HSP5)` are certified upper bounds for the optimal lift constants.
They do not prove that the selected witnesses are closest vectors, nor do
two levels imply a uniform family theorem.

The distinction is useful: a large selected-section norm could be a pivoting
artifact and would require a CVP or dual lower-bound audit, whereas a small
selected-section norm is already a valid constructive upper bound.  The
present experiment therefore gives genuine TRUE evidence without making a
minimum-norm claim.

## 3. Distribution, not only the maximum

The correction-ratio distributions are also nearly identical:

| level | minimum | median | 90th percentile | 99th percentile | maximum |
|---:|---:|---:|---:|---:|---:|
| `p=53` | `0.52623` | `0.55915` | `0.57452` | `0.58747` | `0.59956` |
| `p=61` | `0.52965` | `0.56407` | `0.57679` | `0.58919` | `0.59706` |
| `p=79` | `0.53867` | `0.56391` | `0.57365` | `0.58156` | `0.58576` |
| `p=89` | `0.54183` | `0.56408` | `0.57229` | `0.57943` | `0.59175` |

This rules out the most immediate failure mode of the original basis-only
experiment: none of the four planes contains a narrow direction with
rapidly larger selected lift norm.

The two-local elementary divisors are also bounded but not literally
constant.  The nonzero two-primary torsion is `C_4` at `p=53,61,89` and
`C_2` at `p=79`.  Thus the first two charts suggested the false formula
“always `C_4`”; the four-chart data instead point to the theorem-shaped
statement “two-primary exponent at most four.”

## 4. Reproducibility

The exact profiler is

`experiments/sl3_projective_harmonic_primary_section_profile.py`.

The deterministic certificates are

`experiments/projective-harmonic-primary-p53-section-profile.json`,

with SHA-256

`ac9ce19292d305f0cb619a70913e764796b49028e7c55d2108e5cc1802838015`,

and

`experiments/projective-harmonic-primary-p61-section-profile.json`,

with SHA-256

`39feddf5220db51b1e14cfcaf74cc88f6e48fd0c16189434655e1ef3a65f3768`.

The two later certificates are

`experiments/projective-harmonic-primary-p79-section-profile.json`,

with SHA-256

`d65547f5ab4c76636740e8c31fff81e1d4b1b4f6ebf1e4df1c76d48f409767ef`,

and

`experiments/projective-harmonic-primary-p89-section-profile.json`,

with SHA-256

`095d788892f78f6a8eea190b0195b3cdf839d3cf0e0a2658fd43c89223a2b5e4`.

## 5. Next theorem-shaped target

The repeated numerical constant is less important than the bounded local
module structure.  At all four cuspidal levels the correction cokernel has
two-primary exponent at most four, while the harmonic plane maps trivially
to that torsion.  The next useful family statement is therefore:

> prove from the fixed stabilizer templates that the harmonic correction
> map has uniformly bounded two-primary elementary divisors and admits a
> uniformly bounded normalized section.

The four primes in `(HSP0)` exhaust the prime cuspidal levels below `100`, as
listed by Ash--Yasaki.  Larger levels are worthwhile only as a way to expose
the finite templates behind this statement.  They are not substitutes for
the uniform proof.

Finally, this modular HAP section is only the bounded-primary transfer
layer.  The main compact harmonic obstruction is the paired-discriminant
section constant studied in
`TRUE_P53_CELLULAR_HARMONIC_DISCRIMINANT.md` and
`TRUE_P61_CELLULAR_HARMONIC_SECTION.md`.  Exact `p=79,89` computations of
that stronger invariant are separate; a flat value here cannot by itself
bound the compact discriminant geometry.
