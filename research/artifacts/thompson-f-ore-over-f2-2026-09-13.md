# Thompson's F, Ore route over F_2: exact minimal common-multiple degrees for Guba's P_(1,2), P_(2,1), P_(2,2)

Lane `hl-thompson-f-ore`, 2026-09-13. All computation ran on MSI in `/scratch.global/sauer354/hl-thompson-f-ore/`.
Nodes:
- `thompson-f-p21-over-f2-every-pair-meets-in-degree-seven` and route `thompson-f-p21-over-f2-degree-seven-exhaustive-proof`;
- `thompson-f-p22-over-f2-exhaustive-degree-seven-census` and route `thompson-f-p22-over-f2-census-exhaustive-proof`.

## 1. What a finite computation can certify on the Ore side

By `thompson-f-amenable-iff-group-ring-is-ore`, F is amenable iff `K[F]` is Ore.
- **Counts only certify multiples.** A finite linear count `dim aV + dim bV > dim W`, with `aV, bV ⊆ W`,
  forces `aV ∩ bV ≠ 0`. It certifies a common multiple, never trivial intersection.
- **So non-Ore pairs have no such certificate.** A non-Ore pair has no finite certificate of this kind,
  and the "paradoxical dimension count" suggested for this lane points the wrong way.
- **Consistent with earlier records.** This matches the table in
  `research/artifacts/thompson-f-monomial-doubling-2026-09-13.md` §2. Finite linear algebra settles pairs
  positively, and otherwise only bounds their minimal degrees from below.

**Verbatim pins.** From Guba, arXiv:2305.07113v4, `jgcc-template.tex` (on MSI, `~/famstruct/2305_07113/`):
- Theorem `kielak`: "The group $F$ is amenable if and only if the group ring $K[F]$ over any field satisfies the Ore condition."
- Lemma `kfkm`: "For any field $K$, the group ring $K[F]$ satisfies the Ore condition if and only if the monoid ring $K[M]$ satisfies the Ore condition."
- Lemma `homogen`: "Suppose that any equation of the form $au=bv$ has a nonzero solution in $K[M]$ provided $a$, $b$ are homogeneous polynomials of the same degree. Then $K[M]$ satisfies the Ore condition."
- After Problem `P_(d,m)`: "If the Problem ${\mathcal P}_{d,m}$ has positive solution for any $d,m\ge1$ (that is, we can find nonzero solutions), then the group $F$ is amenable. If this Problem has negative solution for at least one case, then $F$ is not amenable."

Over `K = F_2`, each `P_(d,m)` is a finite set of pairs. So each instance can be settled positively by a
finite computation, and a single pair that is never settled is a non-Ore candidate.

## 2. Method

**Program.** `experiments/thompson-f/ore/ore_linalg.py`.
- **Normal forms.** `x_(i_1)...x_(i_d)` with `i_1 <= ... <= i_d`, and the rewrite `x_j x_i -> x_i x_(j+1)`
  for `i < j`.
- **The test.** For a pair `a ≠ b` of nonzero elements of `F_2[S]`, and degree `k`, let
  `V = F_2[M_(k,k+3)]`. The program decides `dim(aV + bV) < 2|V|` by incremental Gaussian elimination.
- **Why that test is exact.** Left multiplication has no kernel, because `F` is left-orderable. Both summands
  therefore have dimension `|V|`.

**Exact minimal degrees.** The inert-letter-tail step of
`thompson-f-p22-explicit-pair-degree-bound-wiedemann-proof` (Step 2) is field independent. A common
multiple of degree `D` yields one of some degree `E <= D`, supported in `M_(E, E+3)`. For `S_(2,4)` and
`X_2`, letters `<= E+2` already suffice. So the first `k` found is the exact minimal degree over `F_2`.

**Scripts** (md5):
- `ore_linalg.py`:
  - `65070f09cffdb770f7b191f282c78c3a` is the landed version. Job 738304 ran it, and so did the `S_(2,4)`
    per-pair rerun.
  - `c8d0b2a001289193a64eb269feac3c22` ran jobs 737900 and 737901.
  - `2b9b72ecad16b401e84657e946732ed0` was the first login-node calibration run.
  - The later versions add input and output options only (`PAIRS_IN`, `SHARD`, `KMIN`, and a per-pair
    `solved` list). The elimination is unchanged.
- `ore_certify.py` `bfa7a0289ff8b2fd9abaab3000f0ad73`: explicit `u, v` for a settled pair.
- `ore_verify.py` `0774d779b2d4e5d6977037aec1c7fed2`: independent checks by exact piecewise-linear maps.
- `ore_sample.py` `c14d913a27b3e50813e301c2379be87d`: a deterministic sample of settled `P_(2,2)` pairs.

## 3. Checks

**Normal forms.** `ore_verify.py nf 6 6` (job 738303) composes the standard generators as exact PL
homeomorphisms of `[0,1]`.
- **Words:** it checked all 137256 words of length `<= 6` in letters `<= 6`, plus 3000 random words of
  length 7–11.
- **What it confirmed:** each word and its normal form give the same map, and distinct normal forms give
  distinct maps (10604 maps).
- **Convention:** `rl`. Result `ALL_OK`.

**Independent census.** `experiments/thompson-f/ore_census.py` (commit fd68ee7ab, 2026-09-12), mode `p22`,
reports 126144 unsettled pairs at degree 2 and 122745 at degree 3, with letters `<= D+3`
(`ore_census_small_degrees.jsonl`). This lane's independent code gives `130305 - (357 + 3804) = 126144` and
`130305 - (357 + 3804 + 3399) = 122745`. Exact agreement.

## 4. Results

**Calibration, `X_2 = {x_0, x_1, x_2}` (`P_(1,2)`), 21 pairs.** Minimal degrees `{1: 15, 2: 6}`, consistent
with Guba's Theorem `xmy`(b), which bounds the degree by `3`.

**`S_(2,4)` (`P_(2,1)`), 465 pairs.**
- **Settled:** every pair has a common multiple over `F_2`. Minimal degrees:
  `{1: 45, 2: 138, 3: 84, 4: 90, 5: 69, 6: 27, 7: 12}`.
- **Earlier bounds:** Guba's Theorem `s24` gives `<= 41`, and the cardinality certificate
  `thompson-f-p21-cardinality-certificate-in-degree-eleven` gives `11` over every field.
- **Certificates:** `thompson-f-ore-over-f2-2026-09-13-data/s24_certs.json.gz`, uncompressed md5
  `c418bbea79e1ac2a58c2a0c806182bec`.
- **PL check:** `ore_verify.py cert` (job 738303) recomputed `a u` and `b v` for all 465 certificates by
  composing PL maps, without normal forms. Result `certificates_checked: 465, ALL_OK`.

**`S_(3,5)` (`P_(2,2)`), 130305 pairs.**
- **Per-degree counts:** `{1: 357, 2: 3804, 3: 3399, 4: 6951, 5: 5799, 6: 7629, 7: 8037}`. So 35976 pairs are
  settled.
- **Unsettled:** 94329 pairs have no common multiple of degree `<= 7`.
- **Data:** the unsettled list is `thompson-f-ore-over-f2-2026-09-13-data/s35_unsolved_after_k7.json.gz`
  (uncompressed md5 `0207160aa309848432f875ef6d7fee3a`). Pairs are bitmasks over the nine monomials in the
  order of `SETS["S35"]`: `x_0^2, x_0x_1, x_0x_2, x_0x_3, x_1^2, x_1x_2, x_1x_3, x_2^2, x_2x_3`. Summary
  file: `census_over_f2.json` (md5 `6895a5e8e420e7e51d3942f9e244dbad`).
- **Per-shard wall time (max seconds):** `k = 5`: 15.1; `k = 6`: 45.6; `k = 7`: 414.7.
- **PL spot-check (job 739191, 8 tasks, all COMPLETED exit 0):**
  - `ore_sample.py` drew a deterministic sample (seed `20260913`): 24 settled pairs of degree `<= 5`, 24 of
    degree 6 and 24 of degree 7.
  - For each pair it produced explicit `u, v` at the census degree. For the first group it used the least
    `k <= 5` that yields a certificate; those degrees came out `{2: 4, 3: 6, 4: 9, 5: 5}`.
  - `ore_verify.py cert` recomputed `a u = b v ≠ 0` for all 72 by composing PL maps, without normal forms.
    Result: `certificates_checked` totals 72, and all 8 tasks report `ALL_OK`. The largest certificate has
    1632 terms in `u` and `v` together.

**Contrast.** `P_(2,1)` is fully settled by degree 7. For `P_(2,2)`, the per-degree settled counts don't
decay through degree 7, and 72% of pairs are still unsettled.

## 5. Exact gap

- **Root:** a pair of `P_(2,2)` over `F_2` that is never settled proves `thompson-f-is-not-amenable`.
  Settling all 130305 at some degree solves `P_(2,2)` over `F_2`, which is not all fields and so doesn't
  make F amenable. No finite computation of this type can prove non-Ore.
- **Next computation:** degree 8 on the 94329 survivors means per-pair elimination with 151164 columns and
  274638 rows over `F_2`. That is beyond the Python bit-row code at this count. It needs M4RI-style dense
  `F_2` elimination, or a Wiedemann-type rank certificate as in
  `thompson-f-p22-explicit-pair-degree-bound-wiedemann-proof`, plus reduction of pairs by symmetries of the
  problem.
- **Theory:** survivors that keep resisting need an invariant ruling out common multiples in every degree.
  None is known.

## 6. Jobs

- 737900: `S_(2,4)` to degree 8.
- 737901: `S_(3,5)` to degree 5, 32 shards.
- 738303: normal-form and PL certificate verification for `S_(2,4)`.
- 738304: `S_(3,5)` degrees 6–7 on the 109995 survivors, 64 shards.
- 739191: PL spot-check of `S_(3,5)` certificates, 8 tasks: 72 certificates, all `ALL_OK` (§4).
