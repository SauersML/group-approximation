# Row 29 of the length-15 residue: Magnus subgroup overgroups and metabelian covers

Lane `solve-one-relator-magnus`, 2026-09-13.

**Input.** The last uncertified class of the length-15 unpeelable residue,
`G = <a,t | AAttATaTAttaaTT>`, level exponent sums `[-3, 1, 1]`, Alexander polynomial
`Delta(s) = -3 + s + s^2`. The other 29 classes are residually finite by the census
certificates (`research/artifacts/or-length15-residue-2026-09-13.md`).

## 1. Normal form

`residue-output.txt` (line 36) gives the Magnus sequence
`[(0,-2), (2,-1), (1,1), (0,-1), (2,2)]`, that is
`W_0 = a_0^(-2) a_2^(-1) a_1 a_0^(-1) a_2^2`. Solving for `a_1`:

    a_1 = v^(-1),   v = x^(-1) y^2 x^(-2) y^(-1),   x = a_0,  y = a_2,

so `G = <x, y, t | x^t = v^(-1), (v^(-1))^t = y>` (script convention), an HNN
extension of `F(x,y)` along `F_- = <x, v>` and `F_+ = <v, y>`, which meet in `<v>`.

## 2. No intermediate rank-two overgroups (claim landed)

`row29-magnus-subgroups-have-no-intermediate-rank-two-overgroups`: the only rank-two
subgroups of `F(x,y)` containing `F_-` (resp. `F_+`) are `F_-` (resp. `F_+`) and
`F(x,y)`. Proof by Stallings folding plus enumeration of all vertex partitions of the
core graphs (15 and 52). Scripts: `one-relator-magnus-row29-scripts/algext.py`,
output `algext.out` (MSI run; calibration on `<x^2,y^2>` reports the expected three
overgroups).

Consequence: the envelope shape recorded in Attempt 5 of
`unpeelable-extreme-one-relator-groups-sofic` (a cyclic splitting of `F(x,y)` whose
rank-two vertex group properly contains a Magnus subgroup) does not exist for row 29.
The amenable-envelope route can only start from `F_-` or `F_+` being itself a vertex
group of a cyclic splitting of `F(x,y)`; that case is not decided here.

## 3. Metabelian covers

The exhaustive transitive-action search of the census stalled at index 13. Here the
covers are chosen from the Alexander module `M = Z[s^(+-1)]/(Delta)` instead:
affine actions `a : x -> x + 1`, `t : x -> r x` on `Z/n` (`n = p, p^2, p^3`) with `r`
such that the relator acts trivially; affine actions on `F_(p^2) = F_p[theta]/(Delta)`
for `p` with `Delta` irreducible; and products of these with `chi mod m`, `m <= 6`.
Potentials in the collapse search are sampled instead of enumerated. Any `CERT` line is
re-checked by the census verifier `verify.py`. Script `vfib_targeted.py`, job file
`row29-targeted.sbatch` (MSI job 707787). Results are recorded in §4 when the job
finishes.

## 4. Search results, version 1 (job 707787, cancelled)

**Calibration failed, so version 1 negatives say nothing about collapse.** On row 23
(`AAttAATTAtAtaTT`, census certificate at index 10) version 1 found no certificate.
Its index-10 cover `Z/5 r=2 x chi mod 2` has 49 characters and 29 monic ones, but the
potentials were sampled (`pot = 0` plus 60 random vectors) instead of enumerated over
all `3^9`. The census certificate uses one specific potential vector, so the miss is
expected. Output: `one-relator-magnus-row29-scripts/cal23-v1.out`.

**What version 1 does show for row 29.** The job was cancelled after 46 of 70
candidate covers (degrees 3–61). All 46 have `b_1(H) = 1`, a single character up to
sign, and an Alexander polynomial with a non-unit end coefficient under `vfib.py`'s
`alexander()`. A free kernel along that character would force unit end coefficients,
so under that filter none of these 46 subgroups is free-by-cyclic in any direction.
This depends on the `alexander()` implementation, which was not re-derived here, so it
is recorded as a computed filter result, not as a claim. Output:
`one-relator-magnus-row29-scripts/row29-v1-partial.out`.

## 5. Version 2 and calibration (job 709467)

`vfib_targeted2.py` enumerates all potentials in `{-R..R}^(k-1)` when there are at most
60000 of them, exactly as `vfib.py` does. Above that it runs greedy local search on the
cell height spans from random starts. Calibration mode (`calcert`, job file
`cal2.sbatch`) takes the census cover of row 23 directly. It reports whether that cover
is among the affine candidates, then reruns the character loop with the normal
potential rule and with the heuristic forced. Row 29 is to be rerun with version 2 only
after this calibration recovers the known certificate.

**Calibration result (job 709467, log `one-relator-magnus-row29-scripts/cal2.709467.log`).**
- The census index-10 cover of row 23 (`b_1(H) = 2`, 8 characters, 2 monic) is **not**
  among the affine metabelian candidates (`in_affine_candidates=False`). So the version 1
  miss came first from the cover set, and only second from potential sampling.
- On that cover both potential rules recover the certificate: exhaustive (`normal`), and
  local search with enumeration switched off (`heuristic`). `verify.py` confirms it:
  `AAttAATTAtAtaTT VERIFIED k=10 S=6 fibre=F_21`.
- Consequence: fibring certificates do not sit in the affine covers coming from the
  Alexander module, so a metabelian-cover search is a weak test for row 29. Row 29 is
  rerun over all transitive actions (`vfib_allreps.py`), with the calibrated potential
  rule.
