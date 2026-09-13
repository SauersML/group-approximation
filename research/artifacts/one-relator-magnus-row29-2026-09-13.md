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

## 4. Search results

Pending MSI job 707787.
