---
rg: 2
id: zn-rips-top-shell-formula-link-collapse-proof
kind: route
title: Exhaustive link checks show which witnesses certify the top shell, and that the formula witness has a bad point no state lets it remove first
target: zn-rips-top-shell-formula-link-collapse
requires: [zn-rips-top-shell-sign-hull-certificates, z8-rips-scale-11-reduces-to-top-shell-link-collapses]
artifacts: [experiments/zn-rips-top-shell-formula-2026-09-19/README.md, experiments/zn-rips-top-shell-formula-2026-09-19/results.txt, experiments/zn-rips-top-shell-formula-2026-09-19/prefix_avoids_T.py, experiments/zn-rips-top-shell-formula-2026-09-19/ex66.out, experiments/zn-rips-top-shell-formula-2026-09-19/tools/kzc1.cpp, experiments/zn-rips-top-shell-formula-2026-09-19/tools/udom11.cpp, experiments/zn-rips-top-shell-formula-2026-09-19/tools/shdom.cpp, experiments/zn-rips-top-shell-formula-2026-09-19/tools/shdomw.cpp, experiments/zn-rips-top-shell-formula-2026-09-19/tools/ex66.py]
---

Notation is that of the target. All programs, inputs and outputs are in
`experiments/zn-rips-top-shell-formula-2026-09-19/` (below: `X/`). `X/results.txt` has every run with its totals.
Every program enumerates `Lmax_k`, `N(u)` and the bad sets directly from the definitions and checks every condition
with explicit `d_1` distances. No step uses symmetry.

## 1. Formula lines in order (Claim 1)

`X/tools/gen.py k r desc|asc` writes `Lmax_k` and the lines `K u | e_{j(u)} + e_k` for all `u ∈ Z_0`, sorted by
decreasing or increasing `j(u)`. `X/tools/kzc1.cpp` is the (K)/(D) replayer of
`z8-rips-scale-11-reduces-to-top-shell-link-collapses`. It applies the lines one at a time from `C = Lmax_k`. For
each (K) line it collapses `N(u) ∩ C`, removing at each step any point `b` that has a `v` as in the (K) move (§1
of `z8-rips-contractible-at-scale-8-proof`), until the link is a cone on `w`. It then re-checks the cone by
explicit distances. All 16 runs (8 scales, 2 orders) end with `ACCEPT`.

## 2. The obstruction (Claim 2)

*The example.* `k = r = 6`, `u = (2,1,1,1,1,0)`, `w = e_5 + e_6`, `b = (2,1,1,1,0,0)`. Here `b ≻ 0`,
`|b| = 5 ≤ r − 1`, `d(b,u) = 1` and `d(b,w) = 5 + 2 = 7 > 6`. So `b ∈ Bad(u,w)`, and `b ∉ Z_0`.

Let `C ⊇ Lmax ∖ Z_0` contain `u`, and put `S = N(u) ∩ C`, `S' = (N(u) ∩ Lmax) ∖ (Z_0 ∪ {u})`. Then
`S' ⊆ S ⊆ N(u) ∩ Lmax`. A first removal of `b` needs `v ∈ S`, `v ≠ b`, `v ∈ hull(0,u,b,E)` and
`N[b] ∩ S ⊆ N[v]`. The last condition implies `N[b] ∩ S' ⊆ N[v]`.

The box `hull(0,u,b,E) = [0,2] × [0,1]^5` has 96 points. Of these, 91 lie in `N(u) ∩ Lmax` and differ from `b`.
For each of the 91, `X/tools/ex66.py` prints a point `z ∈ S'` with `d(z,b) ≤ 6` and `d(z,v) = 7` (`X/ex66.out`).
For example, `v = (0,0,0,0,1,0)` is blocked by `z = (2,1,1,1,0,1)`. So no candidate works, in any such state
`C`. ∎

*The counts.* `X/tools/udom11.cpp k r ufile` runs the same test for every `u` in the file and every
`b ∈ Bad(u, w_f(u)) ∖ Z_0`. Candidates `v` range over all of `N(u) ∩ Lmax ∩ hull(0,u,b,E)`, including `Z_0`.
Blockers range over `S' ∩ N[b]`. A reported `FAIL` is exactly the situation of the example.
- At `(6, 6)` over all 985 points of `Z_0`: 32 FAILs, in 32 distinct `u`.
- At `(7, 7)`: 1,648 FAILs in 370 distinct `u`. The run was stopped after the 3,196th of the 5,418 points.
- At `(7, 8)`: 978 FAILs in 210 distinct `u`, on the 480-point subset `X/inputs/Zs-7-8.txt` of `Z_0`. There `udom9` finds 1,392 formula
  pairs with no order-free step, in 288 distinct `u`. The run was stopped after the 357th point.
- At `(8, 11)`, for `u = (-2,2,2,-1,2,1,1,0)` (`X/inputs/Tone.txt`, a point of `T`): there are 9,036 bad points outside
  `Z_0`, of which 948 are unbalanced, and 12 FAILs, for example `b = (-3,1,2,-1,2,1,0,0)`.

Since the test is monotone in `C` (more points in `C` only add blockers), the counts are lower bounds.

*Why the class order is irrelevant.* The states `C` above range over everything between `Lmax ∖ Z_0` and `Lmax`.
So the failure persists whichever points of `Z_0 ⊇ T` were deleted before `u`. §1 succeeds only because `kzc1`
first removes other bad points of the same link, and those removals change `N[b] ∩ S`.

## 3. Certificates (Claims 3 and 4)

`X/tools/shdomw.cpp k r ufile` tries, for each `u`, the witnesses `w ∈ hull(0,u,E) ∩ Lmax` with `w ≠ u`,
`d(u,w) ≤ r`, `|w| ≤ WMAX` and `w ∉ F`. It orders them with the argmax witness first. For each witness it enumerates
`Bad(u,w)` in full, including the points of `F`. For each bad `b` it searches `v` in
`b + {δ : |δ| ≤ 2, δ_k ∈ {0,1}}`, then in the whole box `hull(0,u,b,E)`. Each candidate is tested for:
- `v ≠ u, b`;
- `v ∈ Lmax ∖ F`;
- `d(v,w) ≤ r`;
- `v ∈ hull(0,u,b,E)`;
- `v ∈ sh{0,u,b}`, by all `2^k` sign vectors.

These are exactly the conditions of an `F`-certificate. The box search is complete, so a failing witness has
a bad point with no valid `v`. `F = Z_0` by default; `TOPF=1` gives `F = Top`. `ONLYUNB=1` skips balanced `u`
(Claim 3 of the sign-hull node).

- **`Z_0`.** All of `Z_0` (from `X/tools/zgen.py`) was run with `WMAX = 3` at every `(k,r)` of Claim 3. At `(7, 7)`
  this leaves 388 failures. These were rerun at `WMAX = 6` (`X/inputs/Z77f3.txt`), which leaves 88. The last 88
  were run at `WMAX = 7 = r` (`X/inputs/Z77f6.txt`), and all 88 pass.
- **`Top ∖ Z_0`.** The unbalanced points of `Top ∖ Z_0` (from `X/tools/tgen.py`) were run with `TOPF=1` and
  `WMAX = 3`. The only failures at `r ≤ 7`, `k ≤ 6` are 12 points at `(6, 6)` (`X/inputs/Tf66.txt`). All 12 pass
  at `WMAX = 5 = r − 1`.
- **`(7, 7)`, Claim 3′.** With `TOPF=1`, `WMAX = 3`, 1,520 of the 4,816 unbalanced points fail (`X/inputs/Tf77.txt`).
  Rerun at `WMAX = 6 = r − 1`, 824 still fail (`X/inputs/Tf77f6.txt`), all with `x_7 = 1`. For `F = Top` a witness
  has norm at most `r − 1`, so at this `WMAX` the witness range is complete, and the box search for `v` is
  complete too. So these 824 points have no `Top`-certificate. `TOPF=2` gives `F = { x ∈ Top : x_7 ≤ 1 }`, which
  only enlarges the allowed `w` and `v`. Rerun with it at `WMAX = 6`, all 824 still fail.
- **Argmax.** `X/tools/shdom.cpp` is the same test with only the argmax witness. Its totals are Claim 4.

## 4. The case `(8, 11)` (Claim 5)

- *`T ⊆ Z_0`.* Every one of the 53,312 lines of `sets/T-8-11.txt.gz` has norm 11 and last coordinate 0.
- *Prefix and tail avoid `T`.* `X/prefix_avoids_T.py` reads that node's `sets/T-8-11.txt.gz`,
  `certs/d-prefix-8-11.txt.gz` (843,210 lines) and `certs/d-tail-8-11.txt.gz` (346,389 lines). It finds no line
  whose deleted point or witness lies in `T`. The input hashes are in `X/results.txt`.
- *The sample.* `X/inputs/T60u.txt` is the unbalanced part (59 points) of the 60-point sample `X/inputs/T60.txt` of `T`. `shdomw 8 11` with
  `WMAX = 4` certifies all 59 points, with witness norms 2, 3 and 4. The point `(-2,2,2,-1,2,1,1,0)`
  (`X/inputs/Tone.txt`) has 40 bad points with no order-free step under the formula witness (`udom9`: a step `v ∉ Z_0`
  with `d(v,w) ≤ r` that dominates `N[b]` in `N(u) ∩ Lmax`). Under the argmax witness it has 6 such bad points
  (`udom10`).

Claim 5 then follows from Claim 2 and §7 of `zn-rips-top-shell-sign-hull-certificates-proof`.

## 5. The consequences

Claim 6 of `zn-rips-top-shell-sign-hull-certificates` needs, for each level `k = 2, …, n`:
- (a) for the unbalanced points of `Z_0`;
- (b) for the unbalanced points of `Top ∖ Z_0`.

§3 supplies both at every `(k, r)` with `2 ≤ k ≤ r ≤ 6`, and with `k ≤ 6`, `r = 7`. Here `k = 2` is included:
`Z_0 = {r e_1}`, and every point of `Top ∖ Z_0` is balanced. This gives the first consequence. The second is
§§1–2. The third is §3, the `(7, 7)` bullet, together with Claim 5. ∎
