# Exact exterior screen of single Thompson transporters for the rank-32 comparison

Date: 2026-09-12 (fork `kaplansky-df`). All computations ran on MSI through the
shared Leavitt checker. Tool:
`experiments/nonsofic-certificates/kaplansky-df/boundary_exterior_screen.py`.
No counterexample is claimed. A kernel vector is an exact certificate; the
absence of a kernel on a finite window proves nothing.

## 1. What is tested

`Q = L_(F_2)(1,2)^x`, `S = F_2[Q]`. The chart `K = <g, u g u^-1> ~= GL_2(F_4)` acts on the
leaves `(000,001 | 010,011)`, with the rank-32 projectors `f_0, P_0` of the
half-corner artifact. For a Thompson unit `h` the candidate is

```text
Z_h = P_0 [h] f_0,
```

and the question is whether some `L in S` has `L Z_h = f_0`. The target is
`half-corner-chart-comparison-exists`, reduced form.

`B` is the boundary module on the points `w.T`, for one fixed generic 160-bit
tail `T`. A group element acts through its prefix table. `Lambda^k B` carries the
diagonal action, and a group-algebra element acts by summing. If `v != 0` lies in
the `f_0`-sector `f_0 Lambda^k B` and `Z_h v = 0`, then `L Z_h v = 0` while
`f_0 v = v`. So no left inverse exists, at any support of `L`.

The `f_0`-sector is spanned inside the window of points `leaf.w.T`, with `leaf` one
of the four chart leaves and `w` of length `m`. Kernel vectors are found by exact
Gaussian elimination over `F_2`. The kernels reported for `phi`, a dressed `phi`
and `phi + mu` were recomputed independently in the checker's dual mode, which
recomputes every product by prefix tables. Each gave `f_0 v = v != 0` and
`Z v = 0`.

## 2. Sanity data reproduced

`|K| = 180`, `|[K,K]| = 60`. Supports: `f_+ : 30`, `P : 70`, `E : 132`, `f_0 : 56`,
`P_0 : 72`, matching the half-corner certificate. `f_0` and `P_0` are idempotent.
`f_0` kills the natural boundary module (degree 1), as predicted: `f_0` acts as zero
on the natural block and on trivial coordinates. On the window `m = 2`, the
degree-2 sector ranks are `f_0 : 32` and `P_0 : 12`.

The explicit fusion transporter `phi = sigma mu lambda sigma` conjugates the torus
representative `T0 = diag(G, G^2)` exactly to `T1 = diag(I_2, G^2)`. Here `sigma` swaps
`010, 011`, `lambda` swaps the second and third letters under `0`, and `mu` sends
`0 -> 01`, `10 -> 00`, `11 -> 1`.

## 3. Results (window m = 2)

* `Z_phi`, `Z_(phi^-1)`, `Z_mu`, four coefficient-dressed `P_0 c [phi] d f_0` with random
  five-term chart coefficients, and the sums `phi + phi^-1` and `phi + mu` all have
  exact degree-2 kernels.
* All 551 nontrivial Thompson units with complete prefix codes of size at most
  four were screened. 359 have exact degree-2 kernels on this window. The
  degree-3 screen on the same window kills 48 of the remaining 192, leaving 144.
* Among the survivors, those whose inverse carries the four chart leaves to
  cones of one common length need no screen. The reason is not a direct appeal
  to `chart-comparison-must-fuse-torus-classes`: the actor group `<K, h>` of
  `Z_h` need not be finite. Write `Z_h = [h] P_0^h f_0` with
  `P_0^h = [h^-1] P_0 [h]`. A left inverse `L` of `Z_h` makes `L [h]` a left
  inverse of `P_0^h f_0`, which lies in `F_2[K']` for `K' = <K, h^-1 K h>`. With
  uniform depth `d`, `h^-1 K h` acts as `GL_2(F_4)` on the four image cones of
  length `d`, so both charts act by `F_2`-matrices at depth `D = max(3, d)` and
  `K'` is finite. Conditional expectation onto `F_2[K']` (Theorem 1 of the torus
  fusion artifact, applied inside `K'`) and equal regular ranks `32 [K' : K]`
  make `f_0` and `P_0^h` Murray--von Neumann equivalent in `F_2[K']`. So they
  have equal ranks on every `F_2[K']`-module. On the span of the points `p.T`
  with `|p| = D`, `K` acts by natural blocks plus trivial coordinates, where
  `f_0` has rank `0`, while `h^-1 K h` has at least one natural block, where
  `P_0^h` has positive rank. This is a contradiction.
  (Corrected 2026-09-12 by independent re-derivation; the screened conclusion
  is unchanged.)

## 4. Rescreen of nonuniform survivors

Fork `kdf-leavitt-certificate`, 2026-09-12. MSI job 505753 (msismall, 45 s) ran
the tool at commit `8a3807d14` with `--window 3 --rescreen` on the 144 survivors
of Section 3.

* **Classification of the 144.**
  * 8 are uniform on the chart, dead by the uniform-depth argument of Section 3.
  * 24 are non-nesting, including the 8 uniform ones, dead by
    `non-nesting-transporters-cannot-install-chart-comparison`.
  * 120 nest with, or split, a chart leaf.
* **Window `m = 3`, degree 2.** The `f_0`-sector has rank 128 and the `P_0`-sector
  rank 56. None of the 120 nesting transporters has a kernel, so all 120
  survive. The controls reproduce: `Z_phi`, `Z_(phi^-1)`, `Z_mu`, the four dressed
  `phi` and both sums have kernels. `Z_(mu lambda)` has none on this window.
* **The nesting survivors fall into five domain codes:**
  `0 10 110 111` (12 range permutations), `0 100 101 11` (12), `00 01 10 11` (24),
  `00 010 011 1` (36) and `000 001 01 1` (36). The full list is in the run output
  `/projects/standard/hsiehph/sauer354/kdf-leavitt/runs/rescreen_w3_d2.json`.
* **Structural filter.** By `sofic-support-cannot-install-half-corner-comparison`,
  a survivor can install the comparison only if `<K, h>` is nonsofic. Any
  survivor with `<K, h>` finite, amenable or residually finite is dead, whatever
  the screen says.

Pending: degree 3 on window 3 for the 120 (job 506462), and a group-order test of
`<K, h>`. This section is updated when those finish.
