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
  cones of one common length need no screen. `K` and `h^-1 K h` then generate a
  finite uniform-depth group, and
  `chart-comparison-must-fuse-torus-classes` (in the special case where the
  finite image is the actor group itself) kills them. In such a group `T0` and
  `T1` have different fixed-space dimensions on the natural module.

## 4. Rescreen of nonuniform survivors

Pending: window `m = 3`, degrees 2 and 3. This section is updated when the run
finishes.
