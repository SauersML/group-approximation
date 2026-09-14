---
rg: 2
id: small-leavitt-windows-carry-no-strict-design
kind: claim
title: Seven small windows over the Leavitt unit group carry no strict design of any kind, by PSL(3,2) images of their two-rectangle table groups
distinct_from:
  small-leavitt-invariant-output-windows-have-finite-separations: that excludes invariant-output designs on 45 ball windows through images keeping x_h nontrivial; this excludes every design, whatever its alphabet and rules, on seven windows including two defect windows, through images separating all reverse products.
  leavitt-rooted-defect-window-carries-no-strict-design: that proves one of these windows dead by hand through Z * Z/2; this certifies it and six more by replayable permutation witnesses.
  two-rectangle-surjunctive-images-kill-all-designs: that is the general filter; this is its computed instance on explicit windows.
artifacts:
  - research/artifacts/gk3-leavitt-nonlinear-2026-09-14.md
  - experiments/gk3-leavitt-nonlinear/general_window_screen.py
  - experiments/gk3-leavitt-nonlinear/runs/gen.json
  - experiments/gk3-leavitt-nonlinear/runs/gapstage-791209.log
---

**ESTABLISHED** by `small-leavitt-windows-no-strict-design-proof`.

Let `G = L_(F_2)(1,2)^x`, with units in the shared checker's conventions
(`experiments/nonsofic-certificates/README.md`):

- `u = 1 + s0 t1`, `v = 1 + s1 t0`, `w = s0 t1 + s1 t0`.
- `a` is the Thompson unit replacing the prefixes `(0, 10, 11)` by `(00, 01, 1)`.
- `t = 1 + S[00]T[01]`, `q = 1 + S[1]T[01]`, `r = 1 + S[01]T[1]`.
- `l = E_01(1) = 1 + S[000]T[001]`; `cu` is the nine-leaf compressor; `c` is the `x_0` of
  Thompson's `F` on `[1000]`.
- `d = [cu c cu^-1, l]`, and `B_k(X)` is the ball of radius `k` in `X u X^-1`.

**Theorem.** For each window `(S, M)` below, every pair of automata over `G` with memory
`M`, a left inverse with memory `S`, and any finite alphabet, is surjective.

| window | `S` | `M` | reverse classes | certificate |
|---|---|---|---|---|
| control-gl2-1-1 | `B_1(u,v,w)` | `B_1(u,v,w)` | 6 | `<S u M>` finite, order 6 |
| thompson-aw-1-1 | `B_1(a,w)` | `B_1(a,w)` | 10 | PSL(3,2) images |
| thompson-aw-2-1 | `B_2(a,w)` | `B_1(a,w)` | 20 | PSL(3,2) image |
| thompson-aw-1-2 | `B_1(a,w)` | `B_2(a,w)` | 20 | PSL(3,2) image |
| transvections-1-1 | `B_1(u,v,t,q,r)` | `B_1(u,v,t,q,r)` | 23 | PSL(3,2) images |
| defect-direct-E01 | `{1, a', a'^-1, a' l}` | `{1, l, a'}` | 10 | PSL(3,2) image |
| defect-ball-1-1 | `B_1(l,cu,c)` | `B_1(l,cu,c,d)` | 30 | PSL(3,2) images |

Here `a' = cu c^-1 cu^-1`. Every window contains a letter of infinite order, except the control.
The two defect windows contain the nontrivial defect `d` or its root identification.

**Not decided within the search bounds** (GAP runs hit their 900 s limit with no witness):
- `defect-nested-E01`: `S = {1, a', a'^-1, cu, cu^-1, c, a' l}`, `M = {1, l, a', cu, c, d}`;
- `eld1-cu-1-1`: `B_1` of the six `E_ij(1)` with `cu`;
- `eld1-cu-c-1-1`: `B_1` of the six `E_ij(1)` with `cu` and `c`.

A window not decided here is a candidate for further search, not a strict pair.
