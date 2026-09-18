---
rg: 2
id: subexponential-schreier-growth-excludes-sl3z-and-bs1k
kind: claim
title: A group with a faithful action of subexponential orbit growth contains no SL_3(Z) and no BS(1,k), and subquadratic orbit growth also excludes H_3(Z); so no topological full group of a Z^d-action contains SL_3(Z), and Salo's full-shift host in 2V contains no H_3(Z)
distinct_from:
  heisenberg-in-nv-forces-drift-free-central-element: that uses the offset cocycle of nV and invariant measures; this uses only the cardinality of Schreier balls of an arbitrary faithful action and applies to hosts outside nV.
  heisenberg-group-lies-in-no-z-subshift-elementary-group: that excludes H_3(Z) from elementary matrix groups over crossed-product rings by linear-algebraic undistortion; this excludes H_3(Z), BS(1,k) and SL_3(Z) from topological full groups of Z^d-actions by counting orbit points.
  leavitt-unit-group-has-no-integer-heisenberg-subgroup: that targets the binary Leavitt unit group through depth growth of units; this is a pigeonhole bound for the Schreier balls of any faithful action.
  full-shift-topological-full-group-embeds-in-2v: that embeds Salo's host [[{0,1}^Z]] in 2V; this shows that host cannot carry H_3(Z), SL_3(Z) or GL_3(Z).
artifacts:
  - experiments/gl-n-z-2v-orbit-growth-2026-09-17/sl3z_root_distortion_words.py
  - experiments/gl-n-z-2v-orbit-growth-2026-09-17/output.txt
---

**ESTABLISHED** by `subexponential-schreier-growth-excludes-sl3z-and-bs1k-proof`
(direct elementary proof, 2026-09-17, unreviewed by a verifier lane).

**Setting.** Let a group `G` act faithfully on a set `X`. For a finite
`S ⊂ G`, write `|g|_S` for word length in `S ∪ S^-1` (infinite if
`g ∉ ⟨S⟩`), `B_S(x, R) = {w·x : |w|_S <= R}`, and
`γ_S(R) = sup_{x ∈ X} |B_S(x, R)|`. Say the action has **subexponential orbit
growth** if `(1/R) log γ_S(R) → 0` for every finite `S`, and **subquadratic
orbit growth** if `γ_S(R)/R^2 → 0` along some sequence `R → ∞` for every
finite `S`.

**Theorem.**

1. *(Orbit pigeonhole.)* If `g ∈ ⟨S⟩` has infinite order and
   `R_M = max_{0<=j<=M} |g^j|_S`, then `γ_S(R_M) >= M + 1` for every `M >= 1`.
2. *(Distortion inputs.)*
   - In `SL_3(Z)`, with `D = diag(1, A)`, `A = [[2,1],[1,1]]` and root elements
     `x_12, x_13, x_23`, one has `|x_13^N| <= 3 log_φ |N| + 9` for `N ≠ 0`.
   - In `BS(1,k) = ⟨x, t | t x t^-1 = x^k⟩` with `|k| >= 2`,
     `|x^N| <= (|k| + 1)(log_{|k|} |N| + 3)`.
   - In `H_3(Z) = ⟨a, b⟩` with `c = [a, b]` central,
     `|c^N| <= 12 sqrt|N| + 12`.
3. *(Exclusion.)* If the action has subexponential orbit growth, `G` contains
   no `SL_d(Z)` or `GL_d(Z)` with `d >= 3` and no `BS(1,k)` with `|k| >= 2`.
   If it has subquadratic orbit growth, `G` also contains no `H_3(Z)`.
   More generally, a linear lower bound `max_{j<=M} |g^j| >= cM` (from linear
   orbit growth) forces every infinite-order `g` to be undistorted.
4. *(Hosts.)* Let `T` be an action of `Z^d` on a compact space `X`, and let
   `[[X, T]]` be the group of homeomorphisms `f` with `f(x) = T^{c_f(x)} x` for a
   continuous `c_f : X → Z^d`. Its action on `X` has orbit growth at most
   `(2K_S R + 1)^d`. Hence `[[X, T]]` contains no `SL_3(Z)`, no `GL_d(Z)` with
   `d >= 3`, and no `BS(1,k)` with `|k| >= 2`. For `d = 1` it contains no
   `H_3(Z)`.

**Consequence for the 2V program.** Salo's host `[[{0,1}^Z]]` sits in `2V`
(`full-shift-topological-full-group-embeds-in-2v`) and contains every RAAG
(`every-raag-embeds-in-full-shift-topological-full-group`). By item 4 it
contains no `H_3(Z)`, so no `GL_n(Z)` or `SL_n(Z)` with `n >= 3`. The same holds
for any host built as the topological full group of a `Z^d`-subshift, for any
`d`. The RAAG technique therefore cannot be pushed to
`every-gl-n-z-embeds-in-2v`. A host for `SL_3(Z)` needs exponential orbit growth
on every faithful invariant set. For `H_3(Z)` it needs at least quadratic growth.

**Where every member of the class dies.** Take the orbit of the distorted
element: `x_13` for `SL_3(Z)`, `x` for `BS(1,k)`, `c` for `H_3(Z)`. Some point
has more than `M` distinct orbit points. All of them lie in a Schreier ball of
radius `O(log M)` (respectively `O(sqrt M)`), which has at most
`exp(o(log M))` (respectively `o(M)`) points.

**Survivors.** The reversible Turing machine groups `RTM(n,k) ≤ mV` of
Callard–Salo (`brin-thompson-mv-contains-a-distortion-element`) rewrite tape
cells, so their orbit growth is exponential and item 4 does not apply. That is
consistent with their `O(log^4 N)` distortion element.

**Calibration.** The script in `artifacts` verifies the `SL_3(Z)` words
`[w_N, x_23] = x_13^N` exactly for `1 <= N <= 20000` and for three random `N`
of 30, 60 and 120 digits, where `|w_N| / ln N` stays below 12. It also checks
`c^{m^2} = [a^m, b^m]`.
