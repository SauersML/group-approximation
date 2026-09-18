---
rg: 2
id: general-ug-on-bm-hosts-from-group-shift-games
kind: route
title: Lift each unique game on a Bafna--Minzer host to shift games over its transitive holonomy quotients on the same loopless host, solve those by the group-shift form of Bafna--Minzer, and project back
target: general-unique-games-easy-on-globally-hypercontractive-graphs
requires:
  - unique-games-lift-to-group-shift-games-on-the-same-host
  - group-shift-games-easy-on-globally-hypercontractive-graphs
artifacts:
  - experiments/ugc-coset-lift-2026-09-17/check_coset_lift.py
---

This route is conditional: it is complete once
`group-shift-games-easy-on-globally-hypercontractive-graphs` (OPEN) is
established. The other requirement is ESTABLISHED.

**1. The hosts are loopless.** The walks of Bafna--Minzer Theorems 1.6--1.8
never stay put:

* `J(n, l, alpha l)` joins two `l`-sets that differ in exactly `alpha l`
  elements, with `alpha > 0`;
* `Grass(n, l)` joins `L, L'` with `dim(L cap L') = l - 1` (Bafna--Minzer
  Section 5.2), so `L != L'`;
* the depth-`alpha` canonical walk on `X(l)` changes exactly `alpha l` vertices
  of the face.

So `lambda(U) = 0` for every unique game `U` on these hosts, and item 3 of the
lift gives `max_i val(L_i) >= val(U)/k!`.

**2. Lift.** Given `U` with alphabet `k` and `val(U) >= c` on such a host,
compute the lifts `L_1, ..., L_t` (lift item 4, polynomial time for fixed
`k`). Each `L_i` is a left-shift game over a transitive group `H_i` of degree
`<= k`, so `|H_i| <= k!`, on the same host with the same weights. Some `L_i`
has value `>= c/k!`.

**3. Solve.** Run the group-shift algorithm of the required claim with
completeness `c/k!` on each `L_i`. On the good `i`, it returns a labeling of
value `>= delta(alpha, c/k!)`, in time `n^D` with
`D = l^(poly(k! l^(k!/c)))`.

**4. Project.** Lift item 1 turns each output into a labeling of `U` of at
least the same value. Keep the best one. Its value is at least
`min_A delta_A(alpha, c/k!) > 0`, where the minimum is over the finitely many
transitive groups of degree `<= k`. This is lift item 5, (b) implies (a),
applied to this host class.
