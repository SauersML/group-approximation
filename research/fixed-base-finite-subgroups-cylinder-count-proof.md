---
rg: 2
id: fixed-base-finite-subgroups-cylinder-count-proof
kind: route
title: Torsion in B fixes clopen sets, a free finite action has a clopen fundamental domain, and cylinder counts mod h-1 are B-invariant
target: fixed-base-finite-subgroups-satisfy-a-cylinder-count-congruence
requires:
  - odometer-prefix-groups-have-fg-index-kernels
artifacts: []
---

**Item 1.** Let `g^k = 1` and let `g(x) = x`. On a cylinder `vC` around `x`, `g` acts by one
piece `v y -> w a^c(y)`. Its slope `h^(|w|-|v|)` must be `1`: otherwise the `k`-th power of
this piece near `x` has slope `h^(k(|w|-|v|)) != 1`, contradicting `g^k = 1` near `x`. So
`|w| = |v|`, and `x = v y_0` fixed forces `w = v` and `a^c(y_0) = y_0`. The odometer has no
periodic points, so `c = 0`, and `g` is the identity on `vC`. Hence `Fix(g)` is open; it is
closed since `g` is continuous. `N` is dense in `X`, so a nonempty clopen fixed set meets
`N`.

**Item 2.** Let `C <= P` be finite. Its generators act on `N` as a genuine free action (the
regular action restricted to `C`), and their near classes lie in `B`. As elements of `B`
they generate a finite group acting on `X`: two elements of `B` agreeing near infinity on
`N` are equal, by faithfulness. By item 1 every nontrivial element of `C` acts on `X`
without fixed points. A free action of a finite group on a Cantor set by homeomorphisms has
a clopen fundamental domain `U`: every point has a clopen neighbourhood disjoint from its
`|C| - 1` translates, and finitely many such neighbourhoods can be refined to a disjoint
clopen transversal (textbook). So `X` is the disjoint union of `|C|` translates `cU`.
Assign to a clopen set its number of cylinders modulo `h - 1`. This is well defined, since
splitting one cylinder into its `h` children adds `h - 1`, and it is invariant under `B`:
a prefix piece maps a cylinder to a cylinder, and the odometer preserves every cylinder
`wC`. `X` has class `r`, so `r = |C| [U]` modulo `h - 1`, which forces
`gcd(|C|, h - 1) | r`.

**Item 3.** `v` is a prefix permutation of the lowest digit, so it lies in `V_(h,1)`, and it
fixes no point because `d + 1 != d mod h`. For `n = d + h y`: if `d >= 1`, then
`v^-1(n) = (d-1) + h y` and `s` returns `d + h y`; if `d = 0`, then
`v^-1(n) = (h-1) + h y` and `s` gives `h(y+1)`. So `s v^-1` is the identity off the class of
`0` mod `h` and `h y -> h(y+1)` on it, which is the local odometer `a_[0]`. Conjugating by
`v^d` moves it to the class of `d`.
