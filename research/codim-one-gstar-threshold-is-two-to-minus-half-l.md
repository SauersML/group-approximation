---
rg: 2
id: codim-one-gstar-threshold-is-two-to-minus-half-l
kind: claim
title: The Grassmann statement GStar_n of the list-star node has bias threshold of order 2^(-l/2), not 2^(-l) -- at n = l+1 it holds for every gamma above delta(l) <= (2/3) 2^(-l/2) with the full list of functionals (twisted planes are triangles of a rainbow graph, capped spectrally), while for every n >= l+1 and every list size an APN-Sidon clique gives violators at gamma = (1/16 - o(1)) 2^(-l/2) (at least 2^(-l/2)/43 for l >= 8)
distinct_from:
  list-star-coherent-selector-witnesses-put-np-in-rp: that states GStar_n and leaves it OPEN; this settles its codimension-one case n = l+1 up to a constant factor in the bias threshold and gives violators for every n.
  dkkms-list-seed-needs-lists-exponential-in-l: that is a lower bound on list SIZE for the list-seed condition; this is a lower bound on the BIAS below which GStar_n fails for every list size, including the full list of all functionals.
  constant-bias-selectors-need-seed-dishonest-witnesses: that loses kappa = 1/(2^l - 1) from fibre separation; this shows the image-determined 50 percent statement cannot lose less than order 2^(-l/2), which is much larger than kappa.
artifacts:
  - experiments/ugc-gstar-rainbow-2026-09-17/check_codim1_gstar_threshold.py
---

**ESTABLISHED.** Route: `codim-one-gstar-threshold-is-two-to-minus-half-l-proof`
(a complete direct proof, `requires: []`). Unconditional: no complexity
assumption enters.

## The statement it is about

(GStar_n) is stated in `list-star-coherent-selector-witnesses-put-np-in-rp`.
Let `F` assign to every subspace `S <= F_2^n` of dimension `l-1` or `l` a
linear functional `F(S)` on `S`. Let `W` be a uniform `(l-1)`-space and `u`
uniform in `F_2^n`. Put

```text
val(F)    := Pr[ u notin W, F(W+u)|_W = F(W) ]
D_Psi(F)  := E_W min_(psi in Psi) Pr_u[ u notin W, F(W+u)|_W = F(W), F(W+u)(u) != psi(u) ]
D(F)      := D_Psi(F) for Psi = all 2^n functionals of F_2^n   (the best list)
```

GStar_n(gamma, gamma') asks: every `F` with `val(F) >= 1/2 + gamma` has a
list `Psi` of at most `L_max` functionals with `D_Psi(F) <= gamma - gamma'`.
Call `F` a **violator at gamma** if `val(F) >= 1/2 + gamma` and
`D(F) >= gamma`. A violator at `gamma` refutes GStar_n(gamma, gamma') for
every `gamma' > 0` and every `L_max`, because `D_Psi >= D` for every list.

## Statements

Write `d := l + 1`, `m := 2^d - 1` and `N := m(m-1)/6`, the number of
2-dimensional subspaces of `F_2^d`.

**Dictionary (n = l+1).** Identify a functional on `S` with a coset of
`S^perp`. A hyperplane `S = nu^perp` then carries an edge
`e_nu = {x, x + nu}` of the complete graph on `F_2^d`, of *colour* `nu`. So `F`
restricted to hyperplanes is a *rainbow graph* `G_F`: exactly one edge of each
nonzero colour. An `(l-1)`-space `W = P^perp` corresponds to a line `P` (a
2-dimensional subspace) and carries a coset `C_W` of `P`. With
`s(W) := #{ nu in P \ 0 : e_nu lies in C_W }`,

```text
val(F) = sum_W s(W) / (4N),        D(F) = #{ W : s(W) = 3 and e_a, e_b, e_(a+b) form a triangle } / (4N).
```

**Theorem A (spectral cap, n = l+1).** For every `F`,

```text
D(F)  <=  T(G_F)/(4N)  <=  delta(l) := (sqrt2/2) (2^(l+1) - 1)^(1/2) / (2^(l+1) - 2)  <=  (2/3) 2^(-l/2),
```

where `T` counts triangles, and `delta(l) ~ 2^(-l/2)/2`. Hence, whenever
`L_max >= 2^(l+1)`, GStar_(l+1)(gamma, gamma - delta(l)) holds for every
`gamma > delta(l)`, with `Psi` equal to all functionals. The hypothesis on
`val` is not even used.

**Theorem B (Sidon violators, n = l+1).** Let `l >= 4` and
`sigma := floor(2^(l/2))`. The APN graph `{(x, x^3)}` of `F_(2^h)^2`, with
`h = floor(d/2)`, is a Sidon set containing `0` of size `2^h >= sigma` in
`F_2^d`. Take any Sidon set `S'` of size `sigma` with `0 in S'`. Let `G` be
the complete graph on `S'` together with the edges `{0, z}` for every colour
`z` not of the form `a + b` with `a, b in S'`. Then `G` is rainbow. Let `F`
be its table, with `F(W)` the `P`-coset holding the most edges of `P`'s
colours. This `F` is a violator at

```text
gamma_B(l) := 3 C(sigma,3) / (4 C(m,2)),       2^(-l/2)/32 <= gamma_B(l)   (l >= 8),     gamma_B(l) 2^(l/2) -> 1/16.
```

So `gamma_B(l) > 2^(1-l)` for every `l >= 12`. Optimising `|S'|` exactly
gives violators above `2^(1-l)` already at `l = 9` and at every `l >= 11`
(table below).

**Theorem C (every n).** Let `n >= l+1` and let `F0` be any table at
dimension `l+1`. Take `phi : F_2^n -> F_2^(l+1)` onto, with kernel `K`. Put
`F(S) := F0(phi S) o phi` if `S meets K` only in `0`, and `F(S) := 0`
otherwise, and do the same for `W`. Then, with
`p := Pr[W meets K only in 0] = prod_(i=0)^(l-2) (1 - 2^(i-l-1))/(1 - 2^(i-n)) >= 3/4`,

```text
val(F) - 1/2  >=  p (val(F0) - 1/2),        D(F)  >=  p D(F0).
```

So a violator at `gamma` in dimension `l+1` lifts to a violator at
`(3/4) gamma` in every dimension `n >= l+1`. Hence, for every `n >= l+1`,
every `l >= 8` and every list size, GStar_n(gamma, gamma') fails for all
`gamma <= (3/4) gamma_B(l)`, which is at least `2^(-l/2)/43`, and all
`gamma' > 0`.

**Corollary (threshold).** The codimension-one bias threshold

```text
gamma*_(l+1) := sup{ gamma : a violator at gamma exists in dimension l+1 }
```

satisfies `2^(-l/2)/32 <= gamma*_(l+1) <= (2/3) 2^(-l/2)` for `l >= 8`. For
every `n`, the threshold `gamma*_n` is at least `2^(-l/2)/43`.

## Why twisted planes are triangles

At a line `P = {a, b, a+b}`, two edges of distinct colours in `P` meet exactly
when they lie in the same `P`-coset. Inside a 4-point coset every colour-`a`
edge meets every colour-`b` edge. So meeting is an equivalence relation on the
three edges `e_a, e_b, e_(a+b)`, and a line has 0, 1 or 3 meeting pairs. It is
of one of four types:

| type | edges of `P` | best `s(W)` | min cost at `W` |
|---|---|---|---|
| FT | a triangle | 3 | 1/4 (literal units) |
| FU | a star | 3 | 0 |
| t | exactly one meeting pair | 2 | 0 |
| s1 | pairwise disjoint | 1 | 0 |

Only a satisfied triangle costs anything. Every triangle of `G_F` is the FT
line of its three colours. So `D` counts triangles of a graph with `m` edges,
which is at most `(sqrt2/3) m^(3/2)` because `6T = tr A^3 <= lambda_max * 2m`
and `lambda_max <= sqrt(2m)`. The value, however, counts meeting pairs:
`sum_W s = N + 2f + t` and `sum_v C(deg v, 2) = 3f + t`, where `f` is the
number of full lines (FT or FU). One vertex of degree about `(3/4) 2^d` already
gives value above `1/2`. A Sidon clique of size about `2^(d/2)`, attached at
that vertex, adds `C(sigma,3) = Theta(2^(3d/2))` satisfied triangles. That is
`Theta(2^(-d/2))` of the `Theta(2^(2d))` lines, which is where `2^(-l/2)`
comes from.

## What it does (impact types 3 and 4)

* **It changes what is believed.** The live expectation (from
  swarm-0917-w14-w14-ugc-pull) was that GStar violators exist only at bias
  `O(2^(-l))`, like the kappa loss `1/(2^l - 1)` of fibre separation and the
  star-list mass `2^(1-l)` of every recorded mixture. That is false in every
  dimension `n >= l+1`, by Theorems B and C. The true codimension-one
  threshold is `Theta(2^(-l/2))`.
* **Class killed.** Any proof of GStar_n, or of the image-determined
  (Star-List), that loses only `gamma - gamma' = O(2^(-l))` is dead, whatever
  the list size. This includes fibre-collision counting in the style of
  Lemma F (loss `kappa`) and rank counts in the style of LS\* (loss
  `2^(1-l)`). The invariant that kills them is the triangle density of the
  rainbow graph that `F` induces on hyperplanes. Every such proof must pay at
  least `2^(-l/2)/43`.
* **Case closed.** At `n = l+1` with the full list (`L_max >= 2^(l+1)`),
  GStar holds with `gamma' = gamma - delta(l)`. For the DKKMS regime of the
  constant-bias cell (constant `gamma`, large `l`), the codimension-one
  instance of GStar is therefore true, with loss `O(2^(-l/2))`.
* **What is left.** For `n >= l+2` only the lower bound is known. An upper
  bound `D <= C 2^(-l/2)` for every `n` would settle GStar_n up to constants.
  It is recorded under Attempts in the list-star node.

This neither proves nor refutes UGC.

## Checks

`experiments/ugc-gstar-rainbow-2026-09-17/check_codim1_gstar_threshold.py`
runs in about a minute and exits 0.

* **Part A.** Brute force of the primal definitions of `val` and `D`, with `u`
  uniform, every subspace and every functional `psi`, on 160 random tables at
  `(n, l) = (3,2), (4,3)`. It matches the dictionary exactly, as fractions.
* **Part B.** The triangle cap, exhaustively over all 16384 rainbow graphs at
  `d = 3` (max `T = 4`, `D = 1/7`) and by annealing at `d = 4..7`. It also
  checks the identity `sum_v C(deg v, 2) = 3f + t`.
* **Part C.** Exact line-type counts of the Sidon construction by a
  Walsh-Hadamard autocorrelation, checked against brute force for `d <= 9`.
  It verifies Sidon-ness of the APN graph, the inequality of Theorem B for
  `l = 4..199`, and `gamma_B(l) 2^(l/2) >= 1/32` on `l = 8..199` (minimum
  0.0500).
* **Part D.** The K4 example at `d = 3`: `val = 1/2 + 1/7`, `D = 1/7`.
* **Part E.** Primal brute force of the lift at `(n, l) = (4,2), (5,2),
  (5,3), (6,3)`. It checks the formula for `p` and both inequalities of
  Theorem C.

Best exact Sidon violators at `n = l+1` (`sigma*` optimal over prefixes of the
APN graph; `delta(l)` is the cap of Theorem A):

| l | sigma* | gamma* | gamma* 2^(l/2) | gamma* / 2^(1-l) | delta(l) |
|---|---|---|---|---|---|
| 5 | 8 | 2.15e-2 | 0.122 | 0.34 | 9.05e-2 |
| 7 | 15 | 1.05e-2 | 0.119 | 0.67 | 4.45e-2 |
| 9 | 28 | 4.70e-3 | 0.106 | 1.20 | 2.21e-2 |
| 10 | 32 | 1.78e-3 | 0.057 | 0.91 | 1.56e-2 |
| 11 | 55 | 2.35e-3 | 0.106 | 2.40 | 1.11e-2 |
| 13 | 108 | 1.14e-3 | 0.103 | 4.67 | 5.52e-3 |
| 15 | 215 | 5.70e-4 | 0.103 | 9.35 | 2.76e-3 |
| 17 | 420 | 2.68e-4 | 0.097 | 17.5 | 1.38e-3 |
| 19 | 840 | 1.34e-4 | 0.097 | 35.2 | 6.91e-4 |

Odd `l` (even `d`) does better because the APN graph then fills `F_2^d`. The
ratio to `2^(1-l)` doubles every two steps of `l`.

## Not covered

* An upper bound on `D` for `n >= l+2`. In the dual picture, `F` puts an
  affine flat of dimension `e := n - l` on each `e`-space and a flat of
  dimension `e+1` on each `(e+1)`-space. A costly `W` needs a twisted family
  of chosen flats inside one `(e+1)`-flat. For `e = 1` the minimal twisted
  families are exactly triangles. For `e >= 2` larger circuits can occur, and
  the spectral count of Theorem A does not see them. This is heuristic and
  unproved.
* Lists shorter than `2^(l+1)` at `n = l+1`. Theorem A uses the full list.
* Normalisations other than the literal one of GStar_n, for example one that
  counts the event `u in W` as satisfied. At `n = l+1` that event has
  probability `1/4`, and such a variant is not treated here. At `n >> l` it
  has probability `2^(l-1-n)`, and Theorem C covers every `n`.
