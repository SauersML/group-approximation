---
rg: 2
id: fpbs-boundary-cocycle-heights-markov-rare-proof
kind: route
title: Proof that boundary cocycle heights are Markov-rare, with the growth cap, the bound on fibre-uniform heights and the decay of fibre-uniform concatenation
target: fpbs-boundary-cocycle-heights-markov-rare
requires:
  - fpbs-boundary-tilted-susceptibility-kernel
artifacts:
  - experiments/boundary-cocycle-markov-2026-09-17/check_cocycle_markov.py
  - experiments/boundary-cocycle-markov-2026-09-17/check_cocycle_markov.out
---

We work on the conull `Gamma`-invariant set of item 1 of
`fpbs-boundary-tilted-susceptibility-kernel-proof`. On that set the cocycle
identity, diagonal invariance and `Delta > 0` hold for all tuples at once. We use
only two facts from there:

- **(N)** the normalisation `int Delta_zeta(o,y) d nu(zeta) = nu_y(Z) = 1`;
- **(Co)** `Delta_zeta(o,xy) = Delta_zeta(o,x) Delta_(x^(-1) zeta)(o,y)`. This is
  the cocycle identity `Delta_zeta(o,xy) = Delta_zeta(o,x) Delta_zeta(x,xy)`
  combined with diagonal invariance `Delta_zeta(x,xy) = Delta_(x^(-1) zeta)(o,y)`.

**Item 1.** Let `A = {Delta(o,y) >= M}`. Then
`1 >= nu_y(A) = int_A Delta(o,y) d nu >= M nu(A)`.

**Item 2.** Fix `epsilon > 0` and put `t_n = (log gr + 2 epsilon) n`. The union
bound and item 1 give

```text
nu( max_(y in B_n) Delta(o,y) >= e^(t_n) ) <= |B_n| e^(-t_n) <= C_epsilon e^(-epsilon n),
```

because `|B_n| <= C_epsilon e^((log gr + epsilon) n)`. The right side is
summable. By Borel–Cantelli, for a.e. `zeta` we have
`max_(B_n) Delta_zeta(o,.) < e^(t_n)` for all large `n`. So
`h_nu(zeta) <= log gr + 2 epsilon`. Take `epsilon = 1/j` and intersect over `j`.

*Sharpness.* Item 5 of the tilt proof gives `h_nu = log(d-1)` for the visual
measure on `T_d`, and `gr(T_d) = d-1`. Part 1(d) of the artifact prints the
union-bound ratio `|B_n|/(d-1)^n`. It stays bounded, near `d/(d-2)`, so the
cap is attained up to constants.

*Rate comparison.* Item 3 of the tilt claim gives `gamma >= h/2`, and
`h <= log gr`. So [BT] can certify at most `(log gr)/2`.

**Item 3.** By item 1, `delta <= nu(Delta(o,y) >= e^(H(y))) <= e^(-H(y))`.

For the comparability form, (N) gives `1 >= int Delta(o,y) d nu >= delta D(y)/C`,
so `D(y) <= C/delta`. Since `Gamma` is countable, `Delta_zeta(o,y) <= D(y)`
holds for all `y` simultaneously off a null set. There
`max_(B_n) Delta_zeta(o,.) <= C/delta` for every `n`, so `h_nu(zeta) = 0`.

**Item 4.** Let `R` be the range of the selection. If `R` is infinite there is
nothing to prove. Otherwise
`E ⊆ union_(y in R) {Delta(o,y) >= e^s}`, and item 1 gives
`nu(E) <= |R| e^(-s)`.

**Item 5.** Let `F` be the set of `zeta` with `w_(j-1)^(-1) zeta in E_j` for all
`j`. Iterating (Co) gives
`Delta_zeta(o,w_j) = Delta_zeta(o,w_(j-1)) Delta_(w_(j-1)^(-1) zeta)(o,y_j)`.
So on `F`,

```text
Delta_zeta(o,w_k) = prod_(j=1)^k Delta_(w_(j-1)^(-1) zeta)(o,y_j) >= exp(s_1 + ... + s_k).
```

Item 1 applied to `y = w_k` gives `nu(F) <= exp(-(s_1+...+s_k))`.

**The kill.** A fibre-uniform transfer needs a `zeta`-independent height `H`,
valid on a `delta`-fraction of fibres, whose layers `{H >= n}` are nonempty for
unboundedly many `n`. This is what the deterministic modular height supplies in
the nonunimodular case, where `Delta(o,.)` is unbounded above. Item 3 forbids
it for `n > log(1/delta)`. A concatenation of `k` steps of height `n`, each
valid on a fixed fraction, has joint fraction at most `e^(-kn)` by item 5. So
supermultiplicativity with constants independent of `k` fails.

Nothing here uses amenability. Items 1–5 hold on `T_d`, where [BT] is true
(item 5 of the tilt claim). So the obstruction is to the method, not to the
statement.

**Non-uniform version (what survives).** For `x in L_n(zeta)` and
`z in L_m(x^(-1) zeta)`, (Co) gives `xz in L_(n+m)(zeta)`. The layer sets
therefore concatenate exactly, for every fibre, provided the vertex `x` is
allowed to depend on `zeta`. By item 4 such a dependence must range over at
least `nu(E) e^n` vertices. This escape is not closed here.

**Artifact.** `check_cocycle_markov.py` has two parts.

- Part 1 verifies (N), item 1 and item 3 exactly in rationals for the visual
  measure on `T_3`, `T_4` and `T_5` with `|y| <= 12`. It finds
  `max_M M nu(Delta >= M) = (d-1)/d < 1`.
- Part 2 verifies (N) and item 1 by quadrature for the Cauchy law with the
  affine maps of item 6 of the tilt proof.

The output is in `check_cocycle_markov.out`.
