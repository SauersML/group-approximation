---
rg: 2
id: centralized-cyclic-distortion-hs-dehn-tracks-area
kind: claim
title: A stable letter centralizing an exponentially distorted cyclic subgroup has exponential HS-Dehn modulus at arbitrarily small defect
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
  - experiments/hs_dehn_centralizer_family.py
distinct_from:
  cyclic-character-orbit-pressure-has-vanishing-hs-gap: that shows a scalar near-model of a power relation has defect O(1/p) while a mark tends to maximal separation; this is a two-dimensional drift model in a three-generator group that realizes the full van Kampen area of a commutator family as normalized-HS defect, with defect tending to zero.
  hs-dehn-modulus-bounded-by-dehn-function: that is the upper bound by area; this is the first matching lower bound, on an explicit hyperlinear group.
---

Let

```text
Gamma = < a, t, k | t a t^(-1) = a^2,  [k, a] = 1 >,
```

the HNN extension of `BS(1,2)` by a stable letter centralizing the
exponentially distorted cyclic subgroup `<a>`.  For `n >= 1` the words

```text
w_n = [k, t^n a t^(-n)]                                          (CD1)
```

are trivial (`t^n a t^(-n) = a^(2^n)` commutes with `k`), of length `2n+4`
and area at most `2^(n+1)`.  Then for every `L > n`, in dimension `d = L+1`,
there is a unitary tuple `U_L` with

```text
Def(U_L) = |1 - e^(2 pi i / 2^L)| / sqrt(L+1)  -> 0,
||w_n(U_L) - I||_2 / Def(U_L) = |1 - e^(2 pi i 2^(n-1-L))| / |1 - e^(2 pi i / 2^L)|
                               -> 2^(n-1)   (L -> infinity).            (CD2)
```

Consequently the HS-Dehn modulus satisfies `2^(n-1) <= F_Gamma(2n+4) <=
2^(n+1)`: it is the Dehn function up to a factor four, and the supremum is
approached along tuples of defect tending to zero.  In the language of the
Kleene compiler: for any thresholds `delta, alpha`, the halting-style
soundness `Def < delta => ||w_n - I||_2 <= alpha` fails for all
`n >= log_2(alpha/delta) + O(1)`.  Runtime-dependence of the constants is
forced, not an artifact.

**The model.**  Basis `e_0, ..., e_L`, indices mod `L+1`;
`a = diag(e^(i theta_x))` with `theta_x = 2 pi 2^(-x)`; `t` the cyclic
shift `e_x -> e_(x+1)`, so `t a t^(-1) = diag(e^(i theta_(x-1)))` and
`theta_(x-1) = 2 theta_x` exactly for `x = 1..L`; the only defect of the
first relator is the wrap-around phase `theta_L` at `x = 0`.  `k` is the
rotation by `pi/4` in the plane `(e_0, e_L)`, whose `a`-phases differ by
`theta_L`, so `[k, a]` has the same tiny defect.  But `t^n a t^(-n)` carries
phases `theta_(L+1-n)` and `theta_(L-n)` on that plane, differing by
`2^(n-1) theta_L`.  The `2 x 2` computation
`||k D k^* - D||_F = |e^(i delta) - 1|` for a diagonal `D` with phase gap
`delta` gives `(CD2)`.  `experiments/hs_dehn_centralizer_family.py`
reproduces `ratio / 2^n = 0.500` to three digits for `L = 8..24`,
`n <= 12`.

**Why it matters.**  `Gamma` is hyperlinear (`amenable-edge-hnn-preserves-
hyperlinearity`, edge group `Z`) with solvable word problem, so this is no
obstruction to anything; it is a calibration.  It proves that HS defect
accumulates along a derivation exactly like area whenever the derivation
runs through an abelian (near-degenerate spectral) direction, and that the
centralizer-of-a-distorted-subgroup pattern, which is how the Boone tower
reads halting as a commutator (`boone-commutator-criterion-for-halting`),
has HS-Dehn modulus equal to its distortion when the distortion is cyclic.
Any machine group whose halting subgroup is distorted through an abelian
direction inherits this, so a length-controlled compiler must route its
distortion through rigid, non-abelian structure.

**The mechanism that evades it is the quotient, not the kernel.**  Let
`1 -> N -> G -> Q -> 1` be an Ollivier--Wise Rips triple (`G` hyperbolic,
`N` finitely generated with property (T)) and
`Gamma_Q = <G, k | [k, N] = 1>`, so `[k, u] = 1` iff `u` maps to `1` in
`Q`.  If an approximate representation restricts on `N` to an exact
representation with multiplicity spaces `M_j` over the types
`j in Irr(N)`, then (T) forces `k` to within `O(Def)` of `U(N)'`, i.e.
`k ~ sum_j 1 (x) k_j`, and the `G`-generators act on the multiplicity
bundle by unitaries `W_(g,j) : M_j -> M_(g.j)` which satisfy the relators
of `G` approximately and are trivial on the generators of `N`.  So the
`W`'s form an approximate representation of `Q` on `sum_j M_j`, and the
mark `[k, u]` is the defect of the trivial `Q`-word `u` in that
representation.  Property (T) removes the kernel's distortion completely
and hands the problem to the HS-Dehn modulus of `Q`.  This is recorded as
the live attempt on
`unsolvable-word-problem-group-with-computable-hs-dehn-modulus`: the
length-control target for `Gamma_Q` is the length-control target for `Q`.
