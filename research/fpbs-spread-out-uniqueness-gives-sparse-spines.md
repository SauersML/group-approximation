---
rg: 2
id: fpbs-spread-out-uniqueness-gives-sparse-spines
kind: claim
title: Site uniqueness on a spread-out Cayley graph at density p gives an FIID spine of density p plus p squared |T| L, so groups without sparse spines have p_u^site of order at least one over the square root of |T| L
artifacts:
  - experiments/fpbs-spread-out-spines-2026-09-17/compare_bounds_free_group_balls.py
  - experiments/fpbs-spread-out-spines-2026-09-17/output.txt
distinct_from:
  fpbs-bernoulli-cayley-cost-above-one-forces-nonuniqueness: its Theorem 2 transports an arbitrary spine of vertex density theta between generating sets at a cost linear in theta |T| L; here the spine is a supercritical site cluster, both ends of a transported edge must be open, and the cost is quadratic, p^2 b |T| (L-1), which is what makes the criterion and the square-root bound possible
  fpbs-sparse-spine-cost-bound: that bounds C* by the density of an FIID spine at a fixed generating set; here it is applied after a quadratic transport from a spread-out graph, giving a lower bound on p_u^site of every spread-out Cayley graph
  fpbs-fiid-soft-collapse-iff-fiid-sparse-spines: that reads spines off the critical cluster at a fixed generating set; this produces spines from the uniqueness phase of other generating sets and gives an intrinsic criterion for spines needing no subgroup structure
  fpbs-generating-set-threshold-comparison: that compares thresholds of two generating sets by a power map phi(p) on the parameter; this compares uniqueness on a spread-out graph with spine density, not thresholds with thresholds
  fpbs-no-fiid-sparse-spines-on-nonamenable-groups: that is the (refuted) root; its surviving restricted form on groups without lifting subgroups implies Corollary C here, and Corollary B is a subgroup-free way to refute it on a given group
---

**ESTABLISHED (agent-verified, not refereed).** Proof in
`fpbs-spread-out-uniqueness-gives-sparse-spines-proof`.

**Setting.**
- `Gamma` is an infinite finitely generated group and `S` a finite symmetric generating set, `d = |S| >= 3`.
- `T` is a finite symmetric subset of `Gamma \ {e}` with `T ⊂ B_S(L)`, `L >= 1`, and `Cay(Gamma,T)` connected.
- *Mixed percolation* `omega_(p,b)` on `Cay(Gamma,T)`: vertices open independently with probability `p`, edges open
  independently with probability `b`; `b = 1` is site percolation. It is *in the uniqueness phase* if a.s. there
  is exactly one infinite open cluster.
- `p_u^site(T) = inf { p : omega_(p,1) is in the uniqueness phase }`. No monotonicity of uniqueness is used.

**Theorem A (quadratic transport).** If `omega_(p,b)` on `Cay(Gamma,T)` is in the uniqueness phase, then
`Cay(Gamma,S)` carries an FIID random subgraph that is a.s. connected and infinite with

```text
P(o in V)  <=  theta_T(p,b) + p^2 b |T| (L-1)  <=  p + p^2 b |T| (L-1).
```

**Corollary B (a spine criterion without subgroups).** If there are `T_k ⊂ B_S(L_k)` and `(p_k,b_k)` in the
uniqueness phase of `Cay(Gamma,T_k)` with

```text
p_k -> 0   and   p_k^2 b_k |T_k| L_k -> 0,
```

then `Gamma` has FIID sparse spines on every Cayley graph. Hence, by the established nodes:
- `C*(Gamma) = 1` (`fpbs-sparse-spine-cost-bound`);
- `C_sub^b(S') = 1` at every `S'` and `beta_1^(2)(Gamma) = 0`
  (`fpbs-bernoulli-cayley-cost-above-one-forces-nonuniqueness`, Theorem 1);
- Corollary E of `fpbs-fiid-soft-collapse-iff-fiid-sparse-spines`: no argument that stays weakly contained in
  Bernoulli proves `p_c < p_u` on `Gamma`.

For site percolation (`b_k = 1`) the condition reads `p_u^site(T_k) = o((|T_k| L_k)^(-1/2))`.

**Corollary C (square-root obstruction).** Suppose every FIID a.s. connected infinite subgraph of `Cay(Gamma,S)` has
`P(o in V) >= eps_0 > 0`. This holds with `eps_0 = (C*(Gamma)-1)/(d/2-1)` whenever `C*(Gamma) > 1`, and it is
exactly what the surviving restricted root of `fpbs-no-fiid-sparse-spines-on-nonamenable-groups` asserts. Then, for
every `T ⊂ B_S(L)`,

```text
p_u^site(Cay(Gamma,T))  >=  min( eps_0/2 , sqrt( eps_0 / (2 |T| (L-1)) ) ),
```

and more generally `p + p^2 b |T| (L-1) >= eps_0` at every point `(p,b)` of the mixed uniqueness phase.

**Calibration D (free group balls; a computation).** `Gamma = F_2`, `S` a free basis with inverses (`d = 4`),
`C* = 2`, so `eps_0 = 1`, and `T_L = B_L \ {e}`, `|T_L| = 2·3^L - 2`.
- The path-counting spectral bound is `p_u^site(T) >= 1/(|T| rho_T)`. Here `rho_T` is the norm of the uniform
  Markov operator on `T`. It is evaluated exactly by Haagerup's ground spherical function, and cross-checked by
  maximising the sphere polynomials over the Kesten–McKay support.
- Corollary C beats that bound at every `L` from 2 to 20. The ratio of the two bounds is about 2.0 at `L = 2, 3`
  and increases from `L = 3` to 3.73 at `L = 20`. Asymptotically it is `≈ 0.79 sqrt(L)`, because
  `|T| rho_T ≍ L |T|^(1/2)` on the tree while the cost bound is `≍ (L |T|)^(-1/2)`.
- So on groups with `C* > 1`, the heuristic "`p_u` of a spread-out graph is governed by `1/(|T| rho_T)`" is off by at
  least a factor of order `sqrt(L)`. On the free group the operator norm understates the uniqueness threshold by
  at least this factor.
- In mean-degree terms, uniqueness on a `C* > 1` group needs mean open degree `p|T| ≳ (|T|/L)^(1/2)`. This is a
  square-root-of-volume law, the same law for every group with `C* > 1`, including surface groups. It was not
  compared with the hyperbolic Boolean-model literature here.

Script and output: `experiments/fpbs-spread-out-spines-2026-09-17/`.

**What this changes.**
- The surviving question for the hard core is: are there FIID sparse spines on a Tarski monster or on a free Burnside
  group? These groups are periodic, their infinite subgroups are co-amenable, and they have no infinite amenable
  subgroups. So the lift theorem and the central-`Z^2` constructions cannot start there.
- Corollary B gives the first spine criterion that needs no subgroup at all. It asks only for uniqueness of the
  radius-`L` Boolean model on `Gamma` (`T = B_S(L) \ {e}`) at mean open degree `m = p|B_L| = o((|B_L|/L)^(1/2))`.
- Corollary C says that a proof that there are no spines on such a group (which would give `p_c < p_u` there by
  Corollary D) must in particular prove a uniform spread-out nonuniqueness below mean degree `c (|B_L|/L)^(1/2)`.
- The square-root threshold is exactly where groups with `C* > 1` sit.

**Not claimed.**
- Corollary B is not known to apply to any group outside the classes that already have FIID spines.
- Corollary C is one-directional. A group with `p_u^site(B_L) >= c (|B_L| L)^(-1/2)` for every `L` need not lack
  spines.
- The comparison in D is with the path-counting spectral bound, not with the best known lower bound on
  `p_u^site(Cay(F_2,B_L))`.

## Open question recorded here

**(Q) Hard-core Boolean uniqueness at square-root degree.** Let `Gamma` be a Tarski monster or a free Burnside group
of large odd exponent. Is `liminf_L p_u^site(Cay(Gamma, B_S(L) \ {e})) · (|B_L| L)^(1/2) = 0`?
- A yes gives FIID sparse spines, and kills every soft route to `p_c < p_u` on `Gamma`.
- A no, uniformly over all `T`, is necessary for the surviving restricted root on `Gamma`.
