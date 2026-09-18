---
rg: 2
id: local-gadgets-above-exactness-pay-a-random-assignment-floor
kind: claim
title: A gadget reduction that keeps the outer labels and gives each outer constraint private auxiliaries earns completeness above direct exactness only by raising the random-assignment value of every output, so from 2-to-2 or 2-to-1 sources it obeys c <= 1/2 + 2s
distinct_from:
  unique-constraints-orient-at-most-half-of-a-fiber: that is the perfect-completeness injectivity wall for unique networks and says nothing about soundness; this is a quantitative completeness/soundness trade-off at any completeness, with auxiliaries of arbitrary alphabet and arbitrary auxiliary predicates, proved instance by instance through the random-assignment value.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that covers verifiers whose encodings are affine views shared by all constraints at a vertex, with no free auxiliaries; this covers verifiers with free, prover-chosen, constraint-private auxiliaries and arbitrary nonlinear predicates, and needs no linear structure in the source.
  dummy-padding-cannot-beat-the-random-guessing-floor: that is the random floor of the source 2-to-1 game against one decoding-list attack; this is a floor on the output of every local gadget reduction, forced by its own completeness.
  unique-games-hard-at-completeness-one-half: that is the split reduction at c = 1/2; it is the s -> 0 extreme of the trade-off proved here, which is therefore tight.
artifacts:
  - experiments/edge-local-gadget-floor-2026-09-17/check_gadget_floor.py
  - experiments/edge-local-gadget-floor-2026-09-17/run-output.txt
---

**ESTABLISHED.**

*Source.* An outer instance `Phi` is a weighted family of **patches**. A patch
`N` is a set of `k = |N|` outer vertices with alphabets `[K_z]` and a local
satisfying set `S_N <= prod_(z in N) [K_z]`. For a two-prover game the patches
are the edges and `S_N` is the constraint relation `R_e`. `M_N` bounds the
marginal density of `S_N`: `Pr_(x ~ S_N)[x_z = t] <= M_N / K_z` for all `z, t`.
For biregular relations such as `d`-to-`d` and `2`-to-`1`, `M_N = 1`.

*Local gadget reduction `Gamma`.* The output has one **primary** vertex per
outer vertex, carrying the outer label (any injective relabeling is the same
thing). Each patch `N` gets a gadget: a set of **private auxiliary** vertices
of arbitrary alphabets and weighted constraints, total weight `1`, whose scopes
lie in `N` plus that patch's auxiliaries. Predicates are arbitrary, with one
restriction: a scope that meets two or more primaries contains no auxiliary
(a **direct** constraint). The output game is `sum_N mu_N (gadget of N)`. The
gadgets may depend on the whole instance. A unique game output is the special
case where every constraint is a permutation.

For a patch write `v_N(x)` for the best satisfied weight over auxiliary
assignments with primary labels `x`, and `h_N(x)` for the satisfied direct
weight. Put

```text
c_N     = E_(x ~ S_N) v_N(x)                  oblivious completeness
ex_N    = E_(x ~ S_N) h_N(x)                  direct exactness
floor_N = E_(x ~ uniform on prod [K_z]) v_N(x)
```

1. **Local inequality.** With `r_z(t) = min { v_N(x) : x_z = t }`,
   `v_N(x) - h_N(x) <= sum_(z in N) r_z(x_z)` for every `x`.
2. **Patch floor.** `c_N - ex_N <= M_N k floor_N`.
3. **Instance floor.** For **every** input `Phi`, including NO instances,
   ```text
   val(Gamma(Phi)) >= sum_N mu_N floor_N >= sum_N mu_N (c_N - ex_N) / (M_N k_N).
   ```
4. **Direct exactness of 2-prover sources.** If `S_N` is biregular with degrees
   `d_L, d_R`, and the direct constraints are partial permutations of total
   weight `W_N`, then `ex_N <= W_N / d` with `d = max(d_L, d_R)`. For
   2-to-2 and 2-to-1 constraints `ex_N <= 1/2`.
5. **Reduction trade-off.** Suppose a local gadget reduction from a 2-to-2 or
   2-to-1 source outputs unique games and proves `Gap-UG(c, s)` hard with an
   **oblivious** completeness certificate. That means the gadget family satisfies
   `sum_N mu_N c_N >= c` on every input, YES or NO. This holds whenever
   completeness is argued gadget by gadget from "the outer labels lie in `S_N`",
   with the same gadget shapes on all inputs. Then
   ```text
   c <= 1/2 + 2 s.
   ```
   At completeness `1 - eta'` the soundness is at least `1/4 - eta'/2`.
   Near-1 versus near-0 is impossible.
   For `d`-to-`d` sources the threshold is `1/d`, and unique sources (`d = 1`)
   are not obstructed, which is the calibration.
6. **Tightness.** The split gadget (two branch permutations of weight `1/2`)
   has `c = ex = 1/2` and `floor = 1/K`: this is the `s -> 0` end. The
   block-projection gadget (one auxiliary equal to the block index of both
   primaries, not a unique constraint) has `c = 1`, `ex = 0` and
   `floor = 1/2 + 1/K`, so item 2 is asymptotically an equality. The replay
   checks 1--4 exhaustively on 3000 random gadgets over `4x4` and `6x6`
   `d`-to-`d` relations, 2-to-1 relations and 3-vertex patches, with unique and
   arbitrary predicates.

**Sub-relation loophole.** A gadget that is good only on a sub-relation
`T_N < S_N`, used on sources whose planted solutions stay inside `T_N`, is
covered by applying items 1--3 with `T_N` in place of `S_N`. Then the threshold is
the exactness `E_(T_N) h_N`. This exceeds `1/2` only if direct permutations
capture most of `T_N`, which means the planted source restricted to `T` is
already close to a unique game. So the loophole is circular in the same way as
`bkm-test-transparent-on-learnable-games`.

**Consequence for `unique-games-conjecture` (shape of any near-1 reduction).**
Item 3 says a proof of Gap-UG hardness above completeness `1/2`, from any source
whose patches have direct exactness at most `1/2`, cannot use private per-constraint
gadgets around the outer labels with a patch-by-patch (oblivious) completeness
certificate, however large or nonlinear the gadgets are. The completeness
gain must be spent in auxiliary structure **shared across outer constraints**,
i.e. vertex-owned encodings such as long-code tables. Together with the
neighbouring obstructions, this pins down what such a reduction must look like:

* private auxiliaries: floor, this claim;
* shared affine views: collapse to a test-free quotient game,
  `linear-view-unique-verifiers-collapse-to-quotient-coarsening`;
* shared long-code views on learnable pairings: transparent to the derived unique game,
  `bkm-test-transparent-on-learnable-games`.

The shape these leave open includes shared, non-affine encodings on unlearnable
pairing families, the regime of `smooth-design-rich-2to1-hardness`. They do not
cover completeness certified through global structure of the instance, or
sources whose patches have direct exactness above `1/2`. This neither proves
nor refutes UGC.

DERIVATION local-gadget-random-floor-proof
