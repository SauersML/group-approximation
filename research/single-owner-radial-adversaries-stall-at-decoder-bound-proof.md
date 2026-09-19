---
rg: 2
id: single-owner-radial-adversaries-stall-at-decoder-bound-proof
kind: route
title: Level averaging turns a single-owner radial adversary into a label path, and the weights 1/((K-1-d)(K-2-d)) price the forced class crossing of the disagree branch at 4 - 4/K wherever it happens
target: single-owner-radial-adversaries-stall-at-decoder-bound
requires: []
artifacts:
  - experiments/ugc-hadamard-margin-adversary-2026-09-17/check_single_owner_dual.py
  - experiments/ugc-hadamard-margin-adversary-2026-09-17/radial_zone_lp.py
---

Throughout, `T = K/4` and `k >= 2`, so `K >= 4`. The notation is that of the
target claim.

## Step 1: level averaging

Fix a zone `y0 = s chi_p`, and fix one realization `omega` of all the
randomness: `xi`, `(i, tau)` and the label sequence `L = L_p`.

**The branch.** The zone is in the *agree* branch if `xi_p = tau chi_p(i)`
and in the *disagree* branch otherwise. Write `S(x)` for the set of
coordinates where `x` differs from `y0`.

**The labels relative to `C`.** Multiply every label by `s xi_p`.

* `C` becomes `+1`.
* In the agree branch, `D(x) = tau x_i` becomes `+1` if `i` is not in `S(x)`
  and `-1` if it is.
* In the disagree branch the same holds with `D` and `-D` exchanged.

So after renaming `D <-> -D` in the disagree branch (the *agree view*), both
branches are the same combinatorial problem with different boundary labels.

* **Start.** The labels equal to `C` at `y0`, where `S` is empty, are
  `{C, D}` in both views. This is forced by `A(y0) = s xi_p`.
* **End at level `T`.** Level `T` lies outside all zones, so the label there
  is `D`. In the agree view it is `D` in the agree branch and `-D` in the
  disagree branch.

**Level-`d` edges.** A level-`d` edge is `x -> x^j` with `|S(x)| = d` and `j`
not in `S(x)`, for `0 <= d <= T - 1`. Take such an edge uniformly at random.
For the fixed coordinate `i`:

* `Pr[i in S(x)] = d/K`;
* `Pr[i = j] = 1/K`;
* `Pr[i outside S(x) and i != j] = (K-d-1)/K`.

Both endpoint labels are `L(d)` and `L(d+1)`, fixed by `omega`. So the
average over level-`d` edges of `K 1[cut]` equals `c_d(L(d), L(d+1))`, in the
agree view. The table below lists `c_d`, and it is the same in both branches.

| s -> t | c_d |
|---|---|
| C->C, -C->-C | 0 |
| D->D, -D->-D | 1 |
| D->C, -D->-C | d |
| C->D, -C->-D | d+1 |
| C->-D, -C->D | K-d-1 |
| D->-C, -D->C | K-d |
| C->-C, -C->C, D->-D, -D->D | K |

`check_single_owner_dual.py` checks this table against `radial_zone_lp.cut_prob`.

## Step 2: the dual bound

**Reduction to the path.** Let `R` be the adversary's value `max_e K Pr[cut e]`,
and let `w_d >= 0` be weights with `sum_d w_d = 1`. For each `d`,
`R >= avg over level-d edges of K Pr[cut]`, which is `E_omega c_d(L(d), L(d+1))`.
Taking the `w`-combination,

  `R >= E_omega [ Phi(L) ]`,  where  `Phi(L) = sum_{d<T} w_d c_d(L(d), L(d+1))`.

So it suffices to bound `Phi` pathwise:

* `Phi >= 1` for agree paths (start in `{C, D}`, end at `D`);
* `Phi >= 4 - 4/K` for disagree paths (start in `{C, D}`, end at `-D`).

**The weights.** Take

  `w_d = C / ((K-1-d)(K-2-d)) = C (1/(K-2-d) - 1/(K-1-d))`,  with  `C = (3K-4)(K-1)/K`.

**Tail sums.** They telescope:

  `W_e := sum_{d=e}^{T-1} w_d = C (1/(K-1-T) - 1/(K-1-e))`.

`W_0 = C T/((K-1-T)(K-1))`, and with `T = K/4` this is `1`. Two more
identities are used below:

  `C/(K-1-T) = 4(K-1)/K = 4 - 4/K`,  and  `C/(K-2) > 1`.

The second holds because `(3K-4)(K-1) > K(K-2)` for `K >= 2`.

**Two label classes.** Call the transitions in the first four rows of the
table *small* and those in the last three *big*. Small transitions stay inside
`{C, D}` or inside `{-C, -D}`. Big transitions cross between the two classes.

* A big transition at level `d` costs `w_d c_d >= w_d (K-d-1) = C/(K-2-d)`.
* This is at least `C/(K-2) > 1`.

## Step 3: agree paths, and every suffix

**Lemma A.** Fix `e` in `0..T`. Every label path on levels `e..T` that ends
at `D` or at `-D` has `sum_{d>=e} w_d c_d >= W_e`.

*Proof.* If the path contains a big transition, its cost exceeds `1`, which is
at least `W_e`. Otherwise it stays in one class. By the negation symmetry of the table we may
take it to be a path in `{C, D}` ending at `D`. Split its edges into:

* `D->D` edges, each costing exactly `w_d`;
* blocks of the form "optional entry `D->C` at edge `a-1`, then `C->C` edges,
  then exit `C->D` at edge `b`".

Every `C`-run has an exit, because the path ends at `D`. A block costs at
least its exit cost `w_b (b+1)`. Moreover

  `sum_{d=0}^{b} w_d = C (b+1)/((K-2-b)(K-1)) <= C (b+1)/((K-2-b)(K-1-b)) = w_b (b+1)`,

so each block costs at least the sum of `w_d` over its own edges. The blocks
and the `D->D` edges partition the edges `e..T-1`, so the total is at least
`W_e`. QED.

With `e = 0`, **every agree path has `Phi >= W_0 = 1`.**

## Step 4: disagree paths

A disagree path starts in `{C, D}` and ends at `-D`, so it has at least one
big transition. Let the first one be at edge `d`, going from level `d` to
level `d+1`. Then:

* the edges before it cost at least `0`;
* the big transition costs at least `C/(K-2-d)`;
* the suffix from level `d+1` ends at `-D`, so it costs at least `W_{d+1}`
  by Lemma A.

So

  `Phi >= C/(K-2-d) + C (1/(K-1-T) - 1/(K-2-d)) = C/(K-1-T) = 4 - 4/K`.

**The bound does not depend on where the crossing happens.** This is the
obstruction: every place where the disagree branch can leave `C` for the
fallback costs the same under `w`.

## Step 5: assembling

For zone `p`, write `delta_p = Pr[disagree]`. Then

  `R >= (1 - delta_p) 1 + delta_p (4 - 4/K) = 1 + delta_p (3 - 4/K)`.

**Averaging over `p`.** For fixed `(xi, i, tau)`, the number of disagreeing
`p` is the distance from `xi` to the signed Reed-Muller codeword
`p -> tau chi_p(i)`. This is at least `d(xi, RM(1,k))`. Taking expectations,
`avg_p delta_p >= delta_k`, and so `max_p delta_p >= delta_k`. This proves the
claim.

**Exactness.** `check_single_owner_dual.py` computes the exact shortest
`w`-weighted paths by rational dynamic programming, for `K = 8` to `1024`. It
gets exactly `1` for the agree branch and `4 - 4/K` for the disagree branch.

## Step 6: the numerical corollary for k >= 7

**A lower bound on `delta_k`.** Write `W_i = sum_p xi_p chi_p(i)`. Then
`delta_k = 1/2 - E max_i |W_i|/(2K)`, as in the window proof. The `2K`
variables `+-W_i` are each sums of `K` independent signs, so each has
`E e^(lambda X) <= e^(lambda^2 K/2)`. The standard maximal inequality gives

  `E max_i |W_i| <= sqrt(2K ln(2K))`.

Hence

  `delta_k >= 1/2 - sqrt(ln(2K)/(2K))`.

The right side increases with `K`. At `K = 128` it is `0.3528`.

**The class value.** For `k >= 7` we have `3 - 4/K >= 2.96875`, so the class
value is at least `1 + 0.3528 (2.96875) > 2.047`. It tends to `5/2`.
