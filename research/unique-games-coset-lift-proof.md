---
rg: 2
id: unique-games-coset-lift-proof
kind: route
title: Tree-gauge and orbit-split the game, lift each transitive orbit to the regular action of its holonomy group by choosing coset representatives at random, and project back through the orbit map
target: unique-games-lift-to-group-shift-games-on-the-same-host
requires:
  - unique-games-reduce-to-shifts-over-their-holonomy-group
artifacts:
  - experiments/ugc-coset-lift-2026-09-17/check_coset_lift.py
---

A direct, elementary proof. The only import is HOL =
`unique-games-reduce-to-shifts-over-their-holonomy-group`, items 1, 2, 4 and 6,
which are ESTABLISHED. Notation is as in the target claim. A constraint on
`e = (u, v)` reads `sigma_v = pi_e(sigma_u)`. Permutations compose right to
left.

**0. The orbit games.** By HOL 2, in the tree gauge `U^g` every constraint
`pi_e^g` lies in `H`, so it maps each orbit `O_i` to itself. By HOL 4, `U_i` is
the unique game with alphabet `O_i` and constraints `gamma_e = pi_e^g|_(O_i)`,
and `max_i val(U_i) <= val(U) <= sum_i val(U_i)`. The group `H_i` is the image
of `H` under restriction to `O_i`. It is transitive on `O_i`, and
`gamma_e in H_i` for every edge.

**1. Projection.** `p_i(a) = a(o_i)`. It is onto, because `H_i` is
transitive. We have `p_i(a) = p_i(a')` iff `a^(-1) a' in K_i` iff
`a' in a K_i`. So the fibres are the left cosets of `K_i`, each of size
`|K_i|`. Also, `p_i(gamma a) = (gamma a)(o_i) = gamma(a(o_i)) = gamma(p_i(a))`.

Let `h` be a labeling of `L_i` and put `tau_v = p_i(h_v) in O_i`. If `h`
satisfies `e`, that is `h_v = gamma_e h_u`, then
`tau_v = p_i(gamma_e h_u) = gamma_e(tau_u)`, so `tau` satisfies `e` in `U_i`.
Now `U_i` is the restriction of `U^g` to the invariant set `O_i`. So `tau`,
viewed as a labeling of `U^g` with values in `O_i`, satisfies the same edges
in `U^g`. By HOL 1, `sigma_v = g_v^(-1)(tau_v)` satisfies those edges in `U`.
Hence `val_U(sigma) >= val_(U_i)(tau) >= val_(L_i)(h)`. Taking `h` optimal
gives `val(L_i) <= val(U_i) <= val(U)`. The last inequality is HOL 4.

**2. Random lift.** Fix a labeling `tau` of `U_i`. Choose independent uniform
`h_v in p_i^(-1)(tau_v)`.

* If `tau` violates `e`, then `h` violates `e`, by step 1 (contrapositive).
* Let `e = (u, v)`, `u != v`, be satisfied by `tau`: `tau_v = gamma_e(tau_u)`.
  Condition on `h_u = a`. Then `gamma_e a` lies in the fibre
  `p_i^(-1)(gamma_e(tau_u)) = p_i^(-1)(tau_v)`. Since `h_v` is uniform on that
  fibre and independent of `h_u`,
  `Pr[h_v = gamma_e a | h_u = a] = 1/|K_i|`. Average over `a`.
* A satisfied self-loop contributes at least `0`.

By linearity, `E[val_(L_i)(h)] = (val_(U_i)(tau) - lambda_tau)/|K_i| + lambda'`,
where `lambda_tau <= lambda(U)` is the weight fraction of the self-loops that
`tau` satisfies, and `lambda' >= 0`. So some `h` attains at least
`(val_(U_i)(tau) - lambda(U))/|K_i|`. Take `tau` optimal.

**3. Sizes.**

* `H_i` embeds in `Sym(O_i)`, so `|H_i| <= |O_i|!`.
* By orbit-stabilizer, `|K_i| = |H_i|/|O_i| <= (|O_i| - 1)!`.
* The orbits partition `[k]`, so `t <= k`.
* `(|O_i| - 1)! <= (k - 1)!` gives `t |K_i| <= k (k-1)! = k!`.

On a loopless graph, pick `i` with `val(U_i)` maximal. HOL 4 gives
`val(U_i) >= val(U)/t`, and step 2 then gives
`val(L_i) >= val(U)/(t |K_i|) >= val(U)/k!`.

**4. Time.**

* HOL 6 computes `g` and the gauged constraints in `poly(|E|, k)`.
* The closure of the `|E|` gauged constraints, by breadth-first search in
  `S_k`, has at most `k!` elements. It is computed in
  `O(|E| k! k)` steps, which is `poly(|E|)` for fixed `k`.
* The orbits, the restrictions `H_i`, the multiplication tables (at most
  `(k!)^2` entries) and the `t` lifts (one group element per edge) follow.
* The projection of step 1 is explicit.

**5. Equivalence.**

*(b) implies (a).* Given `U` with alphabet `k` on `G in C` and `val(U) >= c`,
compute all lifts `L_i`. Each is an `H_i`-shift game on the same graph
`G in C`, and `H_i` is a transitive group of degree `|O_i| <= k`. By step 3,
some `L_i` has value `>= c/k!`. Let `delta_A` be the constant for `A`-shift
games at completeness `c/k!`. Run the shift-game algorithm for `H_i` on every
`L_i`, project each output by step 1, and keep the best labeling of `U`. The
chosen orbit returns value `>= delta_(H_i)`, so the result has value
`>= delta := min_A delta_A`. The minimum is over the finitely many
isomorphism types of transitive groups of degree `<= k`, so `delta > 0`.

*(a) implies (b).* An `A`-shift game is a unique game with alphabet `|A|` on the
same graph, after any bijection `A -> [|A|]`.

**6. Gap form.** YES: step 3. NO: step 1 gives `val(L_i) <= val(U) <= s` for
every `i`. The group `H_i` is a quotient of `H`, so it is solvable, nilpotent
or abelian whenever `H` is. Also, `H_i` is regular exactly when `K_i = 1`, and
then `L_i` is isomorphic to the shift form of HOL 5 with no loss.

**Check.** `experiments/ugc-coset-lift-2026-09-17/check_coset_lift.py`, Part A,
verifies steps 1--3 by exhaustive search on 30 instances, 23 of which have a
non-regular orbit. Its output is recorded in `output.txt`.
