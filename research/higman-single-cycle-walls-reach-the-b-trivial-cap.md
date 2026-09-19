---
rg: 2
id: higman-single-cycle-walls-reach-the-b-trivial-cap
kind: claim
title: Single-cycle tree models of H(n, 3^(m_b), 3^(m_c), 3^(m_d)) with b trivial exist exactly up to level cap(m) = v2(3^(m_b) - 1) + v2(m_c) + v2(m_d) + 4, so every single-cycle wall is at least cap(m), and in every single-cycle model the orbits of b are the cones below one level j <= cap(m)
distinct_from:
  higman-h4-3-has-no-odometer-models-beyond-level-five: that computes the single wall w_0(3,3,3,3) = 5 by exhaustive search; this proves the exact wall of the b-trivial models for every twisted tuple in closed form, without search, and shows that its value 5 at m = (1,1,1) is the b-trivial cap.
  higman-h4-3-two-orbit-odometer-models-stop-at-level-seven: that enumerates the J = 1 family of H4(3)/<<[a,c]^2>>; this is about single-cycle models of the twisted groups H(n, 3^(m_b), 3^(m_c), 3^(m_d)) that the level-J subtrees of a J-model see, and gives explicit models up to level cap(m) for all of them.
  higman-j-odometer-models-restrict-to-single-cycle-models: that reduces J-odometer models to single-cycle models of the twisted groups, computes two exact walls and a random-probe table of lower bounds, and caps ord(a) by 64 ord(b) in 2-quotients of H4(3); this proves the b-trivial wall exactly for all twisted tuples and shows that most of that table's entries with m_b >= 2 are not walls.
  higman-power-pair-collapse-is-base-uniform-up-to-torsion: that asks whether H4(3)/<<[a,c]^2>> has generators of infinite order; this does not settle it, and only fixes the lower end of the walls that the J-odometer tree families can have.
artifacts:
  - experiments/higman-single-cycle-cap-2026-09-19/captower.py
  - experiments/higman-single-cycle-cap-2026-09-19/captower-output.txt
---

**ESTABLISHED** (proposed; items 1 to 4 proved, item 1 also computer-checked) by
`higman-single-cycle-walls-reach-the-b-trivial-cap-proof`.

**Setting.** For odd integers `n_i` put `H(n_1,n_2,n_3,n_4) = < a,b,c,d | b^a = b^(n_1), c^b = c^(n_2),
d^c = d^(n_3), a^d = a^(n_4) >` with `x^y = y^-1 x y`, so `H4(3) = H(3,3,3,3)`. Write permutations
as functions. Under the convention of `higman-h4-3-has-no-odometer-models-beyond-level-five`
(right action, `gh` = first `g`, then `h`) the relation `b^a = b^(n_1)` reads
`a∘b∘a^-1 = b^(n_1)`, and likewise for the other three. `W_k` is the automorphism group of the binary
tree truncated at level `k`, acting on `Z/2^k` with ancestor `x mod 2^r` at level `r`. A
*single-cycle model of level `k`* is a homomorphism `H -> W_k` with `a -> (x -> x + 1)`. By Lemma 1
of `higman-h4-3-has-no-odometer-models-beyond-level-five-proof` this is the same as a
homomorphism in which `a` is level-transitive. The *wall* `w_0(n)` is the largest level that
carries a single-cycle model.

Fix `m = (m_b, m_c, m_d)`, powers of 2, and the tuple `n(m) = (n_1, 3^(m_b), 3^(m_c), 3^(m_d))`
with `n_1` odd and arbitrary. Put `gamma(m_b) = v2(3^(m_b) - 1)`, so `gamma(1) = 1` and
`gamma(m_b) = v2(m_b) + 2` for even `m_b`. Put

  `cap(m) = gamma(m_b) + v2(m_c) + v2(m_d) + 4`.

**Statement.**
1. **The b-trivial wall is cap(m) exactly.** A single-cycle model of level `k` with `b -> 1` exists
   if and only if `k <= cap(m)`. The explicit model at level `k` is `a = x + 1`, `b = 1`,
   `d = 3^(m_d) x`, with `c` a valuation-preserving map. In log coordinates
   `2^v s 3^i` (`s = ±1`), `c` sends `2^v s 3^i` to `2^v s 3^(lambda(i))`, where
   `lambda(r + m_d q) = r + 3^(m_c) m_d q` for `0 <= r < m_d`. This holds on every layer `2^v U`
   with `n = k - v >= 3` and `2^(n-2) > m_d`, and `c` is the identity on the other layers.
   It does not depend on `n_1`. `captower.py` checks the model at every level `1..cap(m)` for all
   27 tuples with `m_b, m_c, m_d in {1, 2, 4}`, and for `n_1 in {3, 5, 7, -1}` at `m = (2,1,2)`.
   The check covers bijectivity, membership in `W_k` and all four relations.
2. **Lower bound for every wall.** `w_0(n(m)) >= cap(m)` for every `m` and every odd `n_1`.
3. **Block lemma.** In every single-cycle model of level `k` the orbits of `<b>` are the cones
   below the vertices of one level `j`, which are the residue classes mod `2^j`. So `b` fixes level
   `j`, acts as one `2^(k-j)`-cycle on each cone, and `ord(b) = 2^(k-j)`. The action on level `j`
   is a b-trivial single-cycle model, so `j <= cap(m)` by item 1. If `n_1 ≡ 3 mod 4` and `k >= 2`,
   then `j >= 1`.
4. **Rigidity lemma.** If `x, y` in `W_M` are both level-transitive and `y∘x∘y^-1 = x^q` with
   `q ≡ 3 mod 4`, then `M <= 1`. In particular no single-cycle model of a tuple with
   `n_1 ≡ 3 mod 4` has a level-transitive `b` at level `>= 2`.

**Comparison with the known walls** (computed elsewhere).
- `w_0(3,3,3,3) = 5 = cap(1,1,1)`, by `higman-h4-3-has-no-odometer-models-beyond-level-five`.
- `higman-j-odometer-models-restrict-to-single-cycle-models` (item 4) finds by exact search that
  `w_0(3,3,3,9) = 6 = cap(1,1,2)` and `w_0(3,3,9,3) = 6 = cap(1,2,1)`. In its random-probe table
  the nine rows with `m_b = 1` reach `cap(m)` exactly; this is its formula
  `5 + log2 m_c + log2 m_d`. Of the 17 rows with `m_b >= 2`, only `(2,1,1)` and `(4,1,1)` reach
  `cap(m)`, and the other 15 stop below it, for example
  `(2,1,2)`: 7 against 8, `(4,1,4)`: 8 against 10, `(4,4,4)`: 9 against 12. By item 2 those probe
  depths are search limits, not walls.
- Every exactly known wall equals `cap(m)`, and every model found so far has `j <= cap(m)`.

**Consequences.**
- *Reformulation of the wall.* By item 3 every single-cycle model is a b-trivial model on level
  `j <= cap(m)` with `b` filling the cones below it. So `w_0(n(m)) = cap(m)` holds if and only if
  every single-cycle model satisfies `ord(b) <= 2^(cap(m) - j)`, that is, the cones that `b`
  fills cannot extend beyond `cap(m)`. This is open (**conjecture**). The rotation below
  bounds `ord(b)` by a wall of a rotated tuple, and that bound is circular.
- *Rotation.* Let `v` be a vertex at level `j`, and let `2^p`, `2^q` be the lengths of the `<c>`-
  and `<d>`-orbits of `v`. Then `(b, c^(2^p), d^(2^q), a^(2^j))` restricted to the cone of `v` is a
  single-cycle model of `H(n_2, n_3^(2^p), n_4^(2^q), n_1^(2^j))`, with `b` as the odometer, so
  `k - j <= w_0` of that tuple.
- *J-odometer models.* Take a model of `H4(3)` with `a = x + 2^J`. Restricting to the cone of a
  level-`J` vertex `v` gives a single-cycle model of `H(3, 3^(m_b), 3^(m_c), 3^(m_d))` at level
  `k - J`, where the `m`'s are the orbit lengths of `v` (so each is at most `2^J`). This is item 1
  of `higman-j-odometer-models-restrict-to-single-cycle-models`. By item 2 this reduction can never prove a bound below `J + cap(m)` for
  the `m` that occur. If the conjecture holds, every J-model dies by level
  `J + max cap = 4J + 6` (`J >= 1`), since `cap(m) <= 3J + 6` for `m_* <= 2^J`.

**What it kills and what it leaves.**
- Dead: the reading of the probe depths as walls, and any hope that single-cycle walls of the
  twisted tuples stay near 5. They grow at least linearly in `log m`.
- Dead: level-transitive `b` in single-cycle models once `n_1 ≡ 3 mod 4` and `k >= 2` (item 4).
- Left: the upper bound `w_0 <= cap`, which amounts to the bound on `ord(b)` above. A route is
  to show that `b` is affine in the coordinates in which `a = x + 1`. Then the relation
  `a∘b∘a^-1 = b^(n_1)` would bound `ord(b)` by a constant, and so `k <= cap(m) + O(1)`.
