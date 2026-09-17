---
rg: 2
id: low-degree-view-unique-verifiers-collapse
kind: claim
title: A unique verifier over a linear outer game with completeness 1-eps whose view differences have degree D keeps exact weight at least 1 - eps p^D, so below degree log_p(1/eps) it is no sounder than a test-free branch-blind partition coarsening
distinct_from:
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that treats affine views only, with the sharp threshold c > 1/p and subspace kernels; this treats arbitrary views, where exact triples induce bijections between level-set partitions, and bounds the exact weight by 1 - (1-c) p^D using the algebraic degree D of the view differences. It kills Reed--Muller, short-code-type and quadratic encodings of degree below log_p(1/eps), not only Hadamard and Grassmann views.
  derived-unique-game-lower-bounds-the-noise-test: that bounds the long-code noise test from below by a derived unique game and needs a decoder on learnable matchings; this needs no decoder and no richness hypothesis, and shows why only views of degree at least log_p(1/eps) - O(1), such as long codes, can escape.
  unique-constraints-orient-at-most-half-of-a-fiber: that is the perfect-completeness injectivity wall for local gadgets; this is the quantitative near-1 statement for arbitrary composed verifiers.
artifacts:
  - experiments/low-degree-view-collapse-2026-09-17/check_low_degree_collapse.py
---

**OPEN.** Fix a prime `p`.

*Outer linear game `Phi`* (as in
`linear-view-unique-verifiers-collapse-to-quotient-coarsening`). A weighted graph
`(Z, E, mu)`. Each `z` has a label space `A_z`, a finite affine space over `F_p`.
Each edge `e = (a,b)` carries an affine subspace `H_e <= A_a x A_b` whose
projections onto `A_a` and `A_b` are onto. Linear 2-to-2 games qualify, with
`H_e = { T x_a + T' x_b in b + <c> }` and `T, T'` invertible.

*Unique verifier `V` with arbitrary views.* Output vertices `W` with owners
`o : W -> Z` and **arbitrary** functions `rho_w : A_(o(w)) -> F_p^k`. Each outer
edge carries a distribution `tau_e` on triples `t = (w, w', sigma)` with
`o(w), o(w') in {a,b}` and `sigma` a bijection of `F_p^k`. The output unique game
`V(Phi)` draws `e ~ mu`, then `t ~ tau_e`, and accepts iff `sigma(F(w)) = F(w')`.
*Oblivious completeness* `c` is the acceptance of honest labels
`F(w) = rho_w(x_(o(w)))`, averaged over `e`, `t` and a uniform `h in H_e`
(worst-case completeness over `H_e` implies it). A triple is **exact** if it
accepts every `h in H_e`; `w_ex` is the total weight of exact triples.

*Degree.* For a triple `t` on `e`, let `Q_t : H_e -> F_p^k`,
`Q_t(h) = sigma(rho_w(h_(o(w)))) - rho_(w')(h_(o(w')))`. Put `deg t` = the largest
reduced polynomial degree of a coordinate of `Q_t o phi`, for an affine
parametrization `phi : F_p^m -> H_e` (independent of `phi`). Put
`D(V) = max deg t` over non-exact triples. If every view has degree `<= d`, then
`D(V) <= d` for affine `sigma` and `D(V) <= k(p-1)d` for arbitrary `sigma`.

1. **Density lemma.** A nonzero `f : F_p^m -> F_p` of reduced degree `<= D` is
   nonzero on at least `p^(m-D)` points. At `p = 2` this is attained by
   `x_1 x_2 ... x_D`.
2. **Rigidity threshold.** Every non-exact triple `t` rejects at least a
   `p^(-deg t)` fraction of `H_e`. Hence
   ```text
   w_ex >= 1 - (1 - c) p^(D(V))          (= 1 - eps p^D at c = 1 - eps).
   ```
   The bound is attained at `p = 2` by mixing exact triples with the same-owner
   triples `rho_w = 0`, `rho_(w') = x_1 ... x_D`, `sigma = id`. For `D = 1, p = 2`
   it is the bound `2c - 1` of the affine claim.
3. **Partition coarsening.** For a view `rho_w` let `P_w` be its level-set
   partition of `A_(o(w))`. An exact cross triple induces a bijection
   `beta_t : A_a/P_w -> A_b/P_(w')` determined by `H_e` and the two partitions
   alone, with `sigma o rho-bar_w = rho-bar_(w') o beta_t`. An exact same-owner
   triple has `P_w = P_(w')` and `beta_t = id`. Let `Can_part(Phi, V)` be the unique
   game on vertices `(z, P)`, labels the classes of `P`, edges the exact triples
   with constraints `beta_t`. Then for **every** input `Phi`
   ```text
   val(V(Phi)) >= w_ex * val(Can_part(Phi, V)),
   ```
   and an outer labeling of weight `1 - eta` gives `val(Can_part) >= 1 - eta/w_ex`.
4. **Branch blindness.** On a 2-to-2 edge, an exact cross triple has
   `rho_w(x + T^-1 c) = rho_w(x)` and `rho_(w')(y + T'^-1 c) = rho_(w')(y)` for all
   `x, y`. Every branch `H^s = { T x_a + T' x_b = b + s c }` has the same image
   relation, so `Can_part` has the same value for both branch choices of every
   constraint.
5. **Transparency below degree `log_p(1/eps)`.** Suppose a family of verifiers
   with completeness `c = 1 - eps` and `eps p^(D(V)) <= theta < 1`, with constant
   local size, proves `Gap-UG(c_G, s)` NP-hard from `Gap-Phi(1 - eta, s_Phi)`. Then
   the test-free map `Phi -> Can_part(Phi, V)` proves
   `Gap-UG(1 - eta/(1-theta), s/(1-theta))` NP-hard, for unique games in
   label-cover form (per-vertex alphabets of size at most `p^l`, equal along
   edges). So no expansion property of
   the encoding enters soundness.
6. **Necessary degree.** If `val(Can_part(Phi, V)) >= lambda` on the NO instances
   and `val(V(Phi)) <= s < lambda`, then `w_ex <= s/lambda`, and
   ```text
   D(V) >= log_p( (1 - s/lambda) / eps ).
   ```

**Consequence for `unique-games-conjecture`.** Take any composition proof of
near-1 unique games hardness over a linear outer game, such as the 2-to-2
instances of `two-to-two-games-theorem`. Name the invariant: the algebraic degree
`D` of the view differences on the outer constraint spaces. Every verifier with
`eps p^D -> 0` dies at step (2). Its non-exact triples each reject honest labels
with probability at least `p^-D`, which is much larger than `eps`, so they carry
`o(1)` weight. The proof then factors through the branch-blind, encoding-free
coarsening `Can_part` of the outer game. This covers the Hadamard and Grassmann
views (`D = 1`), quadratic encodings `x -> x (x) x` (`D = 2`), and
Reed--Muller or short-code tables of degree `d` (the view at table point `P` is
`x -> P(x)`, `D <= d`), as long as `d <= (1 - gamma) log_p(1/eps)`. A verifier
that crosses the `1/2` wall without first proving a coarsening hard needs
`Omega(1)` weight on soft triples, each rejecting honest labels with probability
`O(eps)`. By (1) such triples have degree at least `log_p(1/eps) - O(1)`. That is
the long-code and high-degree short-code regime, where
`derived-unique-game-lower-bounds-the-noise-test` and the richness region
constrain things further.

This neither proves nor refutes UGC.

## Attempts

- **Referee round (2026-09-17): not established.** Route
  `low-degree-view-unique-verifiers-collapse-proof` and the check script
  `experiments/low-degree-view-collapse-2026-09-17/check_low_degree_collapse.py`
  (0 failures on seeds `20260917` and `7`) were refereed by three lenses. Two
  refuted, one survived.
  - All three confirm items 1-6 as formal statements: the density induction, the
    bound `w_ex >= 1 - (1-c) p^D`, the partition bijections `beta_t`, both value
    transfers, the item 5 parameters and item 6.
  - **Refutation (lenses 1 and 2).** The Consequence paragraph lists the views it
    kills (Hadamard and Grassmann `D = 1`, quadratic `D = 2`, Reed--Muller
    `D <= d`) as if `D` depended only on the views. `D` is the degree of
    `sigma o rho_w - rho_(w')`, which is at most `d` only for affine `sigma`, and
    the model allows arbitrary bijections. Counterexample: Grassmann views
    `rho_w = rho_(w') = x|_L` in `F_2^l` with `sigma` the transposition of two
    points. Then `Q_t` is nonzero on 2 of `2^l` points, `deg t = l - 1`, and the
    triple accepts honest labels with probability `1 - 2^(1-l)`. At
    `eps ~ 2^-l` the bound is empty, and such soft triples can carry `Omega(1)`
    weight. The same happens for quadratic encodings, and for Reed--Muller tables
    over `F_p`, `p >= 5`, where non-affine permutations push `D` up to `(p-2)d`.
    So the class-killing consequence is established only for affine `sigma`. The
    remaining case is `low-degree-view-collapse-survives-non-affine-sigma`, which
    the route now requires.
  - **Lesser gap (lens 1).** Item 4 shows that `beta_t` does not change on the
    triples exact on `H_e`. It does not show that `Can_part` of the instance with
    a branch substituted has the same value, since that instance has further
    triples exact on `H^s` but not on `H_e`. Branch blindness holds for the edge
    set of the original instance only.
  - **Citation problems in `unique-games-conjecture` (lenses 2 and 3).** P1 and
    P2 are alternatives, not joint prerequisites. P3 cites
    `bkm-test-transparent-on-learnable-games` without its learnable-family
    hypothesis. The remark that 2-to-2 machinery "does not supply" 99%-regime
    soundness is unsupported.
