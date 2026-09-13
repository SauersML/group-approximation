---
rg: 2
id: refinement-monoids-are-topologically-free-cantor-types-proof
kind: route
title: Baire category over the cosets of Wehrung's witnesses in Aut(B, mu), with local swaps steering one point along each word
target: refinement-monoids-are-topologically-free-cantor-types
requires: [wehrung-countable-refinement-monoids-group-measurable, simple-refinement-monoids-are-minimal-cantor-types]
---

**Notation.**  As in Steps 1--4 of
`simple-refinement-monoids-are-minimal-cantor-types-proof`:
* `B` is a countable unital atomless Boolean ring;
* `mu: B -> M` is a V-measure with `mu(1) = e` that is both groupoid-induced
  and group-induced;
* `X` is the Stone space of `B`, a Cantor space, and `X_c` is the clopen set of
  `c in B`.

Automorphisms of `B` act on `X` by homeomorphisms.

**Step 1: exhaustive groups realize `(M, e)`.**  Let `Gamma <= Aut(B, mu)` be
`mu`-exhaustive.  Wehrung's Theorem 4.7.14(2) gives
`Z^+<B>//Gamma ≅ M`, `[1] -> e`.  Steps 3 and 5 of that proof use only this
isomorphism, so `(S(X, Gamma), [1_X]) ≅ (M, e)` and `Gamma` acts minimally.
Step 6 there matches invariant measures with states.

**Step 2: the witness space.**
* Since `mu` is group-induced, every pair `(a, b)` with `mu(a) = mu(b)` has
  decompositions `a = direct_sum_i a_i`, `b = direct_sum_i f_i(a_i)` with
  `f_i in Aut(B, mu)`.
* List all pieces over all countably many pairs as `(c_k, d_k)`, `k in N`, and
  put `C_k = {g in Aut(B, mu) : g(c_k) = d_k}`, which contains `f_i`.
* `Aut(B, mu)` is a closed subgroup of `Sym(B)`, hence Polish.  Each `C_k` is
  clopen and nonempty, so `P = prod_k C_k` is Polish.
* For `g in P`, the group `Gamma_g = <g_k : k in N>` is `mu`-exhaustive.

**Step 3: reduction to density.**  Fix a nontrivial reduced word `w` in
letters `x_k^(+-1)` and a nonzero `b in B`.  Let `U(w, b)` be the set of
`g in P` such that `w(g)` is not the identity on `B|b`, i.e. `w(g)(c) != c`
for some `c <= b`.
* `U(w, b)` is open: for fixed `c`, `w(g)(c)` depends continuously on finitely
  many coordinates, because inversion in `Sym(B)` is continuous.
* If `g` lies in all of the countably many `U(w, b)`, then:
  * no `w(g)` with `w != 1` is the identity, so `Gamma_g` is free on the
    `g_k`;
  * no nontrivial element fixes a nonempty clopen set pointwise, so the action
    is topologically free.
* By the Baire category theorem it suffices to prove that each `U(w, b)` is
  dense.

**Lemma R: local swaps.**  Let `A <= B` be a finite subalgebra, `x in X`, and
`Phi ⊆ X` finite.  Then some involution `tau in Aut(B, mu)` maps every atom of
`A` onto itself, fixes every point of `Phi \ {x}`, and sends `x` outside `Phi`.

*Proof.*
* Let `p` be the atom of `A` with `x in X_p`.  Choose a clopen
  `U_0 ⊊ X_p` containing `x` and missing `Phi \ {x}`.  Then choose a nonempty
  clopen `W ⊆ X_p \ (U_0 ∪ Phi)`, possible because `X` has no isolated points.
* By simplicity `mu(U_0) <= N mu(W)` for some `N`.  Riesz decomposition and the
  V-condition split `U_0 = U_1 ⊔ ... ⊔ U_N` with `mu(U_i) <= mu(W)`.  Let `U`
  be the piece containing `x`.
* The V-condition gives `V ⊆ W` with `mu(V) = mu(U)`.
* Since `mu` is groupoid-induced, some measure-preserving isomorphism
  `h: B|U -> B|V` exists.
* Put `tau = h direct_sum h^(-1) direct_sum id` on the complement of `U ∪ V`.
  It is a measure-preserving involution supported in `X_p`.  It fixes `Phi \ {x}`,
  which misses `U ∪ V`, and `tau(x) in V` lies outside `Phi`.  QED.

**Step 4: density by steering.**

*Setup.*
* Take `g in P` and a basic neighbourhood fixing the values of finitely many
  coordinates on a finite set `F ⊆ B`.
* Let `K` be the set of letters in `w`, and `A` the finite subalgebra generated
  by `F` and the `c_k` with `k in K`.
* For `k in K` put `g'_k = g_k sigma_k`, where `sigma_k in Aut(B, mu)` maps
  every atom of `A` onto itself.  Leave the other coordinates alone.
* Then `g'_k` agrees with `g_k` on `F` and `g'_k(c_k) = d_k`.  So `g'` is in
  `P` and in the neighbourhood.

*The steering.*
* Write `w = x_(k_m)^(eps_m) ... x_(k_1)^(eps_1)`, reduced, `m >= 1`.  Start with
  all `sigma_k = id` and a point `x_0 in X_b`.
* We build pairwise distinct points `x_0, ..., x_m` with
  `x_j = (g'_(k_j))^(eps_j)(x_(j-1))`.  We keep commitment sets
  `S_k = {x_(i-1) : k_i = k, eps_i = +1} ∪ {x_i : k_i = k, eps_i = -1}`.
* Step `i` depends on `sigma_(k_i)` only through its value at the committed
  point in `S_(k_i)`.  So replacing `sigma_k` by `sigma_k tau`, with `tau`
  fixing `S_k`, keeps all earlier steps.

*Step `j`, letter `k = k_j`, sign `+1`.*
* `x_(j-1)` is not in `S_k`.
  * It is not an earlier `x_(i-1)`, by distinctness.
  * If it were `x_i` for an earlier step `i` with letter `k^(-1)`, then
    `i = j-1` and `w` would contain `x_k x_k^(-1)`.
* Apply Lemma R with `x = x_(j-1)` and
  `Phi = {x_0, ..., x_(j-1)} ∪ S_k ∪ sigma_k^(-1) g_k^(-1) {x_0, ..., x_(j-1)}`.
* Replace `sigma_k` by `sigma_k tau`.  The new `x_j = g_k sigma_k(tau x_(j-1))`
  is not an earlier point, by the choice of `Phi`.  Add `x_(j-1)` to `S_k`.

*Step `j`, letter `k = k_j`, sign `-1`.*
* Let `z = g_k^(-1)(x_(j-1))` and `q = sigma_k^(-1)(z)`.  Then `q` is not in
  `S_k`.
  * If `q = x_(i-1)` for an earlier step `i` with letter `k`, then
    `x_i = g_k(z) = x_(j-1)`.  So `i = j-1` and `w` would contain
    `x_k^(-1) x_k`.
  * If `q = x_i` for an earlier step `i` with letter `k^(-1)`, then
    `g_k^(-1)(x_(i-1)) = z`.  So `x_(i-1) = x_(j-1)` and `i = j`.
* Apply Lemma R with `x = q` and `Phi = {x_0, ..., x_(j-1)} ∪ S_k`.
* Replace `sigma_k` by `sigma_k tau`.  Its value at `y = tau(q)` is `z`, so
  `(g'_k)^(-1)(x_(j-1)) = y` and `x_j = y` is not in `Phi`.  Add `x_j` to
  `S_k`.

*Conclusion.*  After `m` steps, `w(g')(x_0) = x_m != x_0` with
`x_0 in X_b`.  By continuity some clopen `c <= b` containing `x_0` is moved off
itself, so `g' in U(w, b)`.

**Step 5: conclusion.**  A comeager set of `g in P` generates `Gamma_g`, which
is free of countably infinite rank, acts topologically freely, is
`mu`-exhaustive, and hence minimal with `(S(X, Gamma_g), [1_X]) ≅ (M, e)`
(Step 1).

**Not covered.**
* Freeness.  Killing every fixed point of `w(g')` is not an open-dense
  condition that this steering controls.
* Finitely generated groups.  Exhaustiveness uses infinitely many witnesses.
