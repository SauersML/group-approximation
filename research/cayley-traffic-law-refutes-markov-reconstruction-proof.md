---
rg: 2
id: cayley-traffic-law-refutes-markov-reconstruction-proof
kind: route
title: Evaluate both principles on the rooted Cayley law of the established nonsofic group
target: cayley-traffic-law-refutes-markov-reconstruction
requires:
  - finitely-presented-nonsofic-group-exists
  - markov-sofic-equals-sofic
---

Notation is as in the target claim: `F` is a window of `G` containing `e` and
closed under inverses, and test graphs are connected with edges labelled by
`F`.

**Item 1.**  Fix a spanning tree rooted at `v_0`.  A map `phi` in (CL) is
forced along the tree: `phi(v) = a_v`, the product of the labels read from
`v_0` to `v`.  A non-tree edge `e : v -> w` is consistent exactly when
`a_w^{-1} l(e) a_v = e` in `G`, i.e. when its cycle word is trivial.  So
`lambda_G(T)` is `1` or `0` as stated.

For a second root `v_1`, the map `phi -> phi . phi(v_1)^{-1}` is a bijection
between the maps with `phi(v_0) = e` and those with `phi(v_1) = e`.  Right
translation commutes with the edge law `phi(w) = l(e) phi(v)`.  A directed
cycle has one cycle word `w`, giving `1[w = e]`.

**Item 2.**

- (P1) Immediate from Item 1.
- (P2) `phi(w) = s phi(v)` if and only if `phi(v) = s^{-1} phi(w)`, so the
  reversed, relabelled graph has the same maps.
- (P3) Let `T_i` carry roots `rho_i in V(T_i)^k` with `k >= 1`.  Let
  `T_i o T_j` be the disjoint union with `rho_i(m)` identified to `rho_j(m)`.
  It is connected, and its maps are the pairs of maps agreeing on the roots.
  Root it at the image of `rho(1)` and put
  `f_i(x) = #{phi hom of T_i : phi(rho_i(m)) = x_m for all m}`.  Then

  ```text
  lambda_G(T_i o T_j) = sum over x in G^k with x_1 = e of f_i(x) f_j(x).
  ```

  Once `x_1 = e`, each `f_i` is `0/1` and nonzero at no more than one `x`
  (the tree values), so the sums are finite and

  ```text
  sum_{i,j} c_i conj(c_j) lambda_G(T_i o T_j) = sum_x |sum_i c_i f_i(x)|^2 >= 0.
  ```

  A finite action on `X` satisfies the same identity over `X^k`, with the
  factor `1/|X|`.
- (P4) Let `tau^0(T)` count the maps in (CL) that are injective on `V(T)`.
  Every map factors uniquely through its kernel partition `pi` as an injective
  map of the connected quotient graph `T/pi`.  Hence
  `lambda_G(T) = sum_pi tau^0(T/pi)`, and `tau^0 >= 0`.

**Item 3.**

- *If `G` is sofic.*  For `F` and `eps`, a sofic approximation with
  `sigma_e = id` gives permutation matrices `P_g`.  Normalized Hamming defect
  `d` gives `||P_g P_h - P_{gh}||_2 = sqrt(2 d)`, and `tau(P_g)` is the
  fixed-point density.  So the conclusion of RP holds for any choice of test
  graphs and `delta`.
- *If RP_G(P) holds.*  `lambda_G` lies in `P`.  By Item 1 it has deviation
  `0` from the canonical values on every test graph.  So every window `F` of
  `G` and every `eps > 0` admit a finite doubly stochastic model with the three
  bounds.  The tested products include `g g^{-1} = e`.  Thus every finite
  table of `G` is Markov-sofic, and `G` is sofic by `markov-sofic-equals-sofic`.

For the group `G_ns` of `finitely-presented-nonsofic-group-exists`, RP fails,
so no uniform reconstruction principle over all groups exists.

**Item 4.**  For `g, h, gh in F`, let `Delta_{g,h}` be the triangle with edges
`v_0 -h-> v_1 -g-> v_2` and `v_0 -gh-> v_2`.  For `g in F`, let `L_g` be one
vertex with a loop labelled `g`.  By
`permutation-traffic-is-simultaneous-fixed-points`, for a finite action
`sigma` on `X`:

- the law of `Delta_{g,h}` is `1 - d_H(sigma_g sigma_h, sigma_{gh})`;
- the law of `L_g` is the fixed-point density of `sigma_g`.

The canonical values are `1` and `1[g = e]`.

- *If RL_G(P) holds.*  Apply it to `lambda_G`.  A finite action within `eps`
  of it on these graphs has Hamming defect `< eps` on tested products and
  fixed-point density `< eps` on tested `g != e`.  That is a sofic model of
  the window, so `G` is sofic.  This direction uses neither
  `markov-sofic-equals-sofic` nor (P1)–(P4) beyond membership in `P`.
- *If `G` is sofic.*  Include every `Delta_{g,h}` and `L_g` among the test
  graphs and take `delta <= eps/2`.  A sofic approximation of accuracy `eps/2`
  is within `eps/2` of the canonical values there.  Any law within `delta` of
  them is then within `eps` of that action's law.

With `G = G_ns` both principles fail for every class `P` containing the
rooted Cayley laws.  ∎
