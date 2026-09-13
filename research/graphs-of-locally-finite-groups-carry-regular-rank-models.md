---
rg: 2
id: graphs-of-locally-finite-groups-carry-regular-rank-models
kind: claim
title: Graphs of locally finite subgroups of the binary Leavitt unit group carry weakly finite char-2 rank models with independent cylinder defects, and the depth-mismatched transvection pair sits in one
distinct_from:
  locally-finite-hnn-data-allow-independent-cylinder-defects: that is one locally finite vertex group with single-letter partial conjugations; this allows any countable graph of locally finite vertex groups, so forest edges amalgamate non-conjugate locally finite subgroups and products of their elements are realized as products.
  binary-locally-finite-hnn-models-violate-two-root-identity: that is the letterwise model over one locally finite base; this adds amalgamation along intersections of several locally finite subgroups.
  commuting-subgroup-witnesses-cannot-distort-defect-ranges: that is a product model of a locally finite subgroup with a commuting rank-modelled subgroup; this is the fundamental group of an arbitrary graph of locally finite groups, with no commutation hypothesis.
  fock-local-letters-extend-level-models-with-disjoint-commutation: that realizes exact commutation of disjointly supported letters but not partial conjugations across supports; this realizes partial conjugations and amalgamated products but not commutation between elements that lie in no common vertex group.
  sofic-subgroups-carry-independent-cylinder-defects: that covers relations holding in a sofic subgroup of R^x; this covers relations of the fundamental group of a graph of locally finite subgroups whatever its image in R^x, which can be all of R^x, and places the depth-mismatched pair T_(0,1), T_(1,00) in an explicit tree.
artifacts:
  - research/artifacts/mismatched-factor-graph-of-groups-firewall-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w6-mismatch-c2`; verification requested from `w4-vf-gate`) by
`graphs-of-locally-finite-groups-regular-models-proof`. Artifact Sections 1–3.

**Setting.** `R = L_(F_2)(1,2)`.
* `Y` is a countable graph of groups whose vertex groups `L_v` are countable locally finite subgroups of `R^x`.
* Each edge `e : v -> w` carries a unit `u_e` and a subgroup `K_e <= L_v cap u_e^-1 L_w u_e`, identified with
  `u_e K_e u_e^-1`. On a chosen maximal forest, `u_e = 1`.
* `pi_1(Y)` is its fundamental group.

**Statement.** There is a homomorphism `sigma : pi_1(Y) -> M^x` into a characteristic-two rank ultraproduct with:
1. the free profile `rk(sigma(alpha)) = rank(lambda_Q(alpha))/|Q|` on every finite subgroup `Q` of every vertex
   group;
2. `sigma` nontrivial, and fixed-point-free when some vertex group is infinite;
3. every `M_k(M)` directly finite, so `sigma` is a weakly finite representation.

If the unit root pairs of pairwise disjoint proper cylinders `A_1, ..., A_k` lie in one vertex group, then
`rk(sigma(D_A)) = 3/8` and `rk(sigma(D_(A_1) ... D_(A_k))) = (3/8)^k`. So `theta = 1` and `sigma(D_A) != 0`.

**Mismatched pair (artifact Section 2).**
* `a = T_(0,1)` and `c = T_(1,00)` are involutions, and `ac` has infinite order.
* `a` and `h = T_(01,00)` lie in `R_0^x`, and `c` lies in `g^-1 R_0^x g` for `g = s_10 t_1 + s_11 t_00 + s_0 t_01 ∈ V`.
* `K = R_0^x cap g^-1 R_0^x g` is block diagonal for `[1] ⊔ [00] ⊔ [01]`.
* `H = {1 + s_1 x t_00 + s_01 y t_00} ⋊ K` is locally finite and contains `c` and `h`.
* The tree `L_0 - R_0^x - H - g^-1 R_0^x g`, with the frames in `L_0`, carries the model above with `theta = 1`.

**Consequence.** Some arguments cannot establish any of these targets:
* `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`;
* `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`;
* `binary-complement-corner-has-no-weakly-finite-image`, in its representation form.

These are arguments whose inputs are only:
* relations holding in `pi_1(Y)` for one such graph containing the configurations used, including products of
  elements from different amalgamated vertex groups and conjugation chains routed through their intersections;
* rank calculus in rank ultraproducts, nontriviality and fixed-point-freeness.

In particular, using the pair as a factor together with relations routed along the tree above forces nothing.

**The broken relation (artifact Section 3).**
* The single-letter HNN extension with base `R_0^x` and a letter for `g^-1` breaks `[T_(01,00), T_(1,00)] = 1` for
  the lift `t T_(10,11) t^-1`, by Britton's lemma. `H` repairs it.
* Every relation of `R^x` follows from the Steinberg relations, each inside a finite subgroup of order at most 8, and
  from `K_2(3,R)`.
* So such an argument must use one of: a cycle of Steinberg relations whose elements generate a nonsofic subgroup
  that no graph of locally finite subgroups routes, an element of `K_2(3,R)`, or a global input about all models of
  `R^x`.
