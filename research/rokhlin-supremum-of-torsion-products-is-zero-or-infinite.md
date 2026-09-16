---
rg: 2
id: rokhlin-supremum-of-torsion-products-is-zero-or-infinite
kind: claim
title: For an amenable group P with finite subgroups of unbounded order, the Rokhlin supremum of P x G is 0 or infinity, and it is infinity exactly when G has infinite supremum
distinct_from:
  seward-per-group-rokhlin-entropy-of-bernoulli-shifts: its item 3 is only the zero side, h_sup(P x G) = 0 when h_sup(G) is finite; this adds the infinite side for amenable P, so that the side of the dichotomy is decided by INF(G) for every single G.
  rokhlin-supremum-dichotomy-with-centralized-self-copies: that gets a zero-or-infinity dichotomy only for groups containing their own square; this gets it for every product P x G with no self-copy hypothesis on G, and says which side holds.
  rokhlin-maximality-ascends-co-amenable-subgroups: that is the general ascent theorem along Følner co-amenable subgroups; this applies it to the factor 1 x G of P x G and combines it with Seward's vanishing theorem.
  bernoulli-per-copy-rokhlin-entropy-is-zero-or-full: that says per-copy Bernoulli Rokhlin entropy of one group is 0 or log q; this says the finite-entropy supremum of a product group is 0 or infinity, with the criterion INF(G).
  tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy: that is the dichotomy for one fixed finitely presented host containing its own square; this is the dichotomy for all products with a torsion-rich amenable factor.
---

Let `G` be a countably infinite group. Let `P` be a countable amenable group containing finite subgroups of
unbounded order, for example `P = ⊕_(n ≥ 1) Z/nZ`. Write `h_sup` for Seward's Rokhlin entropy supremum
(`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`). Then:

1. `h_sup(P × G) ∈ {0, ∞}`;
2. `h_sup(P × G) = ∞` if and only if `h_sup(G) = ∞`;
3. the following are equivalent:
   - some free ergodic p.m.p. action of `P × G` has positive Rokhlin entropy, i.e. POS(`P × G`);
   - INF(`P × G`);
   - RBS(`P × G`);
   - INF(`G`).

**Proof sketch.**
- **Zero side.** If `h_sup(G) < ∞`, Seward's Theorem 1.11 gives `h_sup(P × G) = 0`.
- **Infinite side.** If `h_sup(G) = ∞`, then `G` is Rokhlin-maximal at every `q` (Theorem 1.10). The subgroup
  `1 × G` is infinite and co-amenable in the Følner sense: its coset space is `P` with right translations. So
  `P × G` is Rokhlin-maximal by `rokhlin-maximality-ascends-co-amenable-subgroups`, and Theorem 1.10 for `P × G`
  gives `h_sup(P × G) = ∞`.
- **Item 3.** It follows from `positive-rokhlin-entropy-action-gives-positive-supremum` and Seward's chain
  INF ⟹ RBS ⟹ POS.

The full proof is in [[rokhlin-supremum-torsion-products-proof]].

**Use.** For every countably infinite `G`, INF(`G`) ⟺ POS(`P × G`). So maximal Bernoulli Rokhlin entropy of a
single group is equivalent to the existence of **one** positive-entropy free ergodic action of an auxiliary group.
If `G` belongs to a class closed under `G ↦ P × G`, such as groups with an amenable normal subgroup and a fixed
quotient, then POS for the class is equivalent to INF for the class
(`amenable-kernel-ascent-from-positive-entropy-on-products`).

Nothing here is a new lower bound. The theorem transports the question; it does not decide which side any
nonsofic `G` lies on. No novelty is claimed: the ingredients are Seward's theorems and Theorem A.
