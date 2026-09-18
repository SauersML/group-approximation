---
rg: 2
id: product-tree-lattices-surjunctive-via-envelope-transfer
kind: route
title: Induce any strict automaton on a product-of-trees lattice into a strict measured controlled automaton on a product of free products of involutions
target: every-cocompact-product-of-trees-lattice-is-surjunctive
requires:
  - measured-controlled-surjunctivity-is-envelope-invariant
  - products-of-two-virtually-free-groups-controlled-surjunctive
---

A decomposition into two prerequisites, each of which can fail on its own.

1. **E1, ESTABLISHED** (`measured-controlled-surjunctivity-is-envelope-invariant`). For discrete
   cocompact `Gamma, Lambda` in a unimodular group with a basis of compact open subgroups, a strict
   automaton on `Gamma` induces a strict controlled automaton for `Lambda` over `H/Gamma` with Haar
   probability. More generally, the measured-controlled property passes between `Gamma` and
   `Lambda`.
   - *How it could have failed.* Through fundamental domains that are not clopen, or through
     cocycles that are not locally constant. Neither happens when `H` is totally disconnected.
2. **E2, OPEN** (`products-of-two-virtually-free-groups-controlled-surjunctive`).
   `Lambda = C_2^(*p) x C_2^(*q)` is measured-controlled surjunctive.
   - *How it can fail.* A strict controlled automaton over a measured base not induced from any
     lattice.
   - *Why it is not soficity in disguise.* E2 asks for no sofic model of any action.

**Verification of the hypotheses for `L = Aut(T_p) x Aut(T_q)`, `p, q >= 3`.**

- *Compact open basis.* In the permutation topology, the pointwise stabilizers of finite vertex
  sets are compact open subgroups and form a neighbourhood basis of `1`. `L` is second countable.
- *Unimodular.* The modular function is a continuous homomorphism to `R_>0`, so it is trivial on
  compact subgroups. Every element of `Aut(T_p)` is a product of edge inversions, which lie in
  compact edge stabilizers, times an element of a vertex stabilizer.
  - This holds because a path of inversions moves any vertex to any other: for every edge, the
    regular tree has an automorphism swapping its endpoints.
  - So `Delta = 1` on `Aut(T_p)`, and likewise on the product.
- *A residually finite partner.* `C_2^(*p)` acts simply transitively on the vertices of its Cayley
  tree `T_p`, so `Lambda = C_2^(*p) x C_2^(*q)` acts simply transitively on the vertices of
  `T_p x T_q`.
  - `Lambda` meets vertex stabilizers trivially, so it is discrete.
  - `L = Lambda K_v`, so it is cocompact.

**Argument.** Let `Gamma <= L` be discrete cocompact. By E2, `Lambda` is MCS. By E1 part 3,
`Gamma` is MCS. By E1 part 4, `Gamma` is surjunctive.

**What this changes.**
- A strict cellular automaton on Radu's lattice, or on any Burger–Mozes or Wise lattice, now forces
  a strict controlled automaton for the residually finite, linear, Haagerup group
  `C_2^(*p) x C_2^(*q)`, over the Cantor space `L/Gamma` with Haar probability.
- The counterexample programs `radu-bmw-lattice-nonsurjunctive` and
  `strict-automaton-on-lattice-in-product-of-trees` must therefore also defeat every Garden-of-Eden
  argument that uses the measure on this base.
- The same transfer applies to cocompact lattices in any totally disconnected envelope that also
  contains a residually finite cocompact lattice.

**Weak link.** E2. The relative sofic-entropy proof of E2 consumes `F_2 x F_2 ∈ 𝒮`, which already
gives soficity of the lattices. So the route gains over `radu-bmw-lattice-sofic-from-f2xf2-paunescu-class`
only through a measured Garden-of-Eden argument that builds no finite models of the base.
