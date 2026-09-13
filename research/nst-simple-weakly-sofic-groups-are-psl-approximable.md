---
rg: 2
id: nst-simple-weakly-sofic-groups-are-psl-approximable
kind: claim
title: Finitely generated perfect groups are not approximable by finite soluble groups, and simple weakly sofic groups are approximable by the groups PSL_n(q)
distinct_from:
  nikolov-segal-generation-by-conjugates: that is the finite-group generation theorem; this is its application to metric approximation of abstract groups, by Nikolov, Schneider and Thom.
  simple-group-psl-width-is-finite-field-linear-soficity: that converts weak models into PSL_n(q) with any invariant lengths into linear soficity over finite fields; this produces such weak models from any weak soficity of a simple group.
---

**ESTABLISHED (literature import).** N. Nikolov, J. Schneider and A. Thom, *Some remarks on finitarily approximable
groups*, arXiv:1703.06092v2.

- **Definition 1.** For a class `𝒞` of finite groups, an abstract group `G` is `𝒞`-approximable if there is
  `delta: G \ {1} -> (0, ∞]` such that for every finite `S ⊆ G` and `eps > 0` there are `H in 𝒞`, an invariant length
  function `l_H` on `H` and a map `phi: S -> H` with `phi(1) = 1`, `d_H(phi(g)phi(h), phi(gh)) < eps` when
  `g, h, gh in S`, and `l_H(phi(g)) >= delta_g` for `g in S \ {1}`. By their Example 1, `Fin`-approximable is weakly sofic.
- **Theorem 1.** *Any non-trivial finitely generated and perfect group is not **Sol**-approximable.* Here **Sol** is the
  class of finite solvable groups.
- **Theorem 4.** *Any non-trivial finitely generated **Fin**-approximable group has a non-trivial **PSL**-approximable
  quotient. In particular, every simple **Fin**-approximable group is **PSL**-approximable.* Here **PSL** is the class of
  the simple groups `PSL_n(q)`, `n >= 2`, `(n, q) != (2, 2), (2, 3)`.

The proofs use Segal's theorem on finite soluble groups and Nikolov--Segal, Theorem 1.1 and 1.2 style generation
results, with Liebeck--Shalev for Theorem 4 (their abstract and Section 1).

Source status: `nst-simple-weakly-sofic-groups-are-psl-approximable-citation`.
