---
rg: 2
id: rips-segev-port-data-cannot-exclude-balanced-divisors
kind: claim
title: The Rips--Segev graph is itself a balanced port configuration, so extreme-port and extremal-coset arguments cannot exclude two-layer zero divisors with equal degree ranges
distinct_from:
  rips-segev-core-large-gap-two-layer-elements-are-regular: that proves regularity when an offset leaves the line-difference range; this proves the same port method cannot settle offsets (0,0), and that its relation step cannot settle offsets in [-10, 99900] for Steenbock's graphs.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question; this is an obstruction to one family of approaches to it.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-port-data-cannot-exclude-balanced-divisors-proof`.

**Setting.**  Everything is as in `rips-segev-core-large-gap-two-layer-elements-are-regular`.
- `K = K_Gamma` is the core group of a generalized Rips--Segev graph `Gamma` with `Gr'_*(1/8)`.
- A *port configuration with offsets `(d_+, d_-)`* is a finite family of left `<a>`-cosets `T` with nonempty
  finite `Out_T, In_T ⊆ T` satisfying:
  - (P1) `⊔ In_T = (⊔ Out_T) b`;
  - (P2) `max Out_T = max In_T · a^{d_+}` and `min Out_T = min In_T · a^{d_-}`.
- If `alpha (u + w b) = 0` with `alpha != 0`, there is a configuration with offsets `(w_+ - u_+, w_- - u_-)`.

**Theorem.**
1. **Balanced realization.**  Suppose every line endpoint position `0, C_i` is both a source and a target of
   `b`-edges.  This holds for Steenbock's explicit graphs, where `S_i = {0, O_i1, O_i2, C_i}` and
   `T_i = {0, I_i1, I_i2, C_i}`.  Then the image of `Gamma` in `K` is a port configuration with offsets `(0, 0)`.
   - So no argument that derives a contradiction from (P1) and (P2) alone can show that an element
     `u + w b` with `u_+ = w_+` and `u_- = w_-` is a non-zero-divisor.  This includes extremal-coset lemmas,
     neighbour counts, degree gaps and walks of extreme ports.
   - Examples of such elements: `1 + a + (1 - a) b` and `1 + a + (1 + lambda a) b`.
2. **The relation step cannot be sharpened.**  For Steenbock's explicit graphs:
   - the cycles of `x_2`-edges give positive relations `prod_k b a^{C_{l_k} - I_{l_k 2}} = 1`, all exponents
     `>= 99900`;
   - the cycles of `x_1`-edges give `prod_k b a^{-I_{l_k 1}} = 1`, all exponents `<= -10`.

   So for `d_±` in `[-10, 99900]`, all four walk conclusions of the walk lemma are realized by actual relations of
   `K`.  No lemma about positive relations can turn a walk into a contradiction in that range.

**Consequence for the brief.**
- The extremal-coset step ("some coset of the configuration has at most one `b`-neighbour") cannot come from port
  data at offsets `(0, 0)`, because `Gamma`'s configuration is a counterexample to any such purely combinatorial
  conclusion.
- The balanced case needs the coefficient identities `alpha_T w = g_T`, `alpha_T u = f_T` with `f(x) = - g(x b^{-1})`,
  not only supports.

**Exact failing step.**  Moving from "a port configuration exists" to a contradiction.  For offsets `(0, 0)`,
`Gamma` supplies a configuration.
