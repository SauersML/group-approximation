---
rg: 2
id: frobenius-bounded-corona-is-stably-finite
kind: claim
title: The matrix corona modulo spectrally bounded-rank sequences is stably finite and receives every Frobenius-bounded model
distinct_from:
  leavitt-unit-frobenius-bounded-models-are-trivial: that is the open rigidity statement for Frobenius-bounded models of the binary Leavitt unit group; this is the general quotient algebra such models map into, proved stably finite, with no triviality conclusion for any group.
---

**ESTABLISHED.**  Let `k_L -> infinity`, let `P = prod_L M_(k_L)(C)` be the
bounded sequences with the sup norm, write `s_i(X)` for the singular values of
a matrix in decreasing order, `rank_(>t)(X) = #{i : s_i(X) > t}`,
`||X||_F = Tr(X^* X)^(1/2)` and `||X||_(2,k)^2 = (1/k) Tr(X^* X)`.  Put

```text
K = { (X_L) in P :  sup_L rank_(>t)(X_L) < infinity  for every t > 0 }.
```

1. `K` is a closed two-sided `*`-ideal of `P`.  It contains the norm-null
   sequences `bigoplus_L M_(k_L)(C)`, and every `(X_L) in K` satisfies
   `||X_L||_(2,k_L) -> 0`.
2. `Q = P / K` is stably finite.
3. If a group `G` and maps `V_L : G -> U(k_L)` satisfy

   ```text
   limsup_L ||V_L(gh) - V_L(g) V_L(h)||_F < infinity      for all g, h in G,
   ```

   then `g |-> [V_L(g)]` is a homomorphism `G -> U(Q)`, and every tracial
   state `lim_omega tr_(k_L)` of `P` vanishes on `K` and so factors through `Q`.
4. Stable finiteness of a target algebra cannot by itself force such a
   homomorphism to be trivial: every group `G` embeds in the unitary group of
   `C*_r(G)`, which is stably finite because its canonical trace is faithful.
   In particular no argument using only (2) can prove
   `leavitt-unit-frobenius-bounded-models-are-trivial`.

This firms up the quotient sketched in that node.  Proof:
`frobenius-bounded-corona-stable-finiteness-proof`.  No novelty is claimed;
the argument is elementary.

## Attempts

Established; see `frobenius-bounded-corona-stable-finiteness-proof`.
