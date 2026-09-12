---
rg: 2
id: fpbs-rd-quotient-weighted-bubble-gives-critical-l2
kind: claim
title: A polynomially weighted critical fibre bubble over a rapid-decay quotient gives critical L2 boundedness
distinct_from:
  fpbs-hyperbolic-quotient-fibre-estimates-l2-gap: that derives the L2 gap from the unweighted uniform fibre bubble together with the far-halfspace share and the mean-field susceptibility bound; this needs one weighted critical fibre bubble and property RD of the quotient, with no halfspace estimate and no susceptibility exponent.
  fpbs-tree-projected-sphere-bubble-l2-equivalence: that is an exact equivalence for tree-projected generating sets, proved through cut-fibre submultiplicativity; this is a sufficient condition over any quotient with rapid decay, where no cut structure is assumed.
  fpbs-fibre-summed-connectivity-operator: that compares the connectivity operator with its fibre sum on the quotient; this bounds that fibre sum itself through the rapid decay inequality.
artifacts:
  - research/artifacts/fpbs/docs/rd-weighted-fibre-bubble-criterion.md
---

**ESTABLISHED (implication).** Let `Gamma` be finitely generated, `S` a finite
symmetric generating set, `H` any normal subgroup, and `Q = Gamma/H` with word
length `|.|` from `pi(S)`. Suppose `Q` has the Rapid Decay property with
constants `C, D`: `||lambda_Q(f)|| <= C (1+R)^D ||f||_2` for every finitely
supported `f` in `B_Q(R)`. Put `sigma_p(q) = E_p|K_o ∩ q|` for cosets `q`. If

```text
W_D = sum_{q in Q} (1+|q|)^(2D+2) sigma_(p_c)(q)^2  <  infinity,
```

then on `Cay(Gamma,S)`

```text
||T_(p_c)||_{2->2}  <=  C (pi/sqrt 6) W_D^(1/2)  <  infinity,
```

and hence `p_c < p_{2->2} <= p_u`.

The proof uses neither amenability of `H`, nor the far-halfspace share, nor the
mean-field susceptibility bound. The premise can hold only when `Q` is
nonamenable: for amenable `Q` with RD, `||S_(p_c)|| = chi_(p_c) = infinity`.
Proof: artifact Section 1.
