---
rg: 2
id: fpbs-hyperbolic-quotient-every-generating-set
kind: claim
title: Every Cayley graph of a group with a hyperbolic quotient by an infinite normal subgroup has strict thresholds
distinct_from:
  fpbs-product-every-generating-set: that is the direct-product class H x K with H nonamenable; this is the class with an infinite normal subgroup and non-elementary hyperbolic quotient, which contains F_2 x Z and hyperbolic x K but not products with non-hyperbolic factors, and also contains non-split central extensions.
  fpbs-seifert-fibred-every-generating-set: that is the 3-manifold instance; this is the group-theoretic class containing it.
  fpbs-amenable-wq-normal-class-nonuniqueness: that is the class with an infinite amenable wq-normal subgroup and no geometric hypothesis on a quotient; this requires a hyperbolic quotient but allows nonamenable kernels such as F_2 in F_2 x F_2.
  fpbs-sc-choi-seo: that covers acylindrically hyperbolic groups; a group with an infinite normal subgroup of infinite index and hyperbolic quotient, when the kernel is amenable, is never acylindrically hyperbolic.
---

**OPEN.** Let `Gamma` be finitely generated with an infinite normal subgroup
`H` such that `Gamma/H` is non-elementary word hyperbolic. Then for every
finite symmetric generating set `S` of `Gamma`,

```text
p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S)).
```

The class contains:
* `F_2 x Z`, Choi–Seo arXiv:2508.08932 Question 1.3;
* fundamental groups of closed Seifert-fibred 3-manifolds with hyperbolic base,
  Question 1.6;
* `Lambda x K` for any non-elementary hyperbolic `Lambda` and infinite finitely
  generated `K`, including `F_2 x F_2`;
* central extensions of hyperbolic groups.

## Attempts

* **Two fibre estimates.** Route `fpbs-hyperbolic-quotient-via-fibre-estimates`
  carries Hutchcroft's hyperbolic proof over to the quotient. It proves the
  implication (`fpbs-hyperbolic-quotient-fibre-estimates-l2-gap`) and leaves
  two open premises:
  * the uniform fibre bubble, `fpbs-hyperbolic-quotient-uniform-fibre-bubble`;
  * the far-halfspace share, `fpbs-hyperbolic-quotient-far-halfspace-share`.

  **Where it stops:** both premises are open (see their Attempts).
* **Relative susceptibility, for amenable `H`.**
  `fpbs-amenable-wq-normal-class-nonuniqueness` reduces the gap to finiteness of
  `E_p|K_o ∩ H|` just above `p_c`. **Where it stops:** that premise is open, and
  the hyperbolic quotient gives no direct handle on it.
* **Choi–Seo and Hutchcroft.** The halfspace hypothesis fails on
  fibre-concentrated sets, and the groups are not acylindrically hyperbolic
  when `H` is amenable of infinite index. **Where it dies:** the WPD remedy needs
  acylindricity.
* **One weighted fibre estimate.** Route
  `fpbs-hyperbolic-quotient-via-weighted-fibre-bubble`:
  * rapid decay of `Q` (`hyperbolic-groups-have-property-rd`) bounds the fibre
    operator `S_(p_c)` by a polynomially weighted critical fibre bubble;
  * `||T_(p_c)|| <= ||S_(p_c)||` then gives `p_c < p_{2->2}`;
  * no far-halfspace share and no susceptibility bound are used.

  **Where it stops:** the weighted premise
  `fpbs-rd-quotient-weighted-critical-fibre-bubble` is open. For amenable `H`
  the unweighted bubble is necessary for the L2 gap
  (`fpbs-amenable-kernel-l2-gap-forces-fibre-bubble`), so the gap sits between
  the two bubbles.
