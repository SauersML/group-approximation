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
* **2026-09-19, swarm-0917-w17-w17-bs-last1, minimal-counterexample: can any
  supporting-set family replace WPD?** **Refuted on the central part of the
  class; the claim stays OPEN.**
  (`fpbs-cs-set-family-hypothesis-fails-infinite-centre`.)
  - *Question.* The entry above says the WPD remedy needs acylindricity. That
    left open whether some other family `H(g)` could satisfy the hypothesis of
    Choi–Seo `thm:hutchcroft1plus2`, their only route to (Gamma1). Such a
    family might be built from the hyperbolic quotient.
  - *Answer.* No. A disjoint short translate of a set containing `a^-1 A`
    forces `a h a^-1 ∉ A A^-1`. Then `A = E ∪ D_R(E)`, with `D_R(E)` the
    conjugates of the `R`-ball by `E`, defeats every family whenever
    `#(D_R(E) \ E) < #E`.
  - *Where it applies.* When the kernel contains an infinite central
    subgroup, central `E` gives `D_R(E) = B(R)`. So the hypothesis fails for
    every family, every `R` and every generating set, on:
    - `F_2 x Z`;
    - central extensions of hyperbolic groups;
    - Seifert-fibred groups with central fibre;
    - `Lambda x Z^k`.
  - *Where it dies.* The named invariant is conjugation expansion,
    `#(D_R(E) \ E) >= #E` for every finite `E`. It fails at the hypothesis of
    `thm:hutchcroft1plus2`, before Appendix A of [CS] begins. Any route to
    (Gamma1) here must count fibres instead, as
    `fpbs-fibre-bubble-forces-mean-field-susceptibility` does.
  - *What is left open.* Kernels with trivial or finite centre, such as
    `Z^2 ⋊ F_2`, `F_2 x F_2`, and `F_2 x` a lamplighter. There the test does
    not fire; the lamplighter compresses at `R = 1` but not at `R = 2`.
