---
rg: 2
id: mz-envelope-fp-forces-two-sided-fg-near-index-kernel
kind: claim
title: A finitely presented Mallery-Zaremsky envelope forces a finitely presented near shift group with finitely generated near-index kernel, a two-sided window that the shell route does not need
distinct_from:
  shell-germ-fp-is-an-ascending-hnn-gate: that is the shell germ gate, where R_nu finitely presented plus a ONE-sided ascending union of a finitely generated subgroup suffices; this proves that the Mallery-Zaremsky germ group needs the TWO-sided condition that ker(eta) itself is finitely generated, which is strictly stronger (for example for BS(1,2)-type near groups).
  accessible-shell-inputs-admit-no-shift-normalizing-enumeration: that excludes window width zero (s normalizing lambda(P)); this requires some finite width N with ker(eta) = <s^i lambda(P) s^-i : |i| <= N>, and excludes all enumerations where no finite width works.
  square-spiral-z2-near-shift-group-is-not-finitely-presented: that kills one explicit enumeration of Z^2 at R_nu; this gives the general necessary conditions, through which that kill transfers to the Mallery-Zaremsky envelope.
  free-shift-shell-envelopes-are-not-finitely-presented: that kills injective P*<s> near groups for the shell envelope by a presentation argument; here the same inputs die for the permutation envelope because their near-index kernel is an infinite free product.
artifacts:
  - research/artifacts/boone-higman-mz-antitwisted-germ-gate-2026-09-17.md
---

**ESTABLISHED** by `mz-two-sided-kernel-gate-sigma-proof`.

Let `P` be infinite and finitely generated, `nu : P -> N` a bijection, and use `E_nu(P)`, `R = R_nu`, `eta`,
`K = ker eta` and `F^- = {(a,b) : eta(a)+eta(b) = 0}` as in `mz-envelope-germ-group-is-an-antitwisted-fiber-product`.
Then

    E_nu(P)/FSym(N)  finitely presented   <==>   R_nu finitely presented  AND  ker(eta) finitely generated.

In BNS terms, with `R` finitely presented, the right-hand side says `[eta]` and `[-eta]` both lie in `Σ^1(R)`.
Since `K` is the union of `W_N = < s^i lambda(P) s^-i : |i| <= N >`, it is equivalent to a **two-sided finite
window**: some `N` with `s W_N s^-1 = W_N`. Then `R = K ⋊ Z`.

**Consequences.**

1. **Gates.** `E_nu(P)` finitely presented `==>` `R_nu` finitely presented and `ker eta` finitely generated. The
   compiler `infinite-shift-higman-compiler` splits into three gates, and each can fail separately:
   - (G1) the two-sided window;
   - (G2) finite presentation of the mapping torus `K ⋊ Z`;
   - (G3) lifting from germs to `E_nu(P)` itself, which is non-formal because `E_2` contains `H_2` with index 2.
2. **The Mallery-Zaremsky germ gate implies the shell germ gate.** If `E_nu(P)` is finitely presented, then for the
   same `nu` the shell germ group of `shell-germ-group-has-index-two-fiber-product` is finitely presented. So
   the permutation route is at least as hard as the shell route at the germ level, for every enumeration.
3. **Transferred kills.**
   - For the square spiral enumeration of `Z^2`, `E_nu(Z^2)` is not finitely presented.
   - Whenever `P*<s> -> R_nu` is injective and `P ≠ 1`, `E_nu(P)` is not finitely presented.
   - More generally, every enumeration whose near group is only an ascending HNN extension over a finitely
     generated base in one direction dies.

No sufficiency of (G1) and (G2) for finite presentation of `E_nu(P)` itself is asserted.
