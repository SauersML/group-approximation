---
rg: 2
id: kl-simple-failure-universal-cover-collapses-when-centralized
kind: claim
title: The universal central extension of a simple counterexample collapses in the centralized adjunction
distinct_from:
  kl-counterexample-can-be-superperfect-quasisimple: that asks for a failure over a superperfect quasisimple group in the plain adjunction and is open; this proves a collapse only after the center is forced to commute with the new letter.
  central-extension-kl-schur-criterion: that assumes the quotient adjunction injects and derives injectivity for the central extension; this starts from a quotient adjunction that kills the whole coefficient group.
  kl-counterexample-can-be-two-generator-simple: that produces the simple counterexample; this passes to its universal central extension.
---

Let `S` be a two-generator nonabelian simple group, `w in S * <t>` with
`deg_t(w) = m != 0`, and suppose `S -> (S * <t>)/<<w>>` is not injective.
Write `S = F/R` with `F` free of rank two, and put
`S^ = [F,F]/[F,R]` and `A = (R cap [F,F])/[F,R]`.

1. **The universal cover.**
   * `S^` is two-generated, superperfect (`H_1 = H_2 = 0`) and quasisimple.
   * `Z(S^) = A = H_2(S; Z)`, `S^/A = S`, and every proper normal subgroup of
     `S^` lies in `A`.
   * If `S` is finitely presented, so is `S^`.
2. **Centralized collapse.** For every lift `w^ in S^ * <t>` of `w`, all of
   `S^` dies in `(S^ * <t>)/<<w^, [A, t]>>`.
3. **The plain adjunction.** The kernel of `S^ -> (S^ * <t>)/<<w^>>` either lies
   in `A` or is all of `S^`.
   * In the second case `S^` is a counterexample with `K_2(S^, w^) <= H_2(S^) = 0`.
   * Whether some simple failure lifts to that case is the OPEN
     `kl-counterexample-can-be-superperfect-quasisimple`.

Item 1 is the textbook universal central extension. The route derives it from
Hopf's formula alone. No novelty is claimed.

DERIVATION
kl-superperfect-quasisimple-counterexample-proof
