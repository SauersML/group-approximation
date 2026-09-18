---
rg: 2
id: fp-linear-hosts-of-sl-q-have-wild-h3-quotients
kind: claim
title: A finitely presented group between finitary SL(Q) and SL(Q)·Mon has a quotient with infinitely generated H_3
distinct_from:
  split-finitary-sl-q-extensions-are-not-fp: that treats the split case by a direct Steinberg-group argument; this covers non-split extensions too, at the price of a conclusion about H_3 of the quotient.
  weighted-monomial-hosts-of-sl-q-need-wild-stabilizers: that constrains point stabilizers of the monomial part at the finite-generation level; this constrains the homology of the quotient at the finite-presentation level.
---

**ESTABLISHED** through `fp-linear-hosts-of-sl-q-have-wild-h3-quotients-proof`. This is a
lane proof; it has not been independently reviewed. The method is the standard
Lyndon–Hochschild–Serre argument, and no priority is claimed.

## Statement

Notation as in `split-finitary-sl-q-extensions-are-not-fp`.

1. **Linear hosts.** Let `Γ` be finitely presented with
   `SL_X(Q) <= Γ <= SL_X(Q)·Mon(X) <= GL(Q^(X))`. Then `H_3(Γ/SL_X(Q); Z)` is not finitely
   generated. In particular:
   - `Γ/SL_X(Q)`, which is `M/(M ∩ SL_X(Q))` for `M = Γ ∩ Mon(X)`, is not of type `FP_3`;
   - the extension `1 -> SL_X(Q) -> Γ -> Γ/SL_X(Q) -> 1` does not split.
2. **General form.** Let `Γ` be a group with `H_2(Γ; Z)` finitely generated (for example
   `Γ` finitely presented), and let `N ◁ Γ` be perfect. Then `H_2(N; Z)_(Γ/N)` modulo the image
   of a subgroup of `H_3(Γ/N; Z)` embeds in `H_2(Γ; Z)`. So if the coinvariants
   `H_2(N)_(Γ/N)` are not finitely generated, then `H_3(Γ/N; Z)` is not finitely generated,
   and the extension does not split.

## Consequence for the root and Problem 2.7

Any finitely presented overgroup of `GL_n(Q)` built as "finitary `SL(Q)` together with
weighted permutations" has to use a quotient `Γ/SL_X(Q)` with infinitely generated third
homology. Thompson-type, Houghton-type and Baumslag-type quotients that are of type `FP_3`
are therefore excluded, split or not. This complements
`weighted-monomial-hosts-of-sl-q-need-wild-stabilizers`, which excludes monomial parts with
finitely generated point stabilizers already at the level of finite generation.

## Not claimed

- Hosts with a normal `SL_X(Q)` acted on by automorphisms that are not induced by
  `SL_X(Q)·Mon(X)`. Part 2 still applies whenever the coinvariants of `K_2(Q)` are not
  finitely generated. Whether every automorphism of `SL_inf(Q)` acts on `K_2(Q)` through a
  finite group is not settled here.
- `E_(n+1)(R_Toep)`, whose generators are not of this form.
