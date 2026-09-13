---
rg: 2
id: lodha-moore-group-character-simplex
kind: claim
title: The extreme characters of the Lodha--Moore group are the regular character and the characters of its abelianization Z^3
distinct_from:
  thompson-f-character-simplex: that classifies the characters of Thompson's F by importing Dudko--Medynets at F_(2,1); this proves the same shape for the Lodha--Moore group G_0, which is not a Higman--Thompson group, by applying their general theorems to the action of G_0' on the real line.
  lodha-moore-sofic-iff-relator-system-unstable: that consumes this classification to turn nonsoficity of G_0 into permutation stability of its relators; this is the classification itself.
---

**ESTABLISHED (unreviewed).**  Let `G_0 = <a, b, c>` be the Lodha--Moore group
and `pi : G_0 -> Z^3` its abelianization, with `pi(a), pi(b), pi(c)` a basis.

1. `G_0'` has no proper characters.
2. Every indecomposable character of `G_0` is either the regular character, or
   `g -> rho(pi(g))` for a homomorphism `rho : Z^3 -> T`.
3. Hence every character of `G_0` has the form `t tau_reg + (1 - t) chi_ab`, with
   `t in [0, 1]` and `chi_ab` a character through `pi`.  In particular every
   character takes the single value `1 - t` on `G_0' \ {e}`.

**Mechanism.**  `F' <= G_0'` acts on the real line by a topological conjugate of
the dyadic piecewise linear action of `F_(2,1)'` on `(0,1)`.  So the
Dudko--Medynets dyadic compressibility lemma transports to `G_0'`, whose elements
are compactly supported.  Their simple-group theorem gives item 1, and their
extension theorem, with `R = G_0'`, gives item 2.

**Novelty.**  Not checked beyond the repository; no literature search on
characters of the Lodha--Moore group was run.

Derivation: `lodha-moore-character-simplex-via-dudko-medynets`.
