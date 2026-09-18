---
rg: 2
id: fp-simple-q-algebras-embed-in-fp-simple-rings
kind: claim
title: A Q-algebra embeds in a finitely presented simple ring exactly when it embeds in a finitely presented simple Q-algebra
distinct_from:
  leavitt-resolvent-ring-is-fp-simple-of-char-zero: that is one finitely presented simple ring containing Q; this uses it, through its centre Q, to turn every finitely presented simple Q-algebra into a finitely presented simple ring.
  algebra-boone-higman-conjecture: that is the envelope question over a field K, with finite presentation over K; this shows that for K = Q the same question with finite presentation over Z is equivalent.
  fp-simple-ring-of-characteristic-zero-exists: that is the existence of one such ring; this is a transfer principle for all Q-algebras.
---

**ESTABLISHED** through `fp-simple-q-algebras-embed-in-fp-simple-rings-proof` (lane proof,
not independently reviewed).

**Statement.**
1. The centre of the ring `R_L` of `leavitt-resolvent-ring-is-fp-simple-of-char-zero`
   is `Q`.
2. Let `S` be a simple `Q`-algebra that is finitely presented as a `Q`-algebra. Then
   `R_L ⊗_Q S` is a finitely presented simple ring, and `S -> R_L ⊗_Q S`, `s ↦ 1 ⊗ s`,
   is a unital embedding.
3. For a `Q`-algebra `A`, possibly non-unital, the following are equivalent:
   - `A` embeds in a finitely presented simple ring;
   - `A` embeds in a finitely presented simple `Q`-algebra.

**Consequence.** For `Q`-algebras, Boone--Higman-type envelope questions have the same
answer whether finite presentation is taken over `Z` or over `Q`. In particular:
- `char-zero-ring-boone-higman` is equivalent to the case `K = Q` of
  `algebra-boone-higman-conjecture`;
- every finitely presented simple `Q`-algebra in the repository gives a finitely presented
  simple ring. Examples are `L_Q(1,2)^(⊗ j)` and the envelopes of
  `polynomially-representable-algebras-have-fp-simple-envelopes` at `K = Q`.
