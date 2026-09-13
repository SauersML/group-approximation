---
rg: 2
id: outer-torelli-groups-not-fp-for-infinitely-many-ranks
kind: claim
title: "For infinitely many n the Torelli group of Out(F_n) is not finitely presented"
---

Let `T_n = ker(Out(F_n) -> GL_n(Z))`. The claim: `T_n` is not finitely presented
for infinitely many `n`. It is the no-answer for the Out family of Zaremsky
Problem 3.1 (`zaremsky-3-01-out-torelli-resolved`), and the negation of
`outer-torelli-groups-fp-for-large-rank`. By `ia-n-fp-iff-outer-torelli-fp` it is
equivalent to `ia-automorphism-groups-not-fp-for-infinitely-many-ranks`.

The only rank known to fail is `n = 3` (Krstić–McCool; recovered in
Bestvina–Bux–Margalit, arXiv:math/0603177, from `H_2(T_3; Z)` being infinitely
generated).

## Attempts

- **Infinitely generated second homology.** A no-answer would follow from
  `H_2(T_n; Z)` infinitely generated for infinitely many `n`. The known infinite
  generation results sit in other degrees: `H_{2n-4}(T_n; Z)` (BBM Main Theorem
  (2)), and Smillie–Vogtmann's result that the total homology `H_*(T_n; Z)` is
  not finitely generated for `2 < n < 100` or for even `n > 2` (via rational Euler
  characteristics, as summarized in BBM §1). Neither says anything about
  degree 2 when `n >= 4`. Where it dies: the only degree-2 finiteness statement for
  the Aut version is module-finiteness (Day–Putman), which is consistent with
  either answer.
- **Obstruction beyond H_2.** Finite presentability implies type `FP_2` over `Z`
  (the relation module is finitely generated), which is stronger than finite
  generation of `H_2`. A no-answer could come from a relation module that is not
  finitely generated even when `H_2` is. No candidate invariant has been
  identified yet.
