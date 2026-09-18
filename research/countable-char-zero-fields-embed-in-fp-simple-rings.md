---
rg: 2
id: countable-char-zero-fields-embed-in-fp-simple-rings
kind: claim
title: Every countable field of characteristic zero embeds in a finitely presented simple ring
distinct_from:
  field-envelopes-pass-to-algebraic-closures: that settles the countable fields of finite transcendence degree; this asks for all countable fields, and what remains open is infinite transcendence degree.
  char-zero-ring-boone-higman: that asks for every finitely generated Q-algebra with solvable word problem; this asks for countable fields, which are not finitely generated.
  gl-n-q-embeds-in-fp-simple-group: that is the group question for GL_n(Q); this is a ring question.
---

**OPEN.** Every countable field `K` of characteristic zero embeds in a finitely presented
simple ring. Equivalently, by `fp-simple-q-algebras-embed-in-fp-simple-rings`, `K` embeds
in a finitely presented simple `Q`-algebra.

## What is known

- **Finite transcendence degree: yes** (`field-envelopes-pass-to-algebraic-closures`).
  This covers `Q̄`, all algebraic extensions of `Q`, and all algebraic extensions of
  `Q(t_1..t_k)`.
- **Reduction.** The claim is equivalent to its single case
  `K_∞ = Q(t_1, t_2, ...)`.
  - A countable field of characteristic zero has a countable transcendence basis, so it
    embeds in the algebraic closure of `K_∞`.
  - That closure embeds as soon as `K_∞` does, by the transfer in
    `field-envelopes-pass-to-algebraic-closures`, part 1.
- **No decidability obstruction.** A finitely presented simple ring has solvable word
  problem (`fp-simple-algebras-have-solvable-word-problem`), but every finitely generated
  subring of a field is a finitely generated commutative ring, whose word problem is
  solvable. So no subfield is excluded on these grounds.

## Attempts

1. **Registers over central transcendentals (2026-09-17, lane `gq-ring-fp-simple`).**
   *Dies* at infinite transcendence degree. The construction of
   `rational-function-fields-embed-in-fp-simple-rings` uses `k` central transcendentals
   and one resolvent. Every Leavitt--Nekrashevych completion `O_ψ` over a finitely
   generated polynomial ring `Π`, localized, has these properties:
   - its base `B` has finite transcendence degree;
   - every commutative subfield of its core `colim M_(d^n)(B)` is algebraic over `Frac(B)`,
     by Cayley--Hamilton.

   So a copy of `K_∞` would need elements of nonzero degree, or a base `B` that is not a
   localization of a finitely generated polynomial ring.
2. **Possible routes (not attempted).**
   - Registers whose *index* is dynamic, e.g. a letter that shifts
     `t_i ↦ t_(i+1)` inside a noncommutative base.
   - Transcendental power-series constants, such as `e^(t^m)`, defined by finitely many
     differential relations `D E_m = E_m D + m t^(m−1) E_m`, transported along the
     letters. The functions `e^(t^m)` are algebraically independent over `Q(t)`.
   - A general algebra Boone--Higman theorem over `Q`, `char-zero-ring-boone-higman`,
     for a finitely generated decidable algebra containing `K_∞`, for example one from
     Bokut's two-generator embedding. Whether that algebra is decidable is unchecked.
