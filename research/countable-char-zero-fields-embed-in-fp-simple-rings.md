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
   - Transcendental power-series constants, such as `e^(t^m)`, defined by finitely many
     differential relations `D E_m = E_m D + m t^(m−1) E_m`, transported along the
     letters. The functions `e^(t^m)` are algebraically independent over `Q(t)`.
   - A general algebra Boone--Higman theorem over `Q`, `char-zero-ring-boone-higman`,
     for a finitely generated decidable algebra containing `K_∞`, for example one from
     Bokut's two-generator embedding. Whether that algebra is decidable is unchecked.
3. **Shift tape over a Thompson crossed product (2026-09-18, lane `gq-ring-fp-simple`,
   suggested by the coordinator).** The finite presentation of the tape works, but the
   evaluation mechanism dies.
   - **Setting.** Index the variables by the dyadic rationals `I ⊂ (0,1)`. Let Thompson's
     group `F` act on `I` and on `Z[T_I]` by permuting variables.
   - **The tape is finitely presented.** The crossed product `Z[T_I] ⋊ F` is presented by
     `F`, one generator `T_p`, `[T_p, g] = 0` for generators `g` of `Stab_F(p)`, and
     `[T_p, T_q] = 0` for one representative of each of the two orbits of `F` on pairs of
     distinct dyadics. That is finitely many relations, since `Stab_F(p) ≅ F × F` is
     finitely generated and `F` is transitive on increasing pairs.
   - **The shift is consistent.** A shift letter `sh` with `h s_sh = s_sh φ(h)` and
     `T_p s_sh = s_sh T_(p/2)` is compatible for all variables at once. Here `φ(h)` is `h`
     conjugated into `[0, 1/2]` and extended by the identity, so `θ(x) = x/2` is
     `φ`-equivariant: `θ(hx) = φ(h) θ(x)`. The O_ψ criterion's ψ-minimality and
     aperiodicity appear to go through for the noncommutative base
     `S^(-1) Z[T_I, registers] ⋊ F`, because `Q(T_I) ⋊ F` is simple: `F` acts faithfully
     on the field. This was sketched, not written out.
   - **Why the letters are restricted.** Compatibility with `F` forces every register
     update to be `φ(F)`-invariant. The only variables such updates can name are `T_q` with
     `q ∈ [1/2, 1)`, fixed by `φ(F)`, and those are read through a shift-type "load"
     letter. So along any word the registers evaluate a *one-pass* program: variables
     arrive in order, and each is read once into a bounded register file.
   - **Where it dies.** Such values have bounded rank across every cut of the variable
     order. Take a generic irreducible `q(x, y)` of `y`-degree `e`, and suppose `q` divides
     `Σ_(i<=w) a_i(x) b_i(y)` with `w <= e`. Then `b_1(y), ..., b_w(y)` would be linearly
     dependent over `Q(x)` in the function field of the curve `q = 0`. For `w = 2` this
     forces `b_1/b_2 ∈ Q(x) ∩ Q(y) = Q`, which fails for generic curves, whose variables are
     not separated. A prime dividing a product of values divides one value, so generic
     `q` of high degree are never inverted. This is sketched here only for rank `<= 2`; the
     general bounded-rank form is a heuristic.
   - **A bound on diagonal subfields (proved).** In any Leavitt--Nekrashevych completion
     over a localization `B` of a finitely generated commutative `Q`-algebra of Krull
     dimension `δ`, every subfield of the diagonal `colim B^(d^L)` has transcendence
     degree `<= δ`. Such a field maps injectively to a residue field of some stage
     `B -> colim_ξ B` along a word `ξ`. So `K_∞` needs either an infinite-dimensional
     base with an evaluation mechanism beyond one pass, or a non-diagonal commutative
     subring.
