---
rg: 2
id: leavitt-semisimple-torsion-units-conjugate-iff-same-support
kind: claim
title: Units of finite order prime to the characteristic in the binary Leavitt algebra are conjugate iff their spectral supports agree
distinct_from:
  binary-leavitt-nonzero-projectives-are-free: that is the nonstable K_0 fact that every nonzero finitely generated projective is free of rank one; this consumes it over finite separable extensions of the coefficient field to classify conjugacy of semisimple torsion units.
  signed-thompson-z-moving-rank-functions-match-v-rank-functions: that uses V-transitivity on proper clopens; this is a coarser conjugacy invariant for all semisimple torsion units of the unit group, far beyond what V or finite level groups see.
artifacts:
  - research/artifacts/ternary-minus-one-gate-outside-signed-thompson-2026-09-12.md
---

**ESTABLISHED** (route `leavitt-semisimple-torsion-conjugacy-proof`; artifact Section 2; verification requested from
`w4-vf-gate`).

Let `K` be a field, `R = L_K(1,2)`, and `m >= 1` with `char K ∤ m`. For `g in R^x` with `g^m = 1` and an irreducible
factor `q` of `x^m - 1` over `K`, let `e_q(g) in K[g]` be the spectral idempotent. Put
`S(g) = {q : e_q(g) != 0}`. Then two units `g, g'` with `g^m = g'^m = 1` are conjugate in `R^x` iff `S(g) = S(g')`.

**Proof idea.**
- **Decomposition.** `R_R = ⊕_(q in S(g)) e_q(g) R`.
- **Each summand is free.** Left multiplication by `g` makes `e_q(g)R` a module over `K_q ⊗_K R ≅ L_(K_q)(1,2)`,
  where `K_q = K[x]/(q)`. It is projective there, since `K_q/K` is separable. It is nonzero, so by
  `binary-leavitt-nonzero-projectives-are-free` it is free of rank one.
- **Conjugating unit.** Summing isomorphisms of these modules gives an automorphism of `R_R` intertwining `g` and
  `g'`, which is left multiplication by a unit.

**Corollaries** (artifact Section 2).
1. **Square roots of `z`.** Every square root of `z = -1` in `G_3 = L_(F_3)(1,2)^x` is conjugate to the Hadamard unit
   `h`, so to `wd in E ⋊ V`.
2. **Involutions.** Every non-central involution of `G_3` is conjugate to `τ_([0])`.
3. **Order 8.** In `G_3`, an element of order 8 with `a^4 = z` lies in the conjugacy class of some element of
   `E ⋊ V` iff both factors `x^2 ± x - 1` occur in its spectrum. The level-one Singer element of `GL_2(F_3)` has only
   one of them, so it is not conjugate into `E ⋊ V`. This recovers, element by element, `w4-hadamard-f3`'s
   observation that `SD16` is not conjugate into `E ⋊ V`.
4. **Rank functions.** For semisimple torsion `g`, every Sylvester rank function on `F_3[G_3]` gives values
   `rk(f([g]))` that depend only on `S(g)`. These are single-conjugation symmetries, so by
   `anti-central-sofic-data-cannot-force-defect-submultiplicativity` they cannot by themselves force
   `rk(1 - [z]) = 0`.
