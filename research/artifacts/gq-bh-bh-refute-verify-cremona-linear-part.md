# Adversarial check: `fg-cremona-subgroups-have-arithmetic-linear-part` (bh-refute, 2026-09-18)

Coordinator-assigned item. It bears on BBMZ Problem 2.7 (a natural finitely presented host for `GL_n(Q)`) through
Cremona groups.

Verdict: **PASS**. Every step was re-derived.

## Checks

- **Primitive representatives.** By Gauss, the primitive representative is unique up to sign, and its reduction
  mod `p` is never the zero tuple.
- **Step 1.**
  - Let `G_p` be the cone map of a dominant `g_p`. Its image is a cone whose projectivization is dense, hence
    the image is dense in `A^{m+1}`. So `F_p(G_p) ≠ 0`.
  - Write `F(G) = c·H·K`, with `H` the primitive gcd and `K` primitive. Reducing gives `c_p ≠ 0` and `H_p ≠ 0`.
  - A nonzero common polynomial factor does not change the rational map. So `(f∘g)_p = f_p∘g_p`.
- **Step 2.** `S_p` is a subgroup. Inverse-closure is built into the definition, and product-closure applies
  Step 1 to `(f,g)` and to `(g^{-1}, f^{-1})`.
- **Step 3.**
  - In characteristic 0 a dominant equidimensional map is generically étale, so the Jacobian `J_F ≠ 0`.
  - Reduction commutes with differentiation, so `J_{F,p} ≠ 0` for almost all `p`. Then `F_p` is étale at some
    point of `A^{m+1}(F̄_p)`, and `f_p` is dominant.
- **Step 4.**
  - For a linear `f = [A]` with `A` primitive, `f_p` is dominant iff `A mod p` is invertible.
  - So `det A` is an `N`-unit, and `A ∈ GL_{m+1}(Z[1/N])`.
- **Step 5.** `PGL_{m+1}(Z[1/N]) ↪ GL_{(m+1)^2}(Z[1/N])`, which is residually finite.
- **Consequence 1.** A divisible subgroup `D` of a residually finite group is trivial, since its image in any
  finite quotient is a finite divisible group, which is trivial.
- **Consequence 2.** `diag(g,1,…,1)` is scalar only for `g = 1` when `m+1 > n`.

## Attacks tried (all failed)

- **Composition when `g_p` is not dominant.** Excluded: `S_p` requires dominance of both `f_p` and `(f^{-1})_p`.
- **Common factors appearing only mod `p`.** Harmless. They do not change the rational map.
- **Over `C`.** Correctly scoped out.

## Lesson for general BH

In finitely generated groups, "integral representatives with multiplicative reduction at good primes" forces
the linear part to be `S`-arithmetic, hence residually finite. So no host class of this algebraic kind
(Cremona groups, or more generally birational or polynomial automorphism groups over `Q`) can contain
divisible linear subgroups such as `(Q,+)`. A finitely generated host for `GL_n(Q)` must realize `Q`
non-linearly: dynamically (full groups, Leavitt units) or non-residually-finitely. This is the root
obstruction O1 in a form that applies across whole host families.
