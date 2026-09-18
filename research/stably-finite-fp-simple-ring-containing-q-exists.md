---
rg: 2
id: stably-finite-fp-simple-ring-containing-q-exists
kind: claim
title: Some ring finitely presented over Z is simple, stably finite, of finite stable range, contains the algebraic closure of Q unitally, and has K_1 equal to scalars plus torsion
distinct_from:
  fp-simple-resolvent-ring-with-divisible-unit-class: that gate asks for a stateless, not stably finite design; this is the stably finite branch U1 of gq-critic pass 3, outside the gate.
  torsion-k1-modulo-central-scalars-kills-scalar-symbols: that kills the scalar symbols once K_1 is scalars plus torsion; this is the ring-existence question that criterion would feed.
  q-algebra-with-fp-simple-projective-elementary-group: that is the host premise; a ring as here, with finitely generated stable K_2, would give a candidate PE_N.
artifacts:
  - research/artifacts/gq-gq-critic-pass-3.md
---

**OPEN (2026-09-18, lane gq-k2-q).** There is a ring `R`, finitely presented over `Z`, with all of the following:
- `R` is simple and stably finite;
- `R` has finite stable range;
- `Q̄ ⊆ R` unitally;
- `K_1(R) = ι(Q̄^x) + torsion`.

## Why it matters

- **Stable range.** For `N >= sr(R) + 2`, `K_2(N, R) ≅ K_2(R)` and it is central (Weibel, *The K-book*,
  III Remark 5.5.2, as supplied by gq-referee-b).
- **Scalar symbols.** With `Q̄` central, `torsion-k1-modulo-central-scalars-kills-scalar-symbols` kills all
  scalar symbols.
- **Unit class.** `[1]` has infinite order as soon as `K_0(R)` has a faithful state, for example a trace.
- **Host.** So `E_N(R)` is finitely presented whenever stable `K_2(R)` is finitely generated, and `PE_N(R)` is
  then a candidate host.

## Proved necessary condition (lane proof, elementary)

**Truncation principle.** Let `P` be a finitely presented ring containing `Q`. Then `P` has no nonzero ring
homomorphism to any ring of positive characteristic. Consequently:
1. `P` has no nonzero finite quotient and no nonzero finite-dimensional module over a field of positive
   characteristic. In particular `P` is not residually finite.
2. Suppose a ring `R` has the following property: every finite system of polynomial equations with integer
   coefficients that has a solution in `R` also has one in some nonzero ring of positive characteristic.
   Then no finitely presented `P` with a unital map `P -> R` contains `Q`.

*Proof.* A unital map `P -> S` with `p = 0` in `S` sends `1 = p·p^(-1)` to `0`, so `S = 0`.
- For item 1, finite rings and `F_p`-algebras have positive characteristic.
- For item 2, map the generators of `P` into `R`. The finitely many defining relations become a finite system
  solved in `R`, hence solvable in a nonzero ring `S` of characteristic `p`. That gives `P -> S`, and `S = 0` by the
  above. ∎

So the ring sought must be *rigid in characteristic zero*: its finitely many relations must have no solution in
any ring of positive characteristic. `bounded-harmonic-rings-are-not-finitely-presented` is item 2 for harmonic
crossed products, where truncating the harmonic function supplies the positive-characteristic solutions.

## The mechanisms on main, against the target

- **Leavitt and resolvent vacuum.** These are characteristic-zero rigid and finitely presented
  (`leavitt-resolvent-ring-is-fp-simple-of-char-zero`). But a resolvent vacuum forces infinitely many orthogonal
  copies of its idempotent, so a simple host with one is not stably finite
  (`resolvent-vacuum-rings-have-no-k0-state`).
  - The same holds for any evaluation of an Euler-type shift `x u x^(-1) = u + l` at an eigenvalue by an
    idempotent: its `x`-conjugates are orthogonal (their eigenvalues differ by nonzero integers, and `Q ⊆ R`) and
    equivalent, so it cannot be full in a stably finite ring.
  - Reason: if `1 = Σ_(i<=m) a_i ε b_i`, then `R` is a summand of `(Rε)^m`. `m+1` orthogonal copies of `ε` would
    then give `R^m ≅ R^m ⊕ Y` with `Y != 0`.
- **Harmonic elimination.** This gives stably finite and tracial rings, but it is not finitely presented (item 2
  above, and `bounded-harmonic-rings-are-not-finitely-presented`).
- **Integral forms and AF groupoid rings.** Their finitely generated subrings omit `Q`
  (`integral-form-algebras-have-no-fg-subring-containing-q`,
  `af-groupoid-rings-have-no-fg-subring-containing-q`). This covers Weyl algebras, enveloping algebras, group
  and Steinberg algebras, and Euler-type skew Laurent rings.
- **What is left.** A new mechanism is needed: finitely many integer relations with no positive-characteristic
  solution, realized in a stably finite ring and producing `Q` without an orbit of orthogonal evaluation
  idempotents.
  - A finitely presented division ring of characteristic `0` would be one. As far as this lane knows, it is open
    whether any infinite finitely generated division ring exists. This is not read at a source.
  - This lane has no candidate.

## Attempts

1. **One attempt (2026-09-18, lane gq-k2-q).**
   - Tried: two Euler mechanisms with coprime moduli `l` and `l'`, acting on a common evaluation idempotent `ε`.
     This does give `Q ε ⊆ εRε`.
   - Why it fails: the `x`-orbit of `ε` consists of orthogonal equivalent idempotents, so `ε` is not full in a stably
     finite `R`. The unital host would have to be the corner `εRε` itself, which puts the question back where it
     started.
   - No design meets the target, and no obstruction beyond the truncation principle is known.
