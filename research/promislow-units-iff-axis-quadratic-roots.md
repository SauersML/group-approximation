---
rg: 2
id: promislow-units-iff-axis-quadratic-roots
kind: claim
title: R[P] has a nontrivial unit exactly when v^2 - (x + x^-1) v + 1 = 0 has a root other than x^(+-1), and every spectral invariant of such a root is that of x
distinct_from:
  promislow-group-ring-units-are-constant-reduced-norm: that is the quartic reduced-norm criterion deciding whether one element is a unit; this replaces the existence problem uv = 1 in two unknowns by one quadratic equation with a fixed central coefficient, in one unknown.
  rational-unit-conjecture-torsion-free: that is the conjecture for every torsion-free group; this is an equivalent reformulation of its instance on P over every commutative domain, and proves no triviality.
  integral-unit-conjecture-torsion-free: that is Higman's conjecture; on P with R = Z this is an equivalent form of it.
  integral-group-ring-units-have-arithmetically-large-spectra: that constrains the spectrum of u u*, which is not invariant under conjugation by units; this shows that no invariant of the reduced characteristic polynomial of u itself can detect a nontrivial unit.
  promislow-integral-units-have-monomial-definite-line-shadows: that constrains units modulo three ideals; this places every nontrivial root, after v -> x + x^-1 - v, inside the Case A congruence v = x mod (I_A cap I_B cap I_C).
artifacts:
  - experiments/promislow-unit-mahler-2026-09-17/fibre_spectra.py
  - experiments/promislow-unit-mahler-2026-09-17/fibre_spectra-run.log
  - experiments/promislow-unit-mahler-2026-09-17/axis_quadratic_calibration.py
  - experiments/promislow-unit-mahler-2026-09-17/axis_quadratic_calibration-run.log
---

**ESTABLISHED** by `promislow-units-iff-axis-quadratic-roots-proof`. Unreviewed.

**Setting.** `P = <a, b | b^-1 a^2 b = a^-2, a^-1 b^2 a = b^-2>` is the
Promislow group, with `x = a^2`, `y = b^2`, `z = (ab)^2`. These generate
`L = Z^3`, normal of index 4, and conjugation by `a, b, ab` acts on
`(x, y, z)` by `(x, y^-1, z^-1)`, `(x^-1, y, z^-1)`, `(x^-1, y^-1, z)`. So
`c = x + x^-1` is central in `R[P]`. For a commutative domain `R` a unit of
`R[P]` is *trivial* if it is `lambda g` with `lambda in R^x`, `g in P`.

Let `q(T) = T^2 - c T + 1`, and call `v in R[P]` an **axis root** if
`q(v) = 0`, i.e. `v^2 - (x + x^-1) v + 1 = 0`.

1. **Reduction.** For every commutative domain `R`, the following are
   equivalent:
   - (a) `R[P]` has a nontrivial unit;
   - (b) `R[P]` has an axis root `v` other than `x` and `x^-1`.

   Every axis root is a unit, with `v^-1 = x + x^-1 - v`. The only trivial
   axis roots are `x` and `x^-1`. If `u` is a nontrivial unit, then `u x u^-1`
   or `psi^-1(u y u^-1)` is a nontrivial axis root, where `psi` is the
   automorphism `a -> b`, `b -> ab` of `P`, with `psi(x) = y`, `psi(y) = z`,
   `psi(z) = x^-1`.
2. **Equivalent forms.** For `v in R[P]` the following are equivalent:
   - `v` is an axis root;
   - `v + v^-1 = x + x^-1` for a unit `v`;
   - `n = v - x^-1` satisfies `n^2 = x n - n x^-1`.

   The last form has the trivial solutions `n = 0` and `n = x - x^-1`. An axis
   root comes with explicit intertwiners inside `R[P]`:
   `(v - x^-1) v = x (v - x^-1)` and `(v - x) v = x^-1 (v - x)`. If
   `2 in R^x`, put `K = 2v - c`. Then axis roots are exactly the square roots
   `K` of the central element `(x - x^-1)^2`, and the trivial ones are
   `K = +-(x - x^-1)`.
3. **Spectral invariants cannot see nontrivial units (obstruction).** Let `v`
   be an axis root in `C[P]`. For a character `xi: L -> C^x`, let `V(xi)` in
   `M_4(C)` be the image of `v` in the induced representation (left
   multiplication on the basis `1, a, b, ab`, specialised at `xi`). Then:
   - every eigenvalue of every `V(xi)` is `xi(x)^(+-1)`, each with
     multiplicity 2 when `xi(x) != +-1`, exactly as for `x` itself;
   - the characteristic polynomials of left and of right multiplication by
     `v` over `C[L]` are both `(T^2 - cT + 1)^2`, the ones of `x`;
   - its Mahler measure is 0, and every fibre at a unitary character has
     spectral radius 1;
   - the Brown measure of `v` is the pushforward of Haar measure under
     `xi -> xi(x)`, and `tau(v^k) = 0` for `k != 0`;
   - the Fuglede--Kadison determinant of `v` is 1, and `Nrd(v) = 1`.

   By item 1, if `R[P]` has any nontrivial unit (`R` a domain inside `C`) then
   it has one whose invariants of this kind agree with those of the trivial
   unit `x`. So no argument of the form "a nontrivial unit of `Z[P]` or
   `Q[P]` has a reduced characteristic polynomial, spectral radius, Mahler
   measure, entropy, Brown measure, determinant or trace sequence different
   from every trivial unit" can prove the conjecture on `P`. The exact step
   where such an argument dies is the conjugation `u -> u x u^-1`, which is
   nontrivial by the support lemma of the proof and preserves all of these
   invariants. In particular the *Mahler-measure dichotomy* is dead:
   - either the reduced characteristic polynomial has Mahler measure 0, in
     which case some power of `u` is `D`-conjugate to an element of `L`;
   - or it is positive, and the coefficients of `u^n` grow exponentially.

   Nontrivial units fall on both sides. Gardam's unit has Mahler measure
   about `1.41` (numerical). Its conjugate `alpha x alpha^-1` has Mahler
   measure 0.
4. **Shadows.** For `R = Z`, every axis root `v` satisfies
   `v - x in I_A cap I_B cap I_C` or `v - x^-1 in I_A cap I_B cap I_C`. The
   ideals are the kernels of the three definite shadows of
   `promislow-integral-units-have-monomial-definite-line-shadows`. Replacing
   `v` by `v^-1 = c - v` makes it the first. So nontrivial axis roots over `Z`
   are Case A objects: the shadow method gives nothing more on them.

**Calibration** (`experiments/promislow-unit-mahler-2026-09-17/`, exact
arithmetic in `Z[s,t]/(s^4+1, t^4+1)[P]` with Gardam's unit `alpha`):
- `v_x = alpha x alpha^-1`, `v_y`, `v_z` are nontrivial axis roots for their
  axes, with supports 112, 92 and 106 and coefficients up to 7. Reduced to
  `F_2[P]` they are still nontrivial, with supports 79, 51 and 85.
- `psi` is an automorphism with `psi(x) = y`, `psi(y) = z`, `psi(z) = x^-1`.
- Numerically, at 1500 to 4000 random characters (`zeta_8` embeddings):
  - `alpha` has maximal `log|lambda|` equal to `2.08` and Mahler measure
    about `1.41`;
  - `v_x` and all trivial units tested have Mahler measure 0 (up to
    `1e-13`).

So the reduction reproduces the known failures over `F_2` and `Z[zeta_8]`.

**What it changes.** The unit problem on `P` is usually posed as the
bilinear system `uv = 1` on a pair of supports. By item 1 it is equivalent
to the existence of a nontrivial root of one fixed quadratic in one unknown,
whose inverse is `c - v`. So a support census may take
`supp(v^-1) ⊂ supp(v) ∪ {x, x^-1}`. Item 3 says any proof has to use data
that is not conjugation-invariant, such as the involution (`u u*`) or
supports.

DERIVATION
[[promislow-units-iff-axis-quadratic-roots-proof]]
