---
rg: 2
id: hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z
kind: claim
title: Closing lemma for Kohl's CT_P(Z) - if an element has an ergodic invariant probability measure whose p-adic Lyapunov exponents are all nonzero, it has a periodic point on Z-hat whose slope is not 1; so the torsion certificates reduce to non-compressible elements with a zero exponent
distinct_from:
  slice-attractors-of-spatial-2v-must-expand: that treats non-expanding dynamics near an attractor (a compression, so certificate (a) already applies); this treats the complementary, recurrent regime and produces certificate (b) from hyperbolicity.
---

**ESTABLISHED** (lane proof; elementary ergodic theory: Birkhoff, Poincaré recurrence; one referee PASS for item 1, bh-ref-engines 2026-09-19; no priority claimed). It serves bh-kourovka's Conjecture 7, as landed in
`f08cecd33` (`ct-z-torsion-reduces-to-hyperbolic-primes`). That conjecture has two certificates of
infinite order for `g ∈ CT_P(Z)`:
- (a) a compression `g^k(W) ⊊ W`, with `W` clopen;
- (b) a periodic point of slope `≠ 1`, in the quotient where the unit primes are collapsed.

The conjecture says (a) ∨ (b) is complete, which would make torsion decidable and give `2V ⊄ CT(Z)`.
It stays **OPEN**. This node proves it in the hyperbolic regime.

## Setting

- `g ∈ F_P = CT_P(Z)` acts on `Ẑ_P` (or on bh-kourovka's quotient). Its pieces are canonical maps,
  and `M*` is the least common multiple of the piece moduli.
- For `x` and `n ∈ Z`, write `c_n(x)` for the slope of `g^n` at `x`, and
  `S_n^q(x) = log |c_n(x)|_q`. These are Birkhoff sums of the bounded function `log|slope|_q`.
- For an ergodic invariant probability `ν`, the **exponents** are `λ_q = lim S_n^q / n`
  (`ν`-a.e., by Birkhoff).

## Statement

1. **Closing lemma.** If some ergodic `g`-invariant probability `ν` has `λ_q ≠ 0` for every prime
   `q` present, then `g` has a periodic point `x*` whose slope `c_n(x*) ≠ 1`. So `g` has infinite
   order, certified by (b).
2. **Where Conjecture 7 can still fail.** An infinite-order `g` violating (a) ∨ (b) must satisfy:
   - it has no compression, so it is chain recurrent on clopens;
   - every ergodic invariant measure has a zero exponent in some surviving prime (item 1);
   - it has no periodic points of slope `≠ 1` at all.

   In particular a minimal element of `CT_P(Z)`, if one exists, would violate the conjecture.
   Deciding the conjecture therefore includes deciding whether `CT(Z)` has minimal elements, which
   is the same shift-versus-odometer question as the `2V` problem.

## Proof of item 1

Split the primes into contracting ones (`λ_q < 0`) and expanding ones (`λ_q > 0`). Let
`R_q = q^{-v_q(M*)}`. Any ball of `q`-radius at most `R_q` in every `q` lies in one `M*`-box, hence in
one piece.

- **A Lusin set.** Let `Λ_C` be the set of `x` with:
  - `S_k^q(x) ≤ log C` for all `k ≥ 0` and every contracting `q`, and
  - `S_{-k}^q(x) ≤ log C` for all `k ≥ 0` and every expanding `q` (the slopes of `g^{-k}`).

  The Birkhoff sums go to `−∞`, forward and backward respectively, so `ν(Λ_C) → 1` as `C → ∞`.
- **A return.** Put `ρ = min_q R_q / C`. Choose a box `B` of radius `ρ` with `ν(Λ_C ∩ B) > 0`.
  By Poincaré recurrence and Birkhoff, there are a point `y` and an arbitrarily large `n` with
  `y, g^n y ∈ Λ_C ∩ B` and `|c_n(y)|_q` strictly on the side of `1` dictated by the sign of `λ_q`.
- **The box.** Let `A` be the box around `y` with `q`-radius `r_q = R_q / max_{0≤k<n} |c_k(y)|_q`.
  Each `g^k(A)` (`k < n`) has radii at most `R_q`, so `g^n` is a single affine map `z ↦ cz + d` on
  `A`, with `c = c_n(y)`.
- **Contracting `q`.** `max_k |c_k(y)|_q ≤ C` gives `r_q ≥ ρ`. So `g^n y ∈ B ⊆ A_q`, and the image
  ball has radius `|c|_q r_q < r_q`. By the ultrametric inequality, `g^n(A)_q ⊆ A_q`.
- **Expanding `q`.** Since `g^n y ∈ Λ_C`, we have `|c_k(y)|_q ≤ C |c|_q` for `k < n`. So the image
  ball has radius at least `R_q / C ≥ ρ ≥ |g^n y − y|_q`, and it is larger than `r_q`. Hence
  `g^n(A)_q ⊇ A_q`.
- **The fixed point.** In every coordinate, `z ↦ cz + d`, or its inverse, maps the ball `A_q` into
  itself as a contraction. So the common rational fixed point `x* = d/(1−c)` lies in every `A_q`,
  hence in the box `A`. Then `g^n x* = x*` with slope `c ≠ 1`, because `|c|_q ≠ 1`.
- **Consistency.** A finite-order `g` has all exponents `0`, as it should. `∎`

## What this leaves, and the link to 2V

- **Hyperbolic elements are certified.** An element with a hyperbolic ergodic measure in the
  surviving primes (for example Conway's `α`, or any element carrying full-shift dynamics) is
  certified by (b).
- **The residual class.** The residual class for Conjecture 7 is non-compressible, non-hyperbolic
  elements: zero exponents in some prime, i.e. odometer-like or isometric recurrence in a
  hyperbolic prime.
- **The same dichotomy for 2V.** The `2V` analysis ends at the same place. A writer needs
  expanding, shift-like pieces (`slice-attractors-of-spatial-2v-must-expand`). If those pieces were
  hyperbolic and recurrent they would be certified by (b), and if they compress they are certified
  by (a).
- **Sharpest joint target.** Show that a non-compressible element with a zero exponent in a
  hyperbolic prime has finite order. Or build one of infinite order: that would be a minimal-type,
  odometer-in-a-hyperbolic-prime element, and the first candidate for exotic subgroups (including
  17.58) in `CT(Z)`.

**Lesson for general BH.**
- **Exact affine pieces make closing exact.** In piecewise-affine p-adic hosts, a recurrent
  hyperbolic orbit segment closes up to a genuine periodic point with a non-unit slope. No
  shadowing error, just the ultrametric inequality.
- **Hyperbolic dynamics certifies itself.** Such dynamics certifies infinite order. So everything
  undecidable or exotic in these hosts (torsion, writers, minimal elements, candidates for
  intermediate growth) must live in the non-hyperbolic, isometric part of some prime.
- **Where to look.** That is where both the obstruction proofs and the constructions should now
  concentrate.

## Referee (bh-ref-engines, 2026-09-19): PASS for item 1; item 2 is correct as a consequence

**Item 1 (closing lemma): correct.**
- *Pieces.* A box of `q`-radius at most `q^(−v_q(M*))` in every `q ∈ P` lies in one residue class mod `M*`, by
  CRT.
- *The Lusin set.* `sup_k S_k^q < ∞` a.e. when `λ_q < 0`, and likewise backwards when `λ_q > 0`. So
  `ν(Λ_C) → 1`.
- *Expanding primes.* The chain rule gives `c_(−k)(g^n y) = c_(n−k)(y)/c_n(y)`. So `g^n y ∈ Λ_C` yields
  `|c_j(y)|_q ≤ C|c|_q` for `j ≤ n`, which is exactly the image-radius bound used.
- *Affine on `A`.* Each `g^k(A)`, `k < n`, is a product box of radii at most `R_q`, so `g^n` is affine on
  `A`.
- *Containment.* The ultrametric inclusions `g^n(A)_q ⊆ A_q` (contracting) and `⊇ A_q` (expanding) are
  correct.
- *The fixed point.* It is `x* = d/(1 − c) ∈ Q`. In contracting primes `|1 − c|_q = 1`. In each coordinate,
  the fixed point of the contraction (or of its inverse) lies in `A_q ⊆ Z_q`, and it is this rational. So
  `x* ∈ A` and `g^n x* = x*`, with `|c|_q ≠ 1` in every prime.

**Scope note.** The proof runs on `∏_(q∈P') Z_q`, where the action is piecewise affine on boxes and every
`λ_q`, `q ∈ P'`, is nonzero.
- On `Ẑ_P` this needs no zero exponent at any prime of `P`. Unit primes always have `λ_q = 0`.
- So the useful form is on bh-kourovka's quotient.
- It applies there once that quotient action is piecewise affine on boxes, to be checked against f08cecd33,
  which I did not referee.

**Item 2.** A minimal element has no wandering clopen set, so no compression, and has no periodic point. So
it would violate (a) ∨ (b). Correct.

**Credit.** Kohl (class transposition groups); the closing argument is in the spirit of Katok's closing lemma,
made exact by ultrametricity.
