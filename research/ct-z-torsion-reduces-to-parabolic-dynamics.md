---
rg: 2
id: ct-z-torsion-reduces-to-parabolic-dynamics
kind: claim
title: In CT_P(Z), a prime whose degree cocycle is a continuous coboundary (elliptic prime) collapses through a variable-level quotient that preserves order and certificates; with the closing lemma and the one-prime base case, the torsion certificates are complete except on parabolic elements
requires:
  - hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z
  - conway-amusical-permutation-is-the-full-three-shift
distinct_from:
  hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z: that certifies elements with a hyperbolic ergodic measure; this removes elliptic primes by induction and isolates what is left.
---

**ESTABLISHED** for Lemmas 1–2 and the Theorem (lane proof; the base case uses the recalled
attractor–repeller structure of Higman–Thompson elements, and bh-kourovka's collapse, landed in
`f08cecd33`). **Not proved:** Conjecture 7 itself. The residual class is described exactly below.
No priority claimed.

**Correction to the proposed step.** A zero Lyapunov exponent in a prime `p` does **not** by
itself let one factor `p` out. What does is `p` being *elliptic*: its degree cocycle is a continuous
coboundary. Zero exponent with unbounded sums (*parabolic*) is exactly the case that remains open.

## Setting

- **The class `𝒞_P`.** Homeomorphisms `g` of `X = Ẑ_P × Ω`, with `Ω` finite, that are affine
  (`y ↦ cy + d`, `c ∈ ⟨P'⟩`, `d ∈ Q`) on each piece of a finite box partition and permute the labels
  in `Ω`. This contains `CT_P(Z)` (take `|Ω| = 1`) and is closed under the collapses below.
- **Degrees.** `d_p(g)(x) = v_p(slope of g at x)`.
- **Prime types.** A prime `p` is *hyperbolic for g* if `d_p(g) ≢ 0`, and *elliptic for g* if
  `d_p(g) = u∘g − u` for a locally constant `u : X → Z`.
- **Certificates of infinite order.** (a) a compression `g^k W ⊊ W`, `W` clopen; (b) a periodic
  point of slope `≠ 1`, in `g` or in an iterated collapse of `g` (Lemma 1).

## Statement

1. **Lemma 1 (variable-level collapse).** Let `p` be elliptic for `g ∈ 𝒞_P`, with at least one
   other prime of `P'` present. Then for all large `K` the relation
   `x ∼ y` iff (`y_q = x_q` for every `q ≠ p`, the labels agree, and `y_p ≡ x_p mod p^{K+u(x)}`)
   is a closed `g`-invariant equivalence relation, and `g` maps `[x]` onto `[gx]`. The quotient map
   `ĝ` lies in `𝒞_{P∖{p}}`: the `p`-coordinate becomes part of the finite label. Moreover:
   - `ord(ĝ) = ord(g)`;
   - compressions of `ĝ` pull back to compressions of `g`;
   - `ĝ` has one hyperbolic prime fewer.
2. **Lemma 2 (base case).** If `g ∈ 𝒞_P` has at most one hyperbolic prime, then either `g` has
   finite order, or it has both (a) and (b).
3. **Theorem (induction).** Let `g ∈ 𝒞_P`, and consider its successive collapses. Suppose that at
   every stage the current map either:
   - has an ergodic invariant measure with all exponents nonzero in its hyperbolic primes, or
   - has an elliptic hyperbolic prime.

   Then `g` has finite order, or (a) or (b) holds. In particular every counterexample to
   Conjecture 7 reaches a stage that is **parabolic**:
   - no compression;
   - every ergodic measure has a zero exponent in some hyperbolic prime;
   - no hyperbolic prime is elliptic.
4. **Minimal case (Gottschalk–Hedlund).** If that stage is minimal, a hyperbolic prime is elliptic
   as soon as its degree sums are bounded along a single orbit. So a parabolic minimal stage has,
   in every hyperbolic prime, degree sums unbounded along every orbit but sublinear for some
   invariant measure.

## Proofs

**Lemma 1.**
- **Choice of `K`.** Take `K` so large that `K + min u` is at least `v_p` of the moduli of `u` and of
  the pieces of `g`. Then each class lies in one piece of `g` and in one level set of `u`.
- **Classes map to classes.** On that piece `g(y) = cy + d` with `v_p(c) = u(gx) − u(x)`. So `g`
  fixes the other coordinates of the class, as the value at `x`, and sends the `p`-ball
  `x_p + p^{K+u(x)} Z_p` onto `(gx)_p + p^{K+u(gx)} Z_p`. That is `[gx]`.
- **The quotient.** `X/∼` is the finite union, over the values of `u`, of level pieces of `Ẑ_{P∖p}`
  times the residues `mod p^{K+u}`. `ĝ` acts there by the same affine maps on the remaining
  coordinates. There `p` is a unit, so `v_p` no longer counts, and the residue labels are permuted.
- **Order.** If `ĝ^n = id`, then on each piece the affine map of `g^n` is the identity on an open
  subset of a remaining coordinate `Z_q`. So `c = 1` and `d = 0` (diagonal rigidity), and `g^n = id`.
  The converse is clear.
- **Compressions.** The preimage of a clopen `Ŵ` with `ĝ^k Ŵ ⊊ Ŵ` is a clopen `W` with `g^k W ⊊ W`.
- **Hyperbolic primes.** `d_q(ĝ) = d_q(g)` for `q ≠ p`.

**Lemma 2.**
- **No hyperbolic prime.** Every slope is `1` (a `P'`-smooth ratio that is a unit at every prime).
  So `g` permutes the boxes of a common modulus, and a canonical self-map of a box is the identity.
  Hence `g` has finite order.
- **One hyperbolic prime `q`.** Collapse the unit primes (bh-kourovka `f08cecd33`, item 1; or
  Lemma 1 with `u = 0`). This yields a Higman–Thompson element on `Z_q × Ω`, i.e. prefix replacements
  on finitely many roots.
- **Higman–Thompson dynamics.** For these, infinite order forces an attracting periodic orbit
  (Brin's revealing pairs; Salazar-Díaz; recalled, not re-read). Its basin gives (a), and its slope
  `|c|_q < 1` gives (b).

**Theorem.** Induct on the number of hyperbolic primes.
- At a stage with a hyperbolic ergodic measure, apply the closing lemma
  (`hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z`), which works verbatim in `𝒞_P`.
  This gives (b).
- At a stage with an elliptic hyperbolic prime, apply Lemma 1. Order and certificates are
  preserved, and the count drops by one.
- The base is Lemma 2.
- The parabolic description is the negation of the two hypotheses.

**Item 4.** Gottschalk–Hedlund: for a minimal homeomorphism, a continuous function whose Birkhoff
sums are bounded along one orbit is a continuous coboundary. Degree cocycles are locally constant
and integer-valued, so the transfer function can be taken locally constant. `∎`

## The residual class and why it matters

- **What a counterexample looks like.** A counterexample to Conjecture 7, i.e. an undecidable-torsion
  mechanism in `CT(Z)`, must be *parabolic in a p-adic direction*: chain recurrent, with degree sums
  that wander unboundedly but sublinearly, like Birkhoff sums of a non-coboundary over an irrational
  rotation.
- **Where it can come from.** Neither the shift pieces nor the odometer fibres supply this:
  - shifts are hyperbolic, hence certified by (b);
  - odometers over unit primes are elliptic, hence collapsed.

  It needs a genuinely new mechanism: a Sturmian-type skew product built from canonical pieces.
- **What it would unlock.** Such an element would be the first candidate for minimal-type dynamics
  in `CT(Z)`, and so for the `2V` writer and for 17.58's full-group route.
- **Sharpest next step.** Show that a parabolic stage cannot occur. For example: for canonical
  pieces, prove that bounded-slope recurrence forces the degree cocycle to be a coboundary, a
  Gottschalk–Hedlund statement for chain recurrent `𝒞_P` maps. Or construct a Sturmian `𝒞_P` map.

**Lesson for general BH.**
- **Primes come in three types.** In piecewise-affine p-adic hosts the primes of an element are
  hyperbolic, elliptic or parabolic.
- **The first two are harmless.** Hyperbolic primes certify themselves by closing. Elliptic primes
  collapse without changing the order, because diagonal rigidity keeps the remaining coordinates
  faithful.
- **All complexity lives in the third.** So undecidability, writers and exotic subgroups can only
  come from parabolic (rotation-like) degree cocycles. That is one precise dynamical target for both
  the obstruction and the construction side.
