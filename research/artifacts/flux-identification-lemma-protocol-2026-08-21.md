# The flux-identification lemma: protocol (designed 2026-08-21)

Target: the flagged conjecture of
`lambda-exact-face-of-the-collapse-closes` — the composition defect
of the canonical Ad-pullback transports on the flat band groupoid
equals the Matsumoto/Steinberg-symbol class.  Decisive either way:
verified at p = 3 it closes the entire Lambda-exact face for the
(SL_3(Z), SL_3(Z[1/3])) pair; refuted, the cocycle must be computed
directly (still finite).

## The objects

- Level groups `G_a = SL_3(Z/p^a)`; torus elements `h = diag(p, 1,
  p^-1)` and `h' = diag(1, p, p^-1)` (integral after multiplying by
  the appropriate Weyl conjugation; use the exact coweight pair
  whose Gamma-commutation is exact).
- Bands: irreducible constituents of `l^2(G_a)` (equivalently
  irreducibles of `G_a`) graded by essential depth vectors; the
  pullback transport `T_h` sends a constituent `pi` to
  `pi compose Ad(h)` where defined (depth shifted by the weight
  vector), unitarily implemented on the flat module by matching the
  multiplicity spaces.
- The flux: on a band where both orders of composition are defined,
  `T_h T_h' (T_h' T_h)^(-1)` is a Schur scalar `c(pi) in T` (both
  compositions pull back along `Ad(h h') = Ad(h' h)`, so the defect
  is an automorphism of an irreducible).  The lemma asserts
  `c(pi)` equals the Matsumoto symbol `(p, p)_p`-pattern paired by
  the root data — in particular `c = -1` identically at
  `p = 3 (mod 4)` on generic deep bands, `c = +1` at `p = 2`.

## The computation (single level triple suffices)

1. Fix `p = 3`, `a = 2` (level 9; `|G_2| = 3^8 . |SL_3(F_3)| =
   3^8 . 5616` — do NOT enumerate the group; work with one
   explicitly-presented deep constituent).
2. Construct one deep irreducible of `G_2` explicitly: a
   Heisenberg/oscillator-type constituent attached to a generic
   character of the congruence kernel `K = ker(G_2 -> G_1)`
   (abelian, `= (M_3^0(F_3), +)`): induce from a maximal isotropic
   subgroup for the commutator pairing.  These are exactly the
   bands where the metaplectic structure lives (the pairing is
   symplectic-like and `Ad(h)` acts on it).
3. The transports on such a constituent are explicit oscillator
   intertwiners (finite Weil representations of the residue
   symplectic space); their composition defect is a Gauss-sum
   quotient — compute the two orders and the scalar `c` exactly
   (algebraic number arithmetic in a cyclotomic field; a few
   hundred dimensions at most).
4. Compare with `(3,3)_3 = -1`.  Repeat at `p = 5` (`(5,5)_5 = +1`,
   since `5 = 1 mod 4`) as the control: the lemma predicts trivial
   flux there on the same band type — a sharp two-point test of the
   identification.
5. MSI lane; exact arithmetic (python fractions/cyclotomics or
   sympy if present); no floating point in the final scalar.

## Interpretation contract

- `c = -1` at `p = 3` and `c = +1` at `p = 5` on matched bands:
  identification VERIFIED where it matters; land the p = 3 closure
  and rewire the lane's primary pair.
- Any other pattern: the canonical cocycle is NOT the Matsumoto
  class; compute it directly on the same bands (the machinery of
  steps 2-3 already yields it) and re-run the trivializability
  question with the computed class.  Either way the Lambda-exact
  face's decision becomes a finished computation, not a question.
