# Finite-memory self-hashing for non-MF groups

**Status:** exact detector theorems and conditional operator-norm reductions;
the finite-syntax authentication step remains open.
**Date:** 2026-08-23.

## 1. Reuse map

This architecture does not create a second copy of the existing
no-renormalization results.

* Whole-packet collision is the machine-checked theorem
  `CollisionCapacityDetectors.collision_kills_phase`.
* Finite-palette overflow is
  `CollisionCapacityDetectors.phase_close_of_palette_overflow`.
* Choosing the challenge after freezing a finite coordinate is
  `CollisionCapacityDetectors.no_model_of_uniform_unbounded_capacity`.
* Projection-rank rigidity and cyclic rank monodromy are
  `CollisionCapacityDetectors.projection_rank_rigid` and
  `CollisionCapacityDetectors.rank_zero_of_power_monodromy`.
* The exact one-step self-copy detector is packaged directly by
  `repCommutant_eq_map_sandwich_of_compression`,
  `mem_repCommutant_of_commutes_compressed`, and
  `map_commutator_eq_one_of_commutes_compressed`, with the representation-
  theoretic wrapper
  `map_commutator_eq_one_of_commutes_compressed_units`.  The older marked
  compression endpoint `map_marked_commutator_eq_one` and its globalization
  `compressionCentralizerDefect_le_ker` are recovered from the same argument.

The last identification is worth making explicit.  If `B` embeds in an
ascending HNN extension with stable letter `t` and child map `alpha`, and a
sibling packet centralizes `alpha(B)`, then take `Gamma = B`, take the sibling
lamp as `c`, and read the HNN relation as

```text
t Gamma t^-1 <= Gamma.
```

The proof in `Criterion/FiniteDimensionalKill.lean` uses the commutant of the
image of `Gamma`.  Conjugation by the image of `t` injects that finite-
dimensional commutant into itself, hence maps it onto itself.  Therefore the
transported sibling lamp still centralizes the whole image, and its marked
commutator dies.  This is precisely the finite-memory self-copy argument,
proved over every field and every finite-dimensional linear representation.

## 2. Whole-packet collision

For unitary matrices `A`, `B_v`, `B_w`, and a matrix `Z`, assume

```text
||A B_v - Z B_v A|| <= epsilon,
||A B_w - B_w A||   <= epsilon,
||B_v-B_w||         <= delta.
```

Then

```text
||Z-1|| <= 2 delta + 2 epsilon.
```

The proof is a triangle inequality followed by multiplication by the unitary
`B_v A`.  It uses neither trace nor rank.  A finite operator-norm palette for
`U(d)` converts any graph defeating that palette into such an adjacent
collision.  An unbounded family of uniformly authenticated challenge graphs
therefore defeats each fixed finite dimension after the coordinate is fixed.

The word *uniformly* is load-bearing: every addressed check must cost at most
`C Def_R(U)` with the same `C`, independently of address or challenge depth.
The existing Lean theorems formalize the post-coordinate implication, not the
construction of such a finite presentation.

## 3. Exact one-step self-copy detector

Let `B` have commuting child copies `B_0` and `B_1`, each isomorphic to `B`,
and let `alpha : B -> B` have image `B_0`.  In the ascending HNN extension

```text
G_copy = < B,t | t b t^-1 = alpha(b) >,
```

let `p_1,q_1` lie in `B_1` and set `J=[p_1,q_1]`.

Every finite-dimensional representation kills `J`.  Indeed, the algebra (or,
equivalently, the commutant) associated with the child is a conjugate
finite-dimensional copy contained in the parent.  Equal dimension forces
equality.  Since the sibling belongs to the parent and centralizes the child,
its two Pauli generators commute in the representation.

The abstract exact detector is now a standalone unconditional Lean theorem:
`map_commutator_eq_one_of_commutes_compressed`.  Its hypotheses are precisely
the one-sided child inclusion, sibling/child commutation, and membership of
the second sibling generator in the parent.  No literature theorem,
property `(T)`, unitarity, trace, or asymptotic approximation principle enters
this declaration.  A Thompson--Clifford instantiation additionally needs a
formal construction of its group, child embedding, sibling central-product
packet, and Britton embedding.  Those data currently exist at the Cairn
research level, not as a Lean carrier.

## 4. Thompson even-lamp finite-state detector

Let Thompson's simple group `V` act highly transitively on a countable dyadic
orbit `X`, let

```text
M   = F_2^(X),
I_X = ker(sum : M -> F_2),
Gamma_state = I_X semidirect V.
```

The expected finite-presentation argument uses finite presentation of the
permutational wreath product, finite generation of a point stabilizer, and
finitely many diagonal orbits on `X^2`; `Gamma_state` has index two in that
wreath product.

For an exact finite-dimensional unitary representation, the commuting
involutions from `I_X` have finite joint character support.  Covariance makes
that support a finite `V`-set.  Simplicity and absence of finite quotients make
the action trivial.  A `V`-fixed character of `I_X` is trivial: extending it to
`M` gives a function `g : X -> F_2` well-defined modulo constants; invariance
modulo constants gives a homomorphism `V -> F_2`, hence zero, and transitivity
makes `g` constant.  Thus the lamp image is trivial.  The remaining `V` image
is trivial by simplicity plus Malcev residual finiteness of finitely generated
linear groups.

This exact detector is distinct from the existing Pauli-seed character-actor
node.  It claims triviality of the entire representation and uses the
augmentation module itself.  Its Thompson action and finite-presentation
inputs are not currently formalized in Lean.

## 5. Open authentication problems

Exact finite-dimensional sterility is not non-MF: MF permits a different
approximate implementation at every coordinate.  Three equivalent-looking
frontiers remain.

1. **Self-copy checksum.**  Upgrade approximate HNN generator relations to a
   uniform near-equality of parent and child finite-dimensional algebras, or
   directly pin the sibling packet near the parent center.
2. **Finite-state rounding.**  Round an operator-norm approximate model of
   the Thompson even-lamp presentation to a finite exact joint character set
   with controlled actor covariance.
3. **Packet self-hash.**  Produce unbounded challenge graphs whose addressed
   local and edge checks all have one depth-independent root defect bound.

No ordinary normalized-HS quantum-expander gap may be silently used as an
operator-norm Kadison--Kastler estimate.  That upgrade needs its own proof.

## 6. Status of the endpoint

The following implication is established conditionally:

```text
uniform operator-norm self-hash
  + exact finite-memory detector
  -> every norm-corona representation kills the mark.
```

The construction of a finite presentation satisfying one of the uniform
self-hash interfaces is OPEN.  Accordingly this lane is not an unconditional
non-MF construction and is kept separate from the unconditional
router--detector proof.
