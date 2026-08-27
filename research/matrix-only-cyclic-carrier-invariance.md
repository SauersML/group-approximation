---
rg: 2
id: matrix-only-cyclic-carrier-invariance
kind: claim
title: Force a transverse cyclic carrier to become invariant only in finite matrices
distinct_from:
  fanizza-canonical-profile-groupification: that asks to collapse the native machine signal along canonical microstates; this asks only for a finite-dimensional invariance estimate on a cyclic Fourier carrier with independently certified canonical transversality.
  robust-locally-satisfiable-relator-code: that seeks a direct positive fraction of violated word relators; this permits the contradiction to be mediated by one property-T commutator-energy inequality.
  property-t-hs-positive-density-commutant-no-growth: that supplies a lower/no-growth theorem in approximate HNN models; this asks for the opposite matrix-only upper bound which is allowed to fail in the canonical regular von Neumann algebra.
---

Construct a finitely presented group `G=<X|R>`, a property-`(T)` subgroup
`H=<S>`, an infinite-order word `w`, and a nonconstant trigonometric
polynomial `f` such that every nonzero power of `w` in the Fourier support of
`f` has infinite `H`-conjugacy orbit, while the following genuinely
finite-dimensional estimate holds.

There is a modulus `eta(delta)->0` such that every finite-dimensional unitary
tuple `U` with presentation defect at most `delta` satisfies

```text
sum_(s in S)||[U(s),f(U(w))]||_2^2 <=eta(delta).         (MCI1)
```

The estimate must use finite-dimensional multiplicity, rank, or recursion.
It cannot be a formal consequence of the group relations or a dimension-free
Hilbert-space inequality, since the regular representation satisfies those
relations and has the strict lower floor from
`infinite-conjugacy-orbits-give-canonical-carrier-no-capture`.

## Attempts

- `mci-exact-endpoint-is-fd-radical` identifies the zero-defect requirement,
  but `shifted-infinite-heisenberg-wreath-exact-mci-is-hyperlinear` realizes
  that entire endpoint with an infinite-order transverse carrier inside a
  hyperlinear group. The missing statement is uniformity as dimension grows,
  not exact finite-dimensional representation theory.
- Amenable shift-local recursion cannot prove `(MCI1)` by
  `amenable-finite-propagation-feedback-has-folner-tail-models`.
- Property `(T)` supplies the lower floor, not the upper bound;
  `property-t-does-not-force-marked-carrier-transversality` shows that it
  cannot manufacture orbit transversality.
- A finite-at-each-stage word recursion cannot amplify a sublinear exceptional
  summand by `word-recursion-cannot-amplify-sublinear-summands`. A viable
  construction must act on the canonical macroscopic carrier and use a
  matrix-only capacity or holonomy recurrence.
- `cyclic-carrier-energy-stability` is a strict weakening: it permits nonzero
  exact finite-dimensional energy and asks only that one scalar energy
  supremum be upper semicontinuous at zero defect.

## Bounded cyclic selector-word audit

`cyclic-coarse-fine-selector-rows-spread-carrier-error` removes the local
multiplicity-twist problem once the selector rows have been decoded.  Indeed,
if a physical transport is amplified as

```text
U_i=S_i tensor V_i,
```

while the coarse and fine selectors act trivially on the multiplicity factor,
then its reflection row is

```text
C_i=R_(f_(i+1)) U_i R_(e_i) U_i^*
   =(R_(f_(i+1)) S_i R_(e_i) S_i^*) tensor 1.          (MCI-ROW)
```

Thus the arbitrary `V_i` cancels inside each row, before cycling.  The cyclic
trace lemma then gives the positive square-function estimate

```text
sum_i ||C_i-1||_2^2 >=sum_i tau(P_i).                  (MCI-CYCLE-SQ)
```

The remaining issue is whether a bounded family of ordinary group words can
authenticate those rows without making them universal tracial identities.
There are three direct obstructions.

1. **Multiplying the rows loses positivity.**  Replacing the family by one
   product word `C_(k-1)...C_0` permits exact inverse cancellation: choose
   consecutive row errors `D,D^-1` (or conjugate copies on the same carrier).
   The product is one while both row energies are positive.  This is the same
   mechanism certified for cyclic clock holonomy by
   `one-product-holonomy-does-not-sew-four-bs-clocks`.  No estimate of the sum
   in `(MCI-CYCLE-SQ)` follows from the defect of an unlocalized product.
2. **Orthogonal packing is selector-dependent.**  If the row errors could be
   placed on pairwise orthogonal projections `p_i`, then their block-diagonal
   product would satisfy a Pythagorean identity and one word defect could
   charge the sum.  But the operation

   ```text
   C_i -> (1-p_i)+p_i C_i p_i
   ```

   uses addition and a named projection; it is not a group word.  Taking the
   `p_i` as spectral projections of a fixed finite clock makes the construction
   functorial in every finite tracial algebra.  Adjoining literal reflection
   words `1-2p_i` has the same problem: the resulting row identities are
   universal and trigger the regular-trace firewall.
3. **Pure transport words cannot locate the fine atoms.**  Even with the
   involution, all its moments, determinant, and the exact coarse/fine packet
   ranks fixed, `pure-prefix-swap-invariants-are-selector-blind` moves the fine
   atom from inside the coarse atom to its complement while preserving every
   pure word invariant.  The mixed row energy changes.  Repeating this choice
   independently around a bounded cycle preserves all vertexwise pure data,
   so cyclic closure does not authenticate the selectors.

These points give a precise dichotomy for the requested bounded construction.
If the selector reflections are literal group words, the mixed rows and any
orthogonal packing derived from them are valid in the regular tracial
representation and cannot be matrix-only.  If the selectors are
matrix-coordinate decodings, then `(MCI-ROW)` and `(MCI-CYCLE-SQ)` finish the
twist cancellation and error spreading, but an additional finite-matrix
authentication theorem is still required to charge their defects to ordinary
presentation words.  A cyclic product does not supply that theorem.

Accordingly no bounded twist-blind cyclic **group word** construction closes
this claim.  This is not a refutation of `(MCI1)`: a dimension-activated
selector, unbounded conductor, or matrix-dependent orthogonal packing could
still work.  It isolates the live compiler as matrix-only selector decoding,
not multiplicity synchronization or cyclic holonomy.

`global-marked-type-cycle-selector-decoder` records the non-circular global
form of that live compiler.  A finite type permutation is allowed to split
into many cycles, but the rows are compressed only after matrix packet
exactification.  Their squared energies pack through orthogonal isotypic
domains, rather than through a product holonomy word.  This bypasses the
inverse-cancellation objection above without turning any individual mixed row
into a universal identity.
