---
rg: 2
id: determinant-index-cannot-authenticate-julia-heat-overlap
kind: claim
title: Determinant, parity and bounded index cannot authenticate the Julia heat overlap
distinct_from:
  additive-index-instability: that rules out converting an additive index to a fixed finite phase under amplification; this applies the same obstruction to the proposed heat-overlap selector and also records normalized-HS discontinuity of determinant.
  sublinear-block-poisons-normalized-torsion: that treats small singular-value tails in a general torsion detector; this isolates the finite-coordinate invariants available from the Julia pair of equal-rank projections.
  fixed-packet-julia-calculus-is-tracially-functorial: that rules out natural C-star operations on the multiplicity algebra; this rules out the discontinuous finite-dimensional invariants which might appear to evade that functoriality.
---

None of the elementary finite-dimensional invariants of the Julia pair
`E,Q_B` supplies a normalized-HS-stable authentication of
`tau(EQ_B)`.

1. `E` and `Q_B` have equal rank.  The square compression
   `EQ_B:E H -> E H` has ordinary Fredholm index zero.  The relative index
   of the equal-rank projection pair is also zero.
2. A bounded rank defect changes normalized trace by `O(1/d)` and can be
   hidden by direct-sum amplification.  Its parity or any fixed finite
   character is killed by a suitable amplification.
3. Determinant phase is not uniformly continuous in normalized HS norm.
   For fixed `theta`,

   ```text
   Z_d=exp(i theta/d) I_d
   ```

   satisfies `||Z_d-I||_2=O(1/d)` while
   `det(Z_d)=exp(i theta)`.  Thus a determinant certificate can change by a
   fixed phase under a vanishing normalized-HS perturbation.
4. The determinant of the Julia unitary itself has unit modulus and depends
   only on the fixed block parity after stabilization; it cannot record the
   singular-value mass `tr(B^*B)`.  Adding spectator packet copies changes
   determinant and additive indices while leaving all normalized microstate
   statistics and the heat overlap density unchanged.

Therefore any surviving index mechanism must be **extensive**: it must
force `Theta(d)` independent cutoff/matching failures on the same marked
reservoir.  This is equivalent to controlling a rank density, not a raw
integer, parity, determinant or one Fredholm defect.  A selected finite type
does not provide the required coordinate system by itself, because its
`U(m)` multiplicity gauge permits arbitrary rotations and amplifications.
