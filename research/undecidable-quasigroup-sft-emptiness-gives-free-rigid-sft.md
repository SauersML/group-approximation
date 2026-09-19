---
rg: 2
id: undecidable-quasigroup-sft-emptiness-gives-free-rigid-sft
kind: claim
title: In a quasigroup spacetime any nonzero period forces a doubly periodic point, so if emptiness of its sub-SFTs is undecidable then a free quantum-rigid Z^2 SFT exists
distinct_from:
  permutive-triangle-sfts-are-quantum-rigid: that forces a doubly periodic point from a periodic row or column; this does it from a period in any direction, so aperiodic already means free, and adds the decidability dichotomy.
  free-minimal-triangle-permutive-sft-exists: that asks for a free minimal example; this gets a free (not necessarily minimal) example from an undecidability statement, and says what a refutation of that node would decide.
  small-window-quasigroup-sub-sfts-have-periodic-points: that is an exhaustive search at small windows; this is a uniform reduction with no size bound.
  triangle-permutive-existence-iff-hex-cone-determinism: that recodes the free minimal existence problem; this reduces free existence to a computability statement.
---

**ESTABLISHED (route `undecidable-quasigroup-sft-emptiness-gives-free-rigid-sft-proof`, unreviewed).**

Let `(Q, ⋆)` be a finite quasigroup and `X_⋆ = {x ∈ Q^(Z^2) : x(z+e_2) = x(z) ⋆ x(z+e_1)}`. For `A ⊆ Q^L`, let
`Ω(⋆, A)` be the set of points of `X_⋆` all of whose row words of length `L` lie in `A`. By the normal form in
`small-window-quasigroup-sub-sfts-have-periodic-points-proof` §1, every sub-SFT of `X_⋆` is some `Ω(⋆, A)`.

1. **Periods.** If a closed shift-invariant `Ω ⊆ X_⋆` has a point with a nonzero period `v ∈ Z^2`, then `Ω` has a
   doubly periodic point. So `Ω` is free iff it has no periodic point, iff it has no doubly periodic point.
2. **Dichotomy.** Exactly one of the following holds.
   - (D) Every nonempty `Ω(⋆, A)` has a periodic point. Then emptiness of `Ω(⋆, A)` is decidable, uniformly in
     the input `(⋆, A)`.
   - (F) Some `Ω(⋆, A)` is nonempty, free and quantum rigid, so `LC(Ω, k) ⋊ Z^2` is finitely presented over every
     field `k` (by `permutive-triangle-sfts-are-quantum-rigid`).
3. **Consequence.** If emptiness of `Ω(⋆, A)` is undecidable (the open claim
   `quasigroup-spacetime-sft-emptiness-is-undecidable`), then (F) holds. A free SFT whose crossed product is
   finitely presented then exists. By `matricial-aperiodic-sft-rings-are-not-quantum-rigid`, that crossed product is
   not exactly matricial.

**What it does not give.** Minimality. A minimal subsystem of the free SFT in (F) is free, but in general it is
not of finite type, and quantum rigidity is only known to pass to sub-SFTs. So (F) does not settle
`free-minimal-triangle-permutive-sft-exists`. What it does show is that the refutation form of that node, "every nonempty
sub-SFT of every quasigroup spacetime has a periodic point", is exactly (D). That refutation would therefore
imply a decision procedure for the tiling problem of this class. Any proof of it has to be at least as strong as
a decidability theorem.
