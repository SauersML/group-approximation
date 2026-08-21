---
rg: 2
id: mixed-relations-force-holonomy-or-transverse-recovery
kind: claim
title: The compulsory Pauli overlap must either carry a fixed holonomy or be recoverable from both transverse descendants
artifacts:
  - research/artifacts/pauli-overlap-dichotomy-2026-08-20.md
distinct_from:
  pauli-block-tail-or-flat-rigidity-dichotomy: that splits on the singular-value distribution of the sixteen raw-to-comb blocks and its flat branch ends in the constant-block contraction gap; this splits on what happens to an overlap that already exists and its second branch ends in the tensor-independence gap.
  same-orbit-closure: that asks for closure of a rectangular escape under a common orbit, in the whole-map formalism; this asks the mixed relations to force one of two positive-energy alternatives on a specific compulsory overlap.
  multiplicity-return-transducer: that asks for a returning multiplicity wire at fixed packet scale in the Schur-Clifford lane; this asks for a dichotomy on the raw/comb overlap and consumes no predicate compiler.
---

Let `Q` be the transported coefficient corner of the fixed raw/comb Pauli
packet and let the compulsory overlap of
`pauli-packet-incoming-mass-exceeds-corner-capacity` be present, so that some
pair of transported operators has ordered cross-Gram mass at least `5/32`.
By `pauli-overlap-yields-positive-spectral-corner`, after choosing one of two
orientations there is already a canonical spectral projection `R_0` of trace
at least `5/123` on which the oriented product is bounded below by
`sqrt(5/128)`.

The exact packet is stronger still:
`transported-coefficient-corners-share-flat-quarter-carrier` identifies one
canonical projection `F_0=P_0P_1` of trace exactly `1/4` common to the two
transported coefficient corners.  It is flat against all four raw character
cuts and stays at squared distance `23/128` from their algebra.  Thus the
word "same" is closed at the transported-corner level; the open content is
to force recovery of this same `F_0` in the two *descendant algebras*, not to
manufacture or align two unrelated carriers.

**Claim.**  There are fixed constants `c>0`, `kappa>0`, independent of matrix
dimension, such that in every sufficiently accurate atlas microstate at least
one of the following holds on a subcorner `R` of trace at least `c`:

**(HOL)**  Two fixed mixed `A_4`/`A_8` relator words restrict on `R` to
`U tensor H_1` and `V tensor H_2` with `H_1,H_2` commuting and `U,V` distinct
reflections of the standard two-dimensional representation of `S_3`.

**(TRV)**  One and the same projection `F <= R` of trace at least `c` lies
within `kappa` in normalized Hilbert--Schmidt distance of **both** transverse
descendant algebras -- the raw child algebra and the Fourier/comb child algebra
-- which are trace-independent.

In case `(HOL)`, `fixed-holonomy-on-overlap-pays-relator-energy` gives
`||[X,Y]-1||_2^2 >= tau(R) >= c`.  In case `(TRV)`,
`tensor-independent-child-carrier-gap` gives
`dist_2(F,A)^2 + dist_2(F,B)^2 >= tau(F)(1-tau(F))`, so `kappa` cannot be small.
Either way a fixed positive energy is paid.

## Attempts

- **Why the second branch is the interesting one.**  The known countermodel is
  rectangular escape (`rectangular-escape`): a child map `V -> V (+) V` pays for
  its doubling by halving multiplicity, so total dimension is unchanged and no
  absolute divisibility argument sees it.  `(TRV)` is the proposal to stop
  paying for it twice: raw and comb self-similarity in transverse coordinates
  cannot both use the same multiplicity reservoir as the disappearing half.
  The certificate for that is already proved and already in this graph as
  `tensor-independent-child-carrier-gap`, with the value `3/32` at `c=1/4`.
  **The missing content is entirely the word "same"**: the relations must force
  one common carrier into both descendants, not merely a carrier into each.
- **The multiplicative form of the same obstruction.**  If an edge between
  equal-density finite-coordinate sectors expands the label factor by `q_e` it
  consumes multiplicity by `q_e^(-1)`, so on an exactly surviving sector a
  closed cycle satisfies `prod_e q_e = 1`, and a positive-density cycle with
  `prod_e q_e > 1` must lose mass.  This is the reason a single doubling can
  hide while a doubling that returns to the same multiplicity reservoir cannot,
  and it is the cycle form of
  `finite-graph-of-groups-representation-types-are-integer-flows`.
- **Do not expect either branch from Bass--Serre data.**  A finite graph of
  finite groups is virtually free and hyperlinear, so no gluing of that shape
  can force `(HOL)` or `(TRV)` on a positive-density corner.  The relations must
  be genuinely two-dimensional holonomy, or compressor/self-similar.
- **The positive corner is now supplied.**  The former first gap—extracting a
  fixed-density corner from the `5/32` overlap—is closed by
  `pauli-overlap-yields-positive-spectral-corner`, with trace `5/123` and
  singular-value floor `sqrt(5/128)`.  The remaining gap is to show that a
  fixed portion of this corner obeys `(HOL)` or `(TRV)` under the mixed words.
- **The exact common carrier is also supplied.**  The later exact calculation
  `transported-coefficient-corners-share-flat-quarter-carrier` improves the
  soft corner to a canonical trace-`1/4` projection common to both transported
  corners.  It does not by itself put that projection into the raw and comb
  descendant algebras; that transverse recovery is the remaining use of the
  mixed rank-five relations.
- **The character tables do not secretly supply transverse recovery.**  The
  common quarter carrier is far from both the raw and comb four-cut algebras,
  commutes with none of their atoms, and is not the transported quarter
  carrier from the earlier branch-transfer packet.  Their first overlap is
  `1/16`, exactly the product of their traces, but their second overlap is
  `3/64`; consequently their projection reflections have commutator energy
  exactly `1/2`.  Hence “common” at the transported-corner level does not
  identify the earlier membership decoder, but the exact packet already
  supplies the desired holonomy object.  The remaining `(HOL)` work is now to
  expose those two Hecke reflections as legal derived-packet words and make a
  mixed rank-five return require trivial holonomy.  Alternatively the mixed
  words must prove `(TRV)` for the same carrier.
- **Falsification gate, inherited.**  Any proof of this claim must be checked
  against the exact model: the compulsory overlap exists there too, so an
  argument that derives `(HOL)` or `(TRV)` from the overlap alone, without using
  a property the exact atlas model fails, is wrong.  Compare
  `supercritical-network-needs-noncanonical-cuts` and
  `multiplicity-surplus-is-blind-to-the-non-ce-input`, which are the same gate
  in the two neighbouring lanes.
