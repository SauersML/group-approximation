---
rg: 2
id: self-hashing-expander-collision-presentation-route
kind: route
title: Combine free-cone address hashing, self-similar expander words, relative cell coherence, and packet collision
target: self-hashing-expander-collision-presentation
requires:
  - free-cone-shift-finitely-wordizes-recursive-clifford-tails
  - finitely-presented-oligomorphic-linear-pauli-addresser
  - self-similar-clifford-quantum-expander-tape
  - uniform-relative-clifford-tape-cell
  - self-hashed-adversarial-collision-forces-mf-collapse
  - operator-norm-rank-monodromy-zero
artifacts:
  - research/artifacts/no-renormalization-adversarial-collision-compiler-2026-08-23.md
---

Use the free-cone shift to make every addressed recursion check a conjugate of
one root relator.  Install the Pauli packet and its exact infinite model from
the oligomorphic addresser.  The still-open self-similar expander tape must
then provide a constant set of checksum words at every prefix, and the
relative-cell theorem must be strengthened from one-step HS exactification to
coherent operator-norm exactification which leaves the old prefix unchanged.

Finally authenticate cross-packet graph edges, or a cyclic rank selector, by
the same finite root verifier.  The collision theorem or rank monodromy then
gives the finite-dimensional contradiction.

The route remains open because the self-similar expander syntax and coherent
depth-independent authentication are open. None of the established required
nodes alone supplies that missing composition.
