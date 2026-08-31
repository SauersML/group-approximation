---
rg: 2
id: x2-local-afd-holds-on-abelian-packets
kind: claim
title: Popa's local-AFD criterion holds exactly on abelian packets
distinct_from:
  x2-local-afd-holds-at-rate-controlled-packets: that cell pays for non-commutativity with an approximation rate; this cell is rate-free but demands that the packet commute, and the two together shape the counterexample profile stated in the body.
  popa-projection-formulations-of-x2: that is the equivalence of formulations quantified over all packets; this establishes the criterion's instances on the abelian locus, with s = 1 and exact commutation.
artifacts:
  - research/artifacts/x2-shadow-avoidance-recon-2026-08-31.md
---

Let `Y = {y_1,…,y_j}` lie in an abelian von Neumann subalgebra
`A ⊂ R` and `ε > 0`.  Then Popa's local-AFD condition holds at
`(Y, ε)` with `s = 1`: there is a finite-dimensional \*-subalgebra
`B ⊂ A` with `[y_i, 1] = 0` and `‖y_i − E_B(y_i)‖ < ε`.

Consequences for the shape of any X(2) counterexample packet:

* **Singletons never obstruct.**  A single normal element is an
  abelian packet.  A single non-normal `y` is equivalent, for the
  local-AFD conditions, to the self-adjoint pair
  `{(y+y*)/2, (y−y*)/2i}` — so the smallest possible obstruction is a
  genuinely non-commuting PAIR of self-adjoint contractions.
* **Small-support bad mass never obstructs.**  If the packet's
  deviation from an abelian (or finite-dimensional) part is supported
  under projections of summable small trace, the projection
  `s = 1 − (join of supports)` kills it exactly (`z s = z(z^*z)s = 0`
  when `s ⊥ z^*z ∨ zz^*`), reducing to the handled part.  In
  particular the column-isometry family of
  `shadow-avoidance-fails-at-column-isometries`, as a PACKET, is
  handled instantly this way — it defeats only the commutant-form
  reduction, not local AFD.
* **Counterexample profile.**  Any packet refuting X(2) must
  therefore contain a non-commuting pair whose non-abelian mass has
  essentially full support (so it cannot be cut), no controlled
  2-norm approximation rate (`x2-local-afd-holds-at-rate-controlled-packets`),
  and no commuting reorganization — e.g. two Haar unitaries in
  sufficiently generic position.  Conversely the positive route may
  now assume all of this about the packet it must handle.
