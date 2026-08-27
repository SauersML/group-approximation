---
rg: 2
id: schur-packet-flips-realize-predicate-cocycle-proof
kind: route
title: Flip the two last generators and implement the flips by the opposite relative Pauli operators
target: schur-packet-flips-realize-predicate-cocycle
requires:
  - schur-packet-child-square-is-pauli-transverse
  - commuting-automorphism-cocycle-forces-multiplicity
---

Multiplying one involutory generator by the central involution `J` preserves
its square, all centrality relations, and every prescribed commutator.
Therefore both maps in `(SPF1)` extend to automorphisms of `B_f`.  They touch
different generators, so they commute, and they fix all generators of `A_f`.

Fix a selector sector.  The corrected operator `P_x` is the last `p`
generator times a product of leading `p` generators.  Thus `alpha_P` sends it
to `J P_x` and fixes `Q_x`; similarly `alpha_Q` fixes `P_x` and sends `Q_x`
to `J Q_x`.  In the `J=-1` sector these are sign flips.

If `f(x)=1`, `(SCP7)` says `P_x,Q_x` anticommute.  Conjugation by `Q_x`
therefore flips `P_x` and fixes `Q_x`, while conjugation by `P_x` flips
`Q_x` and fixes `P_x`.  Both commute with the baseline packet, so they
implement the two automorphisms on the full simple block, proving `(SPF2)`;
their anticommutation gives `(SPF3)`.  The full forbidden sector algebra is a
matrix algebra, hence its unique simple is invariant.

If `f(x)=0`, `P_x,Q_x` commute and the four characters of their relative
`C_2 x C_2` algebra label the four simple extensions.  The two automorphisms
flip the corresponding signs, so neither produces a projective obstruction
on the full orbit sum; their permutation implementers commute.

Finally apply `commuting-automorphism-cocycle-forces-multiplicity` with
`zeta=-1` to each invariant forbidden simple in `(SPF4)`.  Its external
multiplicity is divisible by two.
