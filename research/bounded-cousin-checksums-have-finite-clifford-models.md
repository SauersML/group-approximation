---
rg: 2
id: bounded-cousin-checksums-have-finite-clifford-models
kind: claim
title: Bounded cousin checksums and compressed holonomies retain finite marked Clifford models
distinct_from:
  first-cousin-cross-arm-breaks-three-state-reuse: that shows one asymmetric cross row detects a reused Pauli factor but has a fresh-factor escape; this tests the first balanced checksum and compressed address-holonomy attempts to combine several such rows in one word.
  bounded-tagged-mark-seam-complex-has-finite-row-range: that bounds outputs of connected pairwise mark-seam diagrams abstractly; this gives the explicit finite Clifford model for the binary-prefix commutator and holonomy words.
  fixed-arity-mark-fusion-has-finite-character-model: that treats an arbitrary genuinely non-pairwise product of conjugate marks by a character-linear model; this treats checksums carrying cousin Pauli arms and compressed address permutations inside a finite Clifford actor.
  full-depth-one-leavitt-menu-has-finite-clifford-model: that closes every depth-one occurrence and actor square in one finite model; this permits any fixed bounded number of cousin addresses and their compressed permutation holonomies.
artifacts:
  - research/bounded-cousin-checksum-clifford-proof.md
---

**ESTABLISHED SCOPED NONLINEAR-HOLONOMY FIREWALL.**  The first balanced
checksum for two cousin prefix pairs is

```text
Q_(alpha,beta)
 =[X_alpha,Z_alpha][X_beta,Z_beta]
  [X_alpha,Z_beta]^(-1)[X_beta,Z_alpha]^(-1).           (BCH1)
```

In the exact binary prefix table, the two diagonal commutators are `J` and
the two crossed commutators are one, so `Q_(alpha,beta)=J^2=1`.  If the two
cousins are instead identified with one reused Pauli pair, all four
commutators become `J` and the same checksum is still

```text
Q_(alpha,beta)=J^4=1.                                  (BCH2)
```

Thus the smallest symmetric product checksum is exactly blind to the
three-state collision.  More generally, any central product checksum in
which every collision edge occurs with even parity is blind for the same
reason.

The first compressed-conjugation alternative is also finite-model
compatible.  Let `D_alpha,D_beta` be the two address charts and use their
relative holonomy

```text
H_(alpha,beta)=D_alpha D_beta^(-1).                    (BCH3)
```

Any fixed bounded menu which asks `H_(alpha,beta)` to permute finitely many
named cousin Pauli arms, and closes only the resulting naturality squares,
has an exact finite monomial/Clifford model.  Give every cousin occurrence a
fresh Pauli factor and let the address holonomies act by the prescribed
finite permutations of those factors.  The common mark remains nontrivial.

This extends to every fixed bound `K`: a word or connected diagram assembled
from at most `K` cousin cells, central commutator outputs, pairwise returned
mark seams, and finite address permutations acts inside

```text
S_3 wr Sym(Omega_K)  semidirect  Clifford_(m_K),        (BCH4)
```

for finite `Omega_K,m_K`.  Its left regular representation is an exact
finite marked model of every null consequence of that bounded menu.
Therefore no such checksum or compressed conjugation proves `(BAC1)`.

An odd asymmetric checksum does detect a collision, but it contains an
unpaired cousin cross row and reduces to
`first-cousin-cross-arm-breaks-three-state-reuse`: finitely many such rows
are repaired by fresh factors, while an unbounded family has the established
relator-area obstruction.  Hence a successful fixed word must be genuinely
outside both classes.  It must impose a non-pairwise coefficient relation
whose value is not determined by central `J` parity and is not implementable
as a finite permutation/symplectic action on the cousin Pauli factors.
The separate fixed-arity fusion firewall shows that replacing pairwise seams
by one higher-arity product of conjugate marks still remains inside a finite
character model; the new relation must read noncommuting payload arms
essentially.

No Property `(T)`, Kazhdan input, stability theorem, or literature result is
used.

DERIVATION
bounded-cousin-checksum-clifford-proof
