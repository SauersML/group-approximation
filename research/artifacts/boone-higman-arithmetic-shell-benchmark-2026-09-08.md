# Arithmetic shell maps and the deterministic finite-state boundary, 2026-09-08

The direct perfect-input shell route remains open. The group A_5 * A_5
is an explicit perfect finitely presented decidable input occurring in
the perfect-envelope construction. It is a useful test of attempts to
obtain presentations beyond the virtually cyclic positive control.

## A sharper finite-state obstruction

A suffix-preserving shell map h_pi fixes 0^infinity. In a deterministic
finite-state transducer, reading this all-zero input eventually traverses
one state cycle. If it consumes m zeros and emits a zeros per cycle,
then pi(n+m)=pi(n)+a for all sufficiently large n. The m source residue
rays have disjoint image tails of step a, and bijectivity makes them
exhaust all a target residue rays. Hence a=m.

Conversely an eventual m-periodic shell permutation has bounded
displacement and can be implemented with a finite initial output delay
and finite residue memory. Thus rational shell maps are exactly the
eventually periodic translations of shell indices.

Taking a common period across finitely many generators and using the
input's free even-index orbit proves that a finitely generated infinite
input admits this rational regular shell action exactly when it is
virtually cyclic. This is a restriction on the concrete shell action,
not on all rational embeddings of the abstract input.

In particular an arithmetic formula whose slope varies between residue
classes is not, for that reason, a deterministic finite-state transducer.
The all-zero cycle cannot choose its output rate based on a residue it
will only learn when the arbitrarily distant first 1 is read.

## Verification boundary

These are written proofs in Cairn. Structural validation checks their
dependencies, not the mathematical arguments themselves. No GPU ran,
no local code or build was executed, and no Civo resource was created.
No finite presentation of the perfect-input shell benchmark is claimed.
