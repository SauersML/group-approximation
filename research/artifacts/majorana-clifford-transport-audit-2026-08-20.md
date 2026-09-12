# Majorana Clifford transport audit

**Source.** Valerie Bettaque and Brian Swingle, *The Structure of the
Majorana Clifford Group*, arXiv:2407.11319v2.  Audited from the complete TeX
source supplied by the user on 2026-08-20.

## Imported dictionary

The paper represents a Hermitian Majorana string by `v in F_2^(2n)` and uses
the nondegenerate alternating form `omega=I^c` for commutation.  Its parity
is the ordinary binary quadratic form `v^T v`.  A Clifford conjugation acts
symplectically; preserving the quadratic form cuts the action down to
`O(2n,2)`.

The useful constructive statement is that the even Householder reflection

```text
v -> v+(a^T v)a
```

is exactly the conjugation action of
`exp(i*pi*mu(a)/4)`.  The authors then reduce every nonexceptional even
reflection to weight-two and weight-four reflections and give a polynomial
decomposition procedure.  This is a clean source-level certificate that a
binary-orthogonal change of a Majorana frame is realized by an honest finite
unitary word rather than by a projection-controlled operator.

## Relevance to Cairn

This is useful for constructing and auditing literal word transports in the
S3 radical and Clifford-lamp regions.  Given a proposed linear action, the
tests are now explicit:

1. preserve the commutation form;
2. preserve the parity quadratic form;
3. factor the resulting orthogonal matrix into even reflections;
4. replace the reflections by braid words.

The paper also proves that, after fixing parity and quotienting by the
all-ones vector, the effective action is `Sp(2n-2,2)` and the restricted
frame potential is the ordinary Clifford frame potential.  This is negative
guidance for the current V4 bottleneck: merely enlarging from a Pauli frame
to every parity-preserving Majorana Clifford frame does not manufacture a
fifth independent character tag.  A successful five-way router must still
use the commutant/Wedderburn multiplicity data or another contextual
non-character invariant.

## What was not imported

The source is exact finite-dimensional Clifford/stabilizer theory.  It gives
no quantitative control of approximate group relations in normalized
Hilbert--Schmidt norm.  Its unitary-design result is therefore not a
local-to-global defect-spreading theorem, and Cairn does not treat it as one.
