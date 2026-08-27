---
rg: 2
id: full-q-zero-sector-is-not-canonical-a1-closed
kind: claim
title: The old full-Q zero sector has a multiplicity-at-most-two block and is not canonically A1-closed
artifacts:
  - research/full-q-zero-sector-canonical-a1-adjacency-proof.md
  - experiments/full_q_zero_block_character_audit.cpp
distinct_from:
  full-q-separate-actor-packet-retains-zero-cross-central-block: that proves existence of an abstract zero-cross simple block for the separate finite packet; this bounds the smallest old zero-block multiplicity and determines what canonical A1 must do to the entire zero sector.
  full-q-a1-binary-extension-closes-zero-cross-block: that proves full central support by a 176-dimensional finite audit; this extracts its exact representation-theoretic consequence and states the finite-intersection hypothesis still needed for arbitrary full-group profiles.
  row2-source-factor-detects-paid-pauli-sheet: that proves global nontriviality of the A1 and S57 sheet commutators but no source compression; this shows why the factor relations alone do not yet imply the canonical A1 adjacency in every representation.
---

**ESTABLISHED CANONICAL-EXTENSION EXCLUSION.**  Put

```text
B=F C[P] F,                  h=F(J_1J_2)F,
I=BhB,                       Z=B/I.                    (ZAE1)
```

The exact separate-actor calculation gives

```text
dim(B)=52,                   dim(I)=44,
dim(Z)=8.                                                (ZAE2)
```

Since `B` is a corner of a finite complex group algebra, it is a
finite-dimensional semisimple star algebra, and so is `Z`.  If its simple
matrix blocks have sizes `d_1,...,d_s`, then

```text
d_1^2+...+d_s^2=8.                                    (ZAE3)
```

Consequently the old zero-cross sector contains a simple type with

```text
dim(FV)=min_i d_i <=2.                                 (ZAE4)
```

Thus the missing `P`-simple can be chosen with full-Q multiplicity one or
two; it is not forced to be a large unidentified constituent.

Now adjoin the canonical binary image

```text
bar(A_1)=x_(u1,q4)(1),       C=F C[P_A] F,
P_A=<P,bar(A_1)>.                                      (ZAE5)
```

The established extension audit proves the exact identity

```text
ChC=C.                                                 (ZAE6)
```

Hence no nonzero `C`-module can restrict to a direct sum of old zero-cross
`B`-types.  Indeed, if `hV=0`, then every element of `ChC` kills `V`, so
`(ZAE6)` says that the identity kills `V`.  Equivalently, whenever an old
zero type occurs in the restriction of a canonical `P_A`-module, its
`A_1`-orbit is forced to meet a positive-cross `P`-type.  In particular,
neither the multiplicity-at-most-two block in `(ZAE4)` nor any sum of the
old zero blocks is closed under the canonical `A_1` adjacency.

This is the precise module-theoretic content of the index-`31` binary
extension.  On its own, the finite calculation would not promote to every
representation of the actual Steinberg packet: that requires identifying
the literal `A_1`--`P` subgroup with the canonical finite group.  That
identification is now supplied by
`full-q-a1-projective-head-is-a-literal-finite-subgroup`, which removes the
formerly possible multiplicity gauge.  The weaker facts `A_1Q=QA_1` and
`[A_1,H]=x_43(a_1h)` would not have sufficed by themselves.

The supplementary exact normalizer audit records eight singleton twisted
double cosets, with unsigned multiplication `C_2^3`; its three elementary
coset generators may be represented by

```text
q2 -> u1,                 u2 -> u3,                 u1 -> u2.  (ZAE7)
```

This thin algebra alone is not the zero quotient: modulo `1000003`, the
old ideal plus the thin algebra has rank only `48`, not `52`.  Thus a
normalizer-character shortcut cannot identify all old zero types, and the
canonical `A_1` exclusion genuinely uses the enlarged corner `(ZAE6)`.

No Property `(T)`, canonical trace, local computation, or literature input
is used.

DERIVATION
full-q-zero-sector-canonical-a1-adjacency-proof
