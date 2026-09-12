---
rg: 2
id: full-q-zero-sector-canonical-a1-adjacency-proof
kind: route
title: Pass from the old cross ideal to the canonical A1 adjacency obstruction
target: full-q-zero-sector-is-not-canonical-a1-closed
requires:
  - full-q-separate-actor-packet-retains-zero-cross-central-block
  - full-q-a1-binary-extension-closes-zero-cross-block
---

Let

```text
B=F C[P] F,                  h=F(J_1J_2)F.
```

The exact fraction-free relative-corner calculation, transported to the
separate-actor packet by equality of the two twisted corners, gives

```text
dim(B)=52,                   dim(BhB)=44.              (1)
```

The quotient `Z=B/BhB` is semisimple because `B` is a finite-dimensional
semisimple complex algebra: use the standard block decomposition of the
finite group algebra and compress by `F`.  Every two-sided ideal in such an
algebra is a direct sum of full matrix blocks.  Therefore

```text
Z ~= direct_sum_i M_(d_i)(C),
sum_i d_i^2=52-44=8.                                  (2)
```

If every `d_i` were at least `3`, the sum in `(2)` would be at least `9`.
This proves the multiplicity bound in `(ZAE4)`.

For the canonical extension put

```text
C=F C[P_A] F.
```

The exact integral compatible-orbit calculation followed by a nonzero
minor modulo `1000003` proves

```text
ChC=C.                                                 (3)
```

The required adjacency statement is the following elementary finite-corner
lemma.

> If `B<=C` are unital finite-dimensional algebras, `h in B`, and
> `ChC=C`, then the restriction to `B` of no nonzero `C`-module is
> annihilated by `h`.

Indeed, write the identity as a finite sum

```text
1_C=sum_j c_j h d_j.
```

If `hV=0` as a `B`-operator, the right side kills `V`, contradicting the
action of `1_C`.  Since a semisimple `B`-module is annihilated by `h`
exactly when all its constituents belong to the quotient `(2)`, this proves
that canonical `A_1` cannot close on the old zero sector.

The finite-intersection issue is logically separate from `(1)--(3)`.
Merely knowing the intersection action on `Q`, or the global nonzero sheet
commutator, would not construct the needed map or remove an occurrence
gauge.  The subsequent literal projective-head theorem resolves this issue
by identifying `<P,A_1>` itself with the canonical finite group, so every
full-group representation restricts to a genuine `C`-module and the lemma
applies without a Mackey assumption.

`experiments/full_q_zero_block_character_audit.cpp` independently enumerates
the singleton normalizer cosets and their exact multiplication.  It runs
only on MSI.  The modular rank printed there is diagnostic only; equations
`(1)--(3)` are supplied by the established exact corner calculations.
