---
rg: 2
id: atlas-shortest-escapee-leavitt-tracial-energy-proof
kind: route
title: Install the Leavitt chart conjugator and evaluate the three commutator words
target: atlas-shortest-escapee-has-exact-leavitt-tracial-energy
requires:
  - atlas-shortest-escapee-has-no-relator-telescope
  - leavitt-factor-regular-charts-inner-conjugate
  - leavitt-regular-atlas-hyperlinearity-criterion
---

# Exact energy in the canonical group factor

Put `M=L(Q)`.  By `leavitt-factor-regular-charts-inner-conjugate`, the two
labelled embeddings of `C[A8]` in `M` are conjugate by a unitary `W in M`.
This is exactly `(LTE1)`.  The canonical trace restricts to the regular
character on either finite chart, so the model has the same normalized
tracial chart margins as every finite regular amplification.

Every word in `T_St` belongs to the kernel of the canonical map to `Q`.
Therefore its evaluation under `(LTE1)` is `lambda_Q(1)=1`; all `4,636`
relator defects vanish exactly.

For unitaries `A,B`, multiplication on the right by `BA` gives

```text
||AB-BA||_2=||ABA^*B^*-1||_2.                         (LTP1)
```

The two dangerous group commutators were evaluated in
`atlas-shortest-escapee-has-no-relator-telescope`:

```text
[a_1,b_2] |-> x_13(1) !=1,
[a_1,c_2] |-> x_15(1)x_13(1) !=1.                    (LTP2)
```

For every nonidentity `q in Q`, the canonical group trace satisfies
`tau(lambda_Q(q))=0`, and hence

```text
||lambda_Q(q)-1||_2^2
 =2-2 Re tau(lambda_Q(q))=2.                          (LTP3)
```

Combining `(LTP1)--(LTP3)` proves the first two equalities in `(LTE2)`.
The third commutator is the literal relator

```text
[a_1,a_2]=orth_15_35_11,
```

so it evaluates to the identity in `Q` and its additive commutator norm is
zero by `(LTP1)`.  Substitution into the already established decomposition

```text
E_w=6||[A_a,B_b]||_2^2+3||[A_a,B_c]||_2^2
    +||[A_a,B_a]||_2^2
```

gives `(LTE3)` and `(LTE4)`.

Finally suppose `Q` is hyperlinear.  Its canonical group trace then embeds
trace-preservingly on group unitaries into a tracial matrix ultraproduct.
Choose representing matrix sequences for the finite set of chart letters,
relators, and the two words in `(LTP2)`.  Exact group identities make every
relator defect tend to zero, while trace preservation and `(LTP3)` make both
dangerous squared defects tend to `2`.  Finite-group correction of the two
`A8` restrictions, as in the regular Atlas criterion, puts the representatives
in exact regular chart form without changing these limits.  Hence `E_w` tends
to `18`, proving `(LTE5)`.  A uniform matrix coercivity inequality would pass
to this sequence and give `18<=0`, so it excludes hyperlinearity of `Q`.
