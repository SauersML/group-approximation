---
rg: 2
id: finite-clifford-cocycles-cancel-on-conjugate-multiplicity
kind: claim
title: Finite Clifford cocycles cancel on a conjugate multiplicity packet
distinct_from:
  inner-pauli-occurrence-labels-are-tietze-removable: that removes inner automorphism labels by a group-valued gauge; this treats genuinely outer Clifford labels and their projective cocycle.
  fixed-extraspecial-packet-is-morita-neutral-for-code-rounding: that uses the plain packet commutant; this builds the exact inverse-cocycle absorber required for normalizer transport.
---

# Finite Clifford cocycles cancel on a conjugate multiplicity packet

ESTABLISHED. Let `K` be the order-32 extraspecial Pauli group, let `rho` be
its unique four-dimensional irreducible representation with `rho(J)=-I`, and
let `A<=Aut(K)` preserve `J`. Choose Clifford intertwiners `C_alpha`:

```text
C_alpha rho(k) C_alpha^* = rho(alpha(k)).                 (CC1)
```

Schur's lemma gives the finite projective cocycle

```text
C_alpha C_beta = c(alpha,beta) C_(alpha beta),
c(alpha,beta) in U(1).                                   (CC2)
```

For commuting labels the induced commutation phase is

```text
b(alpha,beta)=c(alpha,beta)c(beta,alpha)^{-1}.            (CC3)
```

For a face `F=(alpha_1,...,alpha_q)` with product one, the Clifford product
is a scalar

```text
C_(alpha_1)...C_(alpha_q)=c_F I.                         (CC4)
```

Thus a normalizing occurrence operator

```text
r_i=C_(alpha_i) tensor Q_i
```

transfers the face relations to the multiplicity operators with precisely
the inverse finite phases: `Q_iQ_j=b(alpha_i,alpha_j)^{-1}Q_jQ_i` and
`product_F Q_i=c_F^{-1}I`. These are only fixed projective/affine LCS shifts.

They always admit a stationary finite-dimensional absorber. Complex
conjugation changes the cocycle to its inverse, so

```text
T_alpha=C_alpha tensor conjugate(C_alpha)                (CC5)
```

is an honest representation of `A`. Therefore, for **any** ordinary exact
homogeneous-face representation `{Y_i}` on an arbitrary Hilbert space,

```text
r_i=T_(alpha_i) tensor Y_i                               (CC6)
```

normalizes the first Pauli factor by `alpha_i` and satisfies every occurrence
involution, face commutator, and product relation whenever the automorphism
labels themselves commute and multiply to one on each face. All projective
phases cancel between `C` and `conjugate(C)`; the remaining relations are
exactly those on the `Y_i`.

Consequently every class-two or sparse-Clifford contextual model of the
underlying code lifts after one fixed 16-dimensional amplification. The
finite Clifford cocycle cannot force a growing common phase, eliminate the
multiplicity algebra, or yield same-Hilbert code rounding. Its rank and
absorber dimension are bounded independently of the code size.

This argument applies to any fixed finite packet with a distinguished
irreducible sector and a finite projective normalizer action. A surviving
finite-packet construction must impose multi-occurrence relations not pulled
back from a locally satisfied finite automorphism label system; otherwise the
conjugate projective packet cancels it exactly.

