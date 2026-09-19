---
rg: 2
id: schur-packet-child-square-is-pauli-transverse
kind: claim
title: The two Schur packet children form a commuting square or two transverse Pauli MASAs
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  schur-complement-controls-relative-pauli-module: that constructs selector-controlled additive coefficients in the full packet algebra; this realizes their two one-generator halves as actual finite intermediate subgroups and computes the conditional-expectation geometry of their commutants.
  predicate-rank-gate-doubles-restriction-multiplicity: that counts restriction directly from the baseline packet to the full packet; this factors the rank gate through two binary child inclusions and identifies the forbidden factor as a pair of transverse MASAs.
  tensor-independent-child-carrier-gap: that gives an abstract orthogonality inequality for two tensor-independent child algebras; this proves the exact Schur packet supplies those two child algebras canonically on every forbidden sector.
---

Let `A_f<=B_f` be a Schur--Clifford predicate packet.  Define actual finite
intermediate subgroups

```text
B_f^P=<A_f,p_(N+1)>,                 B_f^Q=<A_f,q_(N+1)>.         (SPS1)
```

For every selector character `x`, with baseline spin dimension `D=2^N`, the
corresponding sector algebras are

```text
C[A_f]_x       = M_D,
C[B_f^P]_x     = M_D tensor C[C_2],
C[B_f^Q]_x     = M_D tensor C[C_2],                              (SPS2)
```

and their generated full-packet algebra is

```text
C[B_f]_x = M_D tensor C[C_2 x C_2]    if f(x)=0,
C[B_f]_x = M_D tensor M_2              if f(x)=1.                 (SPS3)
```

Thus the two children are compatible binary refinements on allowed sectors
and the `Z`- and `X`-MASAs of one relative Pauli qubit on forbidden sectors.
This encodes the nonlinear predicate using only genuine finite subgroup
inclusions; it does not name the nonlinear controlled phase as a group
element.

Quantitatively, on a forbidden `B_f`-simple with external multiplicity `m`,
write `H=S_x tensor C^2 tensor C^m`.  Let `E_P,E_Q,E_B` be the
Hilbert--Schmidt conditional expectations onto the commutants of
`B_f^P,B_f^Q,B_f`, respectively.  For every `Y in End_(A_f)(H)`,

```text
||Y-E_B Y||_2^2
 <= ||Y-E_P Y||_2^2 + ||Y-E_Q Y||_2^2.                           (SPS4)
```

Moreover the two centered child ranges

```text
range(E_P-E_B)=C Z tensor M_m,
range(E_Q-E_B)=C X tensor M_m                                  (SPS5)
```

are orthogonal and each has dimension `m^2`.  Hence a recurrent network that
returns one positive-density centered child module as the other must pay a
dimension-free HS defect.

Globally, let `K` be the number of forbidden selector assignments and let `q`
be forbidden Hilbert mass in a `d`-dimensional packet representation.  A
forbidden Schur matrix has full rank `N+1`, so there is one full-packet simple
over each forbidden `x` and no radical-character multiplicity.  The
orthogonal sum `K_PQ` of both centered child modules satisfies

```text
rank(K_PQ)/d^2 >= q^2/(2 D^2 K).                                 (SPS7)
```

All constants depend only on the fixed predicate packet.  The remaining task
is to force the return by an infinite compressor while preserving the exact
non-CE tracial model.
