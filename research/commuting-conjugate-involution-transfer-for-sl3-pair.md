---
rg: 2
id: commuting-conjugate-involution-transfer-for-sl3-pair
kind: claim
title: The native commuting-conjugate involution cannot retain an interior overlap in arithmetic matrix microstates
distinct_from:
  projective-commutant-transfer-for-arithmetic-pair: that quantifies over every unitary and is qualitatively equivalent to full relative-commutant collapse; this quantifies only over a balanced involution whose first h-conjugate commutes with it, the extra native lamp relation that defeats the universal self-adjoint dilation.
  trace-zero-involution-projective-transfer-equals-rcc: that proves involution and trace-zero restrictions alone do not lower the RCC wall; this adds the indispensable joint relation with the h-conjugate.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that gives a countermodel to full RCC from one arbitrary base-coordinate unitary; this records the exact two-coordinate projection profile that remains a countermodel even after the new commuting-conjugate relation.
---

Put

```text
C=SL_3(Z) < A=SL_3(Z[1/2]),
h=diag(2,1,1/2),
```

and fix finite presentations/generating sets.  The **native qualitative
transfer** asks for the following.

Let `rho_n` be canonical regular-trace normalized-HS microstates of `A`, and
let `c_n` be unitaries satisfying

```text
||c_n-c_n*||_2 -> 0,        ||c_n^2-I||_2 -> 0,
tr(c_n) -> 0,
max_(s in S_C)||[c_n,rho_n(s)]-I||_2 -> 0,              (CCI1)
||[c_n,rho_n(h)c_n rho_n(h)^*]-I||_2 -> 0.              (CCI2)
```

Then

```text
1-|tr(c_n rho_n(h)c_n rho_n(h)^*)|^2 -> 0.              (CCI3)
```

This is OPEN.  It is strictly more source-specific than PRCC: the universal
dilation `[[0,u],[u*,0]]` used by
`trace-zero-involution-projective-transfer-equals-rcc` does not in general
commute with its `h`-conjugate, so that reduction no longer applies.

The exact remaining matrix geometry is a two-projection endpoint.  After
rounding `c_n`, put

```text
P_n=(I-c_n)/2,
Q_n=rho_n(h) P_n rho_n(h)^*.
```

Then `(CCI1)--(CCI2)` say, asymptotically,

```text
tr(P_n)=tr(Q_n)=1/2,
P_n in rho_n(C)',
[P_n,Q_n]=0.                                            (CCI4)
```

Writing `a_n=tr(P_nQ_n)`, one has

```text
tr(c_n rho_n(h)c_n rho_n(h)^*) = 4a_n-1,               (CCI5)
e = 1-|4a_n-1|^2 = 8a_n(1-2a_n).                       (CCI6)
```

Thus `(CCI3)` is exactly the assertion that the overlap cannot remain in the
interior:

```text
a_n -> 0  or  a_n -> 1/2.                              (CCI7)
```

Equivalently, along subsequences, either `Q_n` approaches `I-P_n` or it
approaches `P_n`.  This is the weakest currently isolated scalar gate for the
native two-point lamp.  It asks only for exclusion of one balanced commuting
two-projection profile, not correction of the whole actor representation and
not full relative-commutant equality.

**Tracial firewall.**  The exact coset Bernoulli crossed product

```text
L^infinity({+1,-1}^(A/C)) rtimes A
```

contains the base-coordinate involution `c` satisfying all exact versions of
`(CCI1)--(CCI2)` with

```text
tr(PQ)=1/4,
tr(c h c h^-1)=0,
e(c,h)=1.                                               (CCI8)
```

Therefore no argument valid in arbitrary finite tracial von Neumann algebras
can prove `(CCI3)`.  Connes embeddability of this crossed product would give
a matrix counterarchitecture and refute the claim.  The claim is precisely a
matrix-coordinate exclusion of the independent two-coordinate overlap.

## Attempts

- `commuting-conjugate-involution-is-balanced-overlap` gives the complete
  projection reduction `(CCI4)--(CCI7)` and proves that the old universal RCC
  dilation no longer supplies a counterexample: it does not preserve
  `[c,h c h^-1]=1`.
- The exact coset Bernoulli crossed product realizes the maximally interior
  value `a=1/4`.  Thus ordinary compactness, tracial SOS, and finite-von-
  Neumann-algebra identities cannot close the claim.  If that crossed product
  is Connes embeddable, its matrix lifts refute the claim outright.
- The remaining possible arithmetic input must act on the common four atom
  projections of `P` and `hPh*`.  Separate relative-commutant estimates for
  `C` and `hCh^-1` do not identify those atoms and therefore do not exclude
  the stationary Bernoulli profile.
- The finite presentation is the graph wreath product over the Hecke orbital
  graph `Theta_h`.  If the action `A curvearrowright Theta_h` is sofic, the
  graph-wreath permanence theorem makes the candidate sofic and refutes this
  transfer.  Existing automatic soficity covers amenable stabilizers, not the
  present stabilizer `SL_3(Z)`.  Thus a proof here necessarily proves the
  nonsoficity of this explicit nonamenable-stabilizer graph action.
