---
rg: 2
id: perfect-scalar-root-and-two-commutators-proof
kind: proof
title: Perfectness fixes the scalar phase while opposite commutators expose both Toeplitz endpoints
target: scalar-rephased-toeplitz-sections-still-collapse-head
requires:
  - binary-gl-finite-sections-have-no-projective-k2-phase
  - boundary-transvection-is-conjugate-to-head-proof
---

## The two endpoint words

In the Tietze-expanded presentation set

```text
R_TS=[U,V]C^(-1),
W_Q=C[U',V'].
```

The exact Steinberg identities give

```text
R_TS=[x_12(T),x_23(S)]x_13(1)^(-1)=1,
W_Q=x_13(1)[x_14(S),x_43(T)]=x_13(1-ST).                (PSR1)
```

The last minus sign equals plus in characteristic two.

After truncated-shift substitution, write

```text
B_N=X_13(P_(N-1)),                 H_N=X_13(P_0).
```

The finite-section calculation gives

```text
R_TS |-> B_N,                     W_Q |-> H_N,           (PSR2)
```

before scalar rephasing, and `B_N,H_N` are conjugate in
`GL_(28N)(F_2)`.

Now multiply every named generator by an arbitrary scalar. Scalars cancel
from a commutator. If `gamma` is the scalar attached to the named
constant root `C`, then in any ordinary representation `rho_N),

```text
R_TS |-> gamma^(-1)rho_N(B_N),
W_Q  |-> gamma rho_N(H_N).                              (PSR3)
```

All phases on the four raw roots disappear exactly.

## The constant-root phase is forced by the finite scalar group

The fixed scalar group

```text
K=GL_28(F_2)
```

is perfect. Hence, for the fixed finite generating set used in the
presentation, there are fixed words `p_l,q_l`, `1<=l<=s`, such that

```text
C=product_(l=1)^s [p_l,q_l]                             (PSR4)
```

inside `K`.

Adjoin `C` and `(PSR4)` by a Tietze move if they are not already
named. In a scalar-rephased finite-section sector, every scalar belonging
to `p_l` or `q_l` cancels from its commutator, while the ordinary
matrix parts multiply exactly to `rho_N(C)). Therefore the evaluated
word

```text
C^(-1) product_l[p_l,q_l]
```

is exactly the scalar `gamma^(-1)I).

Because this fixed word has a fixed derivation from the presentation
relators, there is a presentation-dependent constant `A` such that

```text
|gamma-1|<=A delta                                      (PSR5)
```

in one sector. For a direct sum with sector-dependent phases, let
`Gamma` be the block-scalar unitary whose blocks are the corresponding
`gamma)'s. The identical fixed derivation gives

```text
||Gamma-I||_2<=A delta.                                 (PSR6)
```

Thus cancellation among different scalar sectors does not help.

## Uniform comparison

For a direct sum of sectors, use `rho(B)` and `rho(H)` for the
corresponding block sums. Sectorwise conjugacy and additivity of squared
normalized Hilbert--Schmidt norm give

```text
||rho(B)-I||_2=||rho(H)-I||_2.                          (PSR7)
```

From `(PSR3)`,

```text
||rho(B)-I||_2
 <=||Gamma^(-1)rho(B)-I||_2+||Gamma-I||_2
 <=||R_TS-I||_2+A delta.                                (PSR8)
```

Using `(PSR6)--(PSR8)` for the head word,

```text
||W_Q-I||_2
 =||Gamma rho(H)-I||_2
 <=||rho(H)-I||_2+||Gamma-I||_2
 <=||R_TS-I||_2+2A delta.                               (PSR9)
```

The named relator defect `||R_TS-I||_2` is at most `delta`; if it is
only a fixed derived word, a further fixed filling-area factor appears.
Absorbing these constants proves `(SRT1)` uniformly in every matrix and
representation dimension.

Every projective finite-section representation linearizes by the
vanishing-Schur-class theorem. A chosen projective lift is exactly an
ordinary linearization followed by the scalar rephasings treated above.
Therefore `(PSR9)` closes both the genuine multiplier and scalar
one-cochain versions of the projective Toeplitz finite-section route.

Nothing in this proof extracts truncated shifts from an arbitrary
approximate representation. Nonscalar perturbations can destroy the exact
form `(PSR3)`; controlling those perturbations is the remaining global
Jacobson rigidity gate.
