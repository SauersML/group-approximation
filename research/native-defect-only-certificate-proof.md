---
rg: 2
id: native-defect-only-certificate-proof
kind: route
title: Amplify a failed native inequality and camouflage it by separating finite quotients
target: native-transfer-has-defect-only-certificate
requires: []
---

The implication `(NDC3) =>` qualitative transfer is immediate.  Conversely,
suppose no constant in `(NDC3)` exists.  Enumerate the nonidentity elements
of `A` in increasing finite windows

```text
F_1 subset F_2 subset ... ,       union_n F_n=A-{1}.      (NDP1)
```

For every `n` choose `rho_n,c_n` such that, writing

```text
epsilon_n=d_cc(rho_n,c_n),       e_n=e_h(rho_n,c_n),
```

one has `e_n>n epsilon_n`.  Put `k_n=ceil(1/e_n)` and take diagonal
tensor powers

```text
rho_hat_n=rho_n^(tensor k_n),
c_hat_n=c_n^(tensor k_n).                               (NDP2)
```

Word telescoping and multiplicativity of normalized trace give

```text
d_cc(rho_hat_n,c_hat_n) <= k_n epsilon_n <=2/n,
e_h(rho_hat_n,c_hat_n)
 =1-(1-e_n)^(k_n) >=1-exp(-1).                          (NDP3)
```

Residual finiteness supplies a finite quotient `q_n:A->K_n` which keeps
every element of `F_n` nonidentity.  Let `lambda_n` be its left regular
representation and define

```text
rho_tilde_n(x)=rho_hat_n(x) tensor lambda_n(q_n(x)),
c_tilde_n=c_hat_n tensor I.                             (NDP4)
```

Every relator has its old evaluation tensored with the identity.  Because
the lamp is trivial on the quotient factor, its subgroup commutators, its
commuting-conjugate defect, and its target word also have their old
evaluations tensored with the identity.  Therefore both quantities in
`(NDP3)` are unchanged.  On the other hand, for `g in F_n`,

```text
tr(rho_tilde_n(g))
 =tr(rho_hat_n(g)) tr(lambda_n(q_n(g)))=0.               (NDP5)
```

Thus `(rho_tilde_n)` is a regular-trace microstate sequence, its native
defect tends to zero, and its target energy stays at least `1-exp(-1)`,
contradicting qualitative transfer.

Tensor powers preserve self-adjoint involutions and preserve trace zero.
For approximate lamps, spectral-sign rounding changes every fixed word by a
vanishing amount.  Tensoring once with `diag(1,-1)` makes the rounded lamp
exactly balanced while leaving all lamp commutators and the target word
tensored with the identity.

For `SL_3(Z[1/2])`, a quotient separating a prescribed finite set can be
chosen directly.  Write its elements as matrices over `Z[1/2]` and choose
one odd prime avoiding a nonzero numerator from each difference `g-I`.
Reduction modulo that prime is defined and keeps every selected element
nonidentity.
