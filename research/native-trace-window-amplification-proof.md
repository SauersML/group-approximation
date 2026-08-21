---
rg: 2
id: native-trace-window-amplification-proof
kind: route
title: Tensor a failed finite window until the native edge energy is macroscopic
target: native-transfer-has-finite-trace-certificate
requires: []
---

The implication `(NTC4) =>` qualitative transfer is immediate: regular
microstates make `sep_F->0`, while all three terms in `d_cc` vanish.

For the converse, enumerate the nonidentity elements of `A` by increasing
finite windows

```text
F_1 subset F_2 subset ... ,       union_n F_n=A-{1}.      (NTA1)
```

If no pair `(F,L)` satisfies `(NTC4)`, then for every `n` there are
`rho_n,c_n` with

```text
e_n=e_h(rho_n,c_n)
 > n(d_cc(rho_n,c_n)+sep_(F_n)(rho_n)).                  (NTA2)
```

In particular `e_n>0`.  Put

```text
k_n=ceil(1/e_n),
tilde rho_n=rho_n^(tensor k_n),
tilde c_n=c_n^(tensor k_n).                              (NTA3)
```

Every relevant word and every lamp commutator tensors diagonally.  Word
telescoping therefore gives

```text
d_cc(tilde rho_n,tilde c_n)
 <= k_n d_cc(rho_n,c_n) <= 2/n.                          (NTA4)
```

The trace-zero involution condition is preserved.  For `g in F_n`,

```text
|tr(tilde rho_n(g))|=|tr(rho_n(g))|^(k_n) <=1/n,         (NTA5)
```

using `(NTA2)` and `e_n<=1`.  Hence `(tilde rho_n)` has the canonical regular
trace on every fixed word.  On the other hand normalized traces multiply, so

```text
e_h(tilde rho_n,tilde c_n)
 =1-(1-e_n)^(k_n) >=1-exp(-1).                           (NTA6)
```

Equations `(NTA4)--(NTA6)` give a regular-trace native leak, contradicting
qualitative transfer.  This proves the equivalence.

For approximate lamp involutions, replace the almost self-adjoint involution
by its spectral sign; all fixed-word defects change by a vanishing amount.
If the rounded involution is not exactly balanced, replace the entire tuple
by

```text
rho'(x)=rho(x) tensor I_2,
c'=c tensor diag(1,-1).                                  (NTA7)
```

Then `tr(c')=0`, while the two lamp commutators and the target product are
the old operators tensored with the identity.  Their normalized
Hilbert--Schmidt defects and trace-square energy are unchanged.
