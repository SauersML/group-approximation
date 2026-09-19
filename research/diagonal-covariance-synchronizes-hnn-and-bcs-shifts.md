---
rg: 2
id: diagonal-covariance-synchronizes-hnn-and-bcs-shifts
kind: claim
title: Finite diagonal covariance synchronizes the HNN and BCS shifts without collapsing height
---

Let `t` be an ascending-HNN stable letter, let `U` be a distinct BCS shift
word, and let `Z={z_1,...,z_s}` be a finite set of BCS words. Add the finite
relations

```text
[t,U]=1,       [t U^(-1),z_i]=1        (1<=i<=s).               (DC1)
```

Then, for every `n>=0`,

```text
t^n z_i t^(-n)=U^n z_i U^(-n).                              (DC2)
```

The new relations have total `t`-exponent zero, so the HNN height character
survives. Moreover, if `pi_T` is any unitary representation of the HNN
skeleton and `pi_B` any unitary representation of the BCS group words, the
assignments

```text
h |-> pi_T(h) tensor I,
z |-> I tensor pi_B(z),
U |-> I tensor pi_B(U),
t |-> pi_T(t) tensor pi_B(U)
```

give an exact representation of the diagonal-covariance skeleton. Any marked
BCS word remains nonidentity whenever it was nonidentity under `pi_B`.

