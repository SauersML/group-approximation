---
rg: 2
id: fixed-phase-tensor-coset-closure-proof
kind: route
title: Tensor m plus one fixed-phase representations and translate the resulting polyadic closure
target: fixed-central-phase-scalar-profiles-form-coset-subgroup
requires: []
---

Take any `m+1` profiles `xi^(0),...,xi^(m)` in `Sigma_m`, realized by
representations `pi_0,...,pi_m`.  Their tensor product is again an allowed
representation and satisfies

```text
(pi_0 tensor ... tensor pi_m)(J)=zeta^(m+1) I=zeta I.
```

Its scalar interface profile is the coordinatewise product

```text
xi^(0) xi^(1) ... xi^(m).
```

Thus `Sigma_m` is closed under `(m+1)`-fold multiplication.

Assume it is nonempty, choose `s in Sigma_m`, and put

```text
H=s^(-1) Sigma_m subset mu_m^n.
```

Then `1 in H`.  If `h,k in H`, apply `(m+1)`-fold closure to the profiles

```text
sh, sk, s, ..., s
```

with `m-1` final copies of `s`.  Their product is

```text
s^(m+1)hk=shk,
```

because every coordinate of `s` has order dividing `m`.  Hence `hk in H`.
Likewise apply closure to `m-1` copies of `sh` and two copies of `s`.  The
product is

```text
s^(m+1)h^(m-1)=s h^(-1),
```

so `h^(-1) in H`.  Therefore `H` is a subgroup and

```text
Sigma_m=sH.
```

Only closure under tensor products and the displayed scalar identities were
used, so the proof is unchanged for any tensor-closed representation class.

