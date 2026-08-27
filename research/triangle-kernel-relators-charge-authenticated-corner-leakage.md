---
rg: 2
id: triangle-kernel-relators-charge-authenticated-corner-leakage
kind: claim
title: Triangle-kernel relators charge all leakage of their authenticated positive-density corners
distinct_from:
  finite-multipath-average-coercivity-has-exact-julia-absorber: that leaves complementary leakage as the exact analytic escape; this proves the native triangle relators pay that leakage once the multipath block is identified with a kernel-word compression.
  hadamard-selector-commutator-charges-two-path-leakage: that manufactures a two-path average and its complement as blocks of one transverse selector word; this applies directly to every triangle-kernel relator and requires no finite selector packet.
  compact-hyperbolic-km-regular-microstates-synchronize: that must construct a common regular carrier and identify its compressed kernel word with finite label paths; this supplies the complete analytic estimate after that construction.
---

**ESTABLISHED.**  Use the triangle presentation from
`triangle-colimit-llp-reduces-to-relator-local-splitting`:

```text
Gamma=G_0/<<N>>,              G_0=P_12 *_(P_2) P_23,
N=ker(P_1 *_(P_0) P_3 ->> P_13),
```

and fix a free basis `n_1,...,n_r` of `N`.  Let `pi` be any unitary tuple for
the generators of `G_0`, let `q` be any projection of trace `beta>0`, and put
`Y_a=pi(n_a)`.  Then

```text
tau_q(q Y_a^*(1-q)Y_a q)
 <= beta^(-1)||Y_a-I||_2^2.                            (TKL1)
```

Thus each native added two-cell `n_a=1` independently charges the complete
Julia leakage of its own word across every authenticated positive-density
carrier.  More generally, if `Z` is a unitary with `ZqZ^*=p`, then

```text
tau_q(qY^*(1-p)Yq)<=beta^(-1)||Y-Z||_2^2.              (TKL2)
```

Combine this with `finite-multipath-average-coercivity-has-exact-julia-absorber`.
If `A_1,...,A_m in qMq` are corner unitaries, `K=m^(-1)sum_i A_i`, and

```text
delta=||qY_aq-K||_(2,q),
```

then

```text
sum_(i,j)||A_i-A_j||_(2,q)^2
 <=2m^2 beta^(-1)||Y_a-I||_2^2+4m^2 delta.             (TKL3)
```

There is therefore no exact finite-dimensional Julia absorber once the
native kernel word and the additive block have been matched on the same
positive carrier: zero relator defect and zero matching defect force every
path to agree.  The remaining Kac--Moody problem is not another leakage
inequality.  It is the finite coefficient identity which constructs `q` with
uniform `beta` and proves `qY_aq` is close to the desired multipath average.
