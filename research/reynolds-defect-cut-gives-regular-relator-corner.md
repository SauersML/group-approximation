---
rg: 2
id: reynolds-defect-cut-gives-regular-relator-corner
kind: claim
title: A Reynolds defect cut gives a large regular carrier and a polar two-path relator corner
distinct_from:
  triangle-kernel-relators-charge-authenticated-corner-leakage: that bounds leakage after a positive carrier has been named; this constructs a relation-dependent carrier commuting with one finite overlap subgroup and gives an explicit density/modulus.
  finite-multipath-average-coercivity-has-exact-julia-absorber: that permits arbitrary corner paths but leaves carrier invariance open; this uses the relator defect itself to force invariance and polar-corrects the compressed word.
  km-triangle-local-bimodules-have-finite-nonflat-models: that rules out carriers selected from local regular bimodule data alone; this consumes the kernel-word defect in the spectral selector and therefore lies outside that counterpacket.
---

**ESTABLISHED.**  Let `rho:H->U(D)` be an exact representation of a fixed
finite group, let `Y in U(D)`, and put

```text
d=||Y-I||_2,
Delta_H=|H|^(-1) sum_(h in H)
 rho(h)(Y-I)^*(Y-I)rho(h)^*.                           (RDC1)
```

For `s>0`, let `q=1_[0,s](Delta_H)` and `beta=tr(q)`.  Then `q` commutes
with `rho(H)` and

```text
beta >=1-d^2/s.                                        (RDC2)
```

If `beta>0`, put `C=qYq`.  There is a unitary `B in qM_Dq` extending the
polar part of `C` such that

```text
tr_q(q-C^*C) <= |H|s,
||C-B||_(2,q) <= sqrt(|H|s),
||C-q||_(2,q) <= sqrt(|H|s).                           (RDC3)
```

Consequently the genuine two-path average

```text
K=(q+B)/2                                               (RDC4)
```

satisfies

```text
||qYq-K||_(2,q) <= sqrt(|H|s).                         (RDC5)
```

Choosing `s=d` for `0<d<1` gives

```text
beta>=1-d,             ||qYq-K||_(2,q)<=sqrt(|H|d).    (RDC6)
```

If the ambient `H`-representation is a multiple of `Reg(H)`, then the
`H`-invariant range of `q` contains a regular `H` summand of ambient relative
dimension at least

```text
max(0,1-|H|(1-beta)).                                  (RDC7)
```

Thus a triangle kernel word `Y=pi(n_a)` canonically supplies a uniformly
positive regular-overlap carrier and a coherent polar two-path average as its
defect tends to zero.  This is relation-dependent and so evades every exact
local-bimodule counterpacket.

The one-word construction does not synchronize the whole Kac--Moody
triangle.  The former finite-family cut and polar-gauge issue is settled by
`summed-reynolds-cut-synchronizes-kernel-corners`; what remains is transport
of that common overlap-subgroup carrier through the larger rank-two charts.
