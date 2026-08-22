---
rg: 2
id: diagonal-retention-fusion-coefficient
kind: claim
title: Diagonal self-retention is exactly a positive-kernel Rayleigh coefficient
distinct_from:
  fixed-density-polarization-retention-is-terminal: that identifies the canonical central summand forced by a uniform retained weight; this gives the exact finite-word coefficient whose positivity is equivalent to retention and proves its decay whenever the canonical limit is CE
  diagonal-tensor-trace-powers-forget-full-gns-tensor: that warns that the full tensor product does not survive in the diagonal algebra; this quantifies precisely how much of the original tracial representation does survive
---

Let `tau` be a character of a countable group `G`.  For every positive
integer `n`, define its **diagonal fusion coefficient**

```text
d_n(tau) = inf {
  tau^n(a* a) / tau(a* a) :
  a in C[G], tau(a* a)>0
}.                                                        (DRC1)
```

Here `tau^n(g)=tau(g)^n`, extended linearly to `C[G]`.  Then

```text
d_n(tau)=max { beta in [0,1] : tau^n-beta tau is positive }.
                                                               (DRC2)
```

Consequently, for `0<=beta<1`, the following are equivalent:

1. `d_n(tau)>=beta`;
2. there is a character `rho` such that
   `tau^n=beta tau+(1-beta)rho`;
3. the diagonal `n`-fold tracial representation retains the `tau` GNS
   representation with tracial fusion weight at least `beta` (in the
   character/direct-summand sense).

Thus `(DRC1)` is an exact representation-category criterion, not just a
necessary scalar moment test.  Writing `a=sum_i c_i g_i` turns it into the
finite Gram-kernel quotient

```text
 sum_ij conj(c_i)c_j tau(g_i^-1 g_j)^n
 -------------------------------------------------- .          (DRC3)
 sum_ij conj(c_i)c_j tau(g_i^-1 g_j)
```

Now suppose `n_k` is unbounded and

```text
tau^(n_k) -> phi_H=1_H                                  (DRC4)
```

pointwise, as in character polarization.  Define `d_infty(tau)` by replacing
`tau^n` in `(DRC1)` by `phi_H`.  Then

```text
limsup_k d_(n_k)(tau) <= d_infty(tau).                  (DRC5)
```

In particular, if the canonical quotient algebra `L(G/H)` is Connes
embeddable while the GNS algebra of `tau` is not, then

```text
d_infty(tau)=0,
d_(n_k)(tau) -> 0.                                      (DRC6)
```

Indeed, positive `d_infty` would give `beta tau<=phi_H` for some `beta>0`.
The central Radon--Nikodym argument would realize the `tau` GNS algebra as a
central tracial summand of `L(G/H)`, contradicting CE permanence under
corners and central summands.

This gives a decisive audit of fusion/self-similarity proposals.  A uniform
positive recurrence coefficient along polarizing tensor powers is possible
only if the scalar-kernel quotient already has the desired non-CE canonical
summand.  Abstract isomorphism of tensor factors, recurrence of an
irreducible label, or preservation inside the full tensor product does not
meet `(DRC1)`.
