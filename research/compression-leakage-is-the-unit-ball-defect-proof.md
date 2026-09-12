---
rg: 2
id: compression-leakage-is-the-unit-ball-defect-proof
kind: route
title: Compute the exact compression defect and separate marked tests from the unit ball
target: matrix-ulam-stability-needs-full-unit-ball-control
requires: []
---

# Exact compression identity

Let `pi:M_n(C)->N` be a unital star homomorphism into a tracial von
Neumann algebra and let `p` be a nonzero finite projection. Give `pNp`
its normalized trace. The map

```text
phi_p(x)=p pi(x) p
```

takes contractions to contractions. It is linear, star preserving, and
unital as a map to `pNp`, whose unit is `p`. For contractions `x,y`,

```text
phi_p(xy)-phi_p(x)phi_p(y)
 = p pi(xy) p - p pi(x) p pi(y) p
 = p pi(x) (1-p) pi(y) p.                         (1)
```

Therefore its uniform multiplicative defect is exactly the supremum in
(MUS2). There is no loss or hidden dimension factor in this identity.

Definition 2.1 of Alekseev--Thom tests (1) for every pair of contractions.
It also tests additivity whenever `x,y,x+y` are contractions, homogeneity
for every scalar of modulus at most one, and the star and unit operations.
Theorem 3.5 then gives a modulus independent of `n`, a semifinite
amplification, a finite projection `q`, and a unital star homomorphism into
`qPq` uniformly close to `phi_p` on the whole source unit ball. Thus the
theorem applies to the compression exactly after the supremum in (MUS2) is
small.

# A sharp marked-test counterexample

Take `N=M_2(C)`, `p=e_11`, and `pi` the identity representation. Put

```text
u = diag(1,-1),   x=e_12,   y=e_21.
```

The marked unitary relation `u^2=1` survives compression exactly:

```text
phi_p(u^2)=p=phi_p(u)^2.                           (2)
```

On the other hand, `xy=p`, while `phi_p(x)=phi_p(y)=0`. Hence

```text
phi_p(xy)-phi_p(x)phi_p(y)=p.                      (3)
```

The normalized trace on the one-dimensional corner satisfies
`||p||_2=1`. Thus the full unit-ball multiplicative defect equals one even
though the displayed marked relation has defect zero.

This example does not say that no presentation can ever control (MUS2).
It says that such control is an additional quantitative theorem: it must
show that the selected relations generate all contraction-pair leakages
with constants uniform in the matrix size. Neither the cited Ulam theorem
nor the formal Stinespring construction proves that implication.
