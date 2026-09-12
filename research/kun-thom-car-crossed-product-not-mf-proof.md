---
rg: 2
id: kun-thom-car-crossed-product-not-mf-proof
kind: route
title: Evaluate the Clifford central sign as the scalar minus one
target: kun-thom-car-crossed-product-is-not-mf
requires: [kun-thom-clifford-extension-not-weak-mf]
artifacts:
  - notes/FALSE_CLIFFORD_NORM_MF_STERILITY.md
---

# Evaluate the Clifford central sign as the scalar minus one

Write `E=C(X) semidirect G` for the complete Kun--Thom Clifford extension,
where `C(X)` has generators `z,c_x` and relations

```text
z^2=c_x^2=1,   z central,   c_x c_y=z c_y c_x  (x!=y).
```

Let `B` be either the full or the reduced C-star crossed product of
`A_CAR=Cl(X)` by the permutation Bogoliubov action of `G`.  Denote its
canonical Majoranas and actor unitaries by the same symbols `c_x` and `u_g`.
They satisfy all defining relations of `E` after setting

```text
z |-> -1_B.
```

Consequently, any unital star-homomorphism

```text
Phi:B -> Q=product_n M_(d_n)/directSum_n M_(d_n)
```

would induce a group homomorphism

```text
Theta:E -> U(Q),
Theta(c_x)=Phi(c_x),   Theta(g)=Phi(u_g),   Theta(z)=-1_Q.
```

But `kun-thom-clifford-extension-not-weak-mf` says that every group
homomorphism from `E` to a norm matrix corona satisfies `Theta(z)=1_Q`.
Since a norm matrix corona is nonzero and has `1_Q!=-1_Q`, this is impossible.
Thus neither crossed product has a unital norm-corona representation.

An MF embedding of a unital C-star algebra may be taken unital, so neither
crossed product is MF.  Notice that no exactness, nuclearity, or crossed-product
permanence assertion is used: the proof is only the central-sign evaluation
followed by the already established operator-norm sterility theorem.

Finally, the conclusion is deliberately not promoted to the von Neumann
category.  A trace-preserving embedding of the canonical tracial closure into
a tracial ultraproduct controls normalized Hilbert--Schmidt defects, not
operator-norm defects, and therefore does not contradict this proof.
