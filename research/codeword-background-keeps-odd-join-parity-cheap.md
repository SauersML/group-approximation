---
rg: 2
id: codeword-background-keeps-odd-join-parity-cheap
kind: claim
title: A codeword background keeps every bounded dual parity face cheap while the odd-cut join boundary stays macroscopic
distinct_from:
  orthogonal-odd-cut-join-amplifies-boundary-linearly: that does not impose parity words; this completes the construction against every bounded-width dual row and computes the exact face defects.
  balanced-parity-excludes-perfect-matching-pauli-mixtures: that forces constant energy for a far projective matching packet; this construction has vanishing balanced energy but is itself vanishingly close to an exact code tuple.
  translated-three-site-blocks-defeat-global-peeling: that centrally translates sparse Pauli defects to refute one global coordinate set; this is one noncentral direct-sum model aimed specifically at the boundary of the joined physical projection.
---

ESTABLISHED.  Let `C_L<=F_2^L` be any binary code with a codeword
`c=(c_i)` of density `rho=|c|/L`.  Present `C_L` by any family of dual rows
`h in C_L^perp` of width at most `w`, including all bounded local-dual rows,
repeated original rows, and bounded-width pair sums.  There are reflections
`A,B_1,...,B_L` for which, at every fixed `0<s<=1`,

```text
 p_i=1_[s,1](((B_i-AB_iA)/2)^2)
```

are pairwise orthogonal and, for `p=join_i p_i`,

```text
 (1/L)sum_i ||[p,B_i]||_2^2=rho(1-1/L),                (CBJ1)
 (1/L)sum_i ||[A,B_i]||_2^2=2/L,                       (CBJ2)
 (1/L^2)sum_(i,j)||[B_i,B_j]||_2^2
   =4rho(L-1)/L^2.                                      (CBJ3)
```

For a dual row `h`, in any fixed ordering of its parity word,

```text
 ||prod_(i in h)B_i-I||_2^2
   =(|h|+|h intersect supp(c)|)/L <=2w/L.              (CBJ4)
```

The within-face commutator defect of a pair `i!=j` is

```text
 ||[B_i,B_j]||_2^2=2(c_i+c_j)/L<=4/L.                  (CBJ5)
```

Assigning the same `B_i` to all equality copies makes the equality layer
exact.  Hence every normalized layer of the balanced presentation has
energy `O_w(1/L)`; repeating original faces and adding bounded pair-sum or
all-local-dual faces does not change this order.  If the code family has
relative distance and `c!=0`, then `rho` is bounded below, so the join
boundary in `(CBJ1)` is nevertheless constant.

This rules out a parity-aware estimate of the unnormalized row boundary

```text
 D(p)<=C_s E_balanced                                  (CBJ6)
```

even for the all-local-dual balanced overlay.  It does **not** rule out the
correctly normalized estimate `D(p)/L<=C_s E_balanced`, which is tight on
this family.

Nor is this a far balanced countermodel.  The exact commuting code tuple

```text
 Bbar_i=direct_sum_(j=1)^L S^(c_i)
```

satisfies every dual parity word, and

```text
 ||B_i-Bbar_i||_2^2=(1+c_i)/L,
 (1/L)sum_i||B_i-Bbar_i||_2^2=(1+rho)/L.               (CBJ7)
```

Thus the parity completion identifies the right conclusion sharply: local
dual faces do not make the bare join boundary small, but the cross-boundary
profile is a sparse, cheaply repairable deviation.  Any terminal theorem
must either charge `D(p)/L` at the complete-pair normalization or branch to
the existing sparse/block-adaptive reset, rather than demand `D(p)=o(1)`.
