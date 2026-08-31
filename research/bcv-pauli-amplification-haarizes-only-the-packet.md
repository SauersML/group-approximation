---
rg: 2
id: bcv-pauli-amplification-haarizes-only-the-packet
kind: claim
title: Exact BCV Pauli amplification makes the packet Haar but leaves the source-fiber trace arbitrary
distinct_from:
  bcv-every-perfect-question-reduction-amplifies-readable-closure: that proves the universal tensor inclusion of readable algebras; this computes the trace on that tensor form and shows why the inclusion is not a canonical groupification.
  controlled-pauli-corner-has-clifford-groupification: that realizes a finite controlled-Pauli covariance by a group element while leaving its multiplicity involution uncontrolled; this applies the same multiplicity boundary to the entire BCV Question Reduction packet.
  finite-invariant-partition-only-reduces-irs-to-fiber-irs: that gives the corresponding IRS boundary for a finite invariant object partition; this gives an explicit Pauli/source tensor formula and a one-question ZPC countermodel.
---

**ESTABLISHED.** In the exact normal form of
`bcv-every-perfect-question-reduction-amplifies-readable-closure`, put
`A=F_2^k` and use normalized traces. Then

```text
tau_S = tr_A tensor tau_T,                               (PHT1)
tau_S(e_z tensor b)=2^(-k) tau_T(b),                     (PHT2)
tau_S((X^a Z^c) tensor b)
  = delta_(a,0) delta_(c,0) tau_T(b).                    (PHT3)
```

Thus the Pauli matrix factor has its unique normalized trace and the
readable SamZ algebra `ell^infinity(A)` has the uniform, or Haar, law.
The source multiplicity trace `tau_T` is unchanged.

This is canonization of a matrix corner, not of an ordinary group trace.
Let `P_k` be the extraspecial Pauli group of BCV Definition 3.64, with
central involution `J`, and put `p_-=(1-J)/2`. Definition 3.68,
equation `(45)`, and Remark 3.70 identify

```text
p_- L(P_k) p_- = M_(2^k)(C).                             (PHT4)
```

The state in `(PHT1)` is the normalized trace of this `J=-1` corner,
equivalently the canonical trace of the twisted Weyl matrix algebra.
It is not the canonical group trace of `P_k`: the Pauli representation
has

```text
tau_S(J)=-1,
```

whereas `J` is a nonidentity group element and
`tau_(L(P_k))(J)=0`.

For a controlled source observable from BCV equation `(51)` and
Remark 4.22 item (6),

```text
C_j=sum_z e_z tensor U_(s(z),j),
tau_S(C_j)=2^(-k) sum_z tau_T(U_(s(z),j)).               (PHT5)
```

More generally, if `C=sum_z e_z tensor C_z` and
`D=sum_z e_z tensor D_z`, then

```text
tau_S(C X^a D X^(-a))
  =2^(-k) sum_z tau_T(C_z D_(z+a)).                      (PHT6)
```

Words with nonzero total Pauli translation have zero trace, but
zero-translation words retain arbitrary source-fiber moments. In particular,

```text
tau_S(1 tensor b)=tau_T(b).                              (PHT7)
```

## A perfect ZPC countermodel to canonical group trace

Let `G_0` be the one-question tailored game whose readable answer is empty,
whose linear/unreadable answer is one bit, and whose only test is synchronous
equality. Every signed involution `U` on `C^m` is a perfect ZPC strategy.
The sampler is constant, so its honest Question Reduction lift has

```text
C=1 tensor U
```

and the same forced Pauli packet for every choice of `U`. For `m=3` take

```text
U=diag(1,1,-1).
```

This is a faithful representation of `C_2`, but
`tau_S(C)=1/3`, while the canonical trace of the nonidentity element of
`C_2` is zero. The choices `I`, `diag(1,1,-1)`, and
`diag(1,-1,-1)` give traces `1,1/3,-1/3` with the identical Pauli
relations and packet trace. Hence no consequence of perfect Question
Reduction alone can promote the whole target character to a canonical
group character.

## Recursion does not wash out the tail

After `r` exact inverse steps, composing the monomial normal forms gives

```text
H_0 =
  (tensor_(j<r) ell^2(F_2^(k_j))) tensor H_r,

tau_0 =
  (tensor_(j<r) tr_(2^(k_j))) tensor tau_r.              (PHT8)
```

Every finite seed/Z marginal is product Haar, but

```text
tau_0(1 tensor b)=tau_r(b).                              (PHT9)
```

An infinite compatible packet union is the hyperfinite `2^infinity` UHF
factor, while an attained finite-dimensional strategy cannot contain
infinitely many nontrivial factors because its dimension is divisible by
`product_j 2^(k_j)`. In neither case do the packet equations force a
nontrivial tail trace to become regular.

The Pauli-X operators only implement dual translations inside a packet:

```text
X_i Z_j X_i^*=(-1)^(delta_(i,j)) Z_j.                   (PHT10)
```

They do not supply a unitary shifting recursion levels or lamp sites.
Therefore the forced packets do not by themselves produce a lamplighter
semidirect product.

## Exact extra hypothesis that would groupify

Let `A_0` be a countable discrete abelian lamp group,
`K=dual(A_0)`, and let a countable group `Lambda` act on `A_0`. Suppose
one additionally has

1. a coherent copy `D=L^infinity(K,Haar)`;
2. a genuine unitary representation `g |-> v_g` of `Lambda` normalizing
   `D` and implementing the dual action; and
3. the trace-preserving conditional expectation satisfies

```text
E_D(v_g)=0 for every g != e,                             (PHT11)
```

equivalently `tau(d v_g)=0` for all `d in D` and `g != e`.

Then the integrated representation gives a trace-preserving copy

```text
L(A_0 semidirect Lambda)
  = L^infinity(K) rtimes Lambda.                         (PHT12)
```

Taking `A_0=direct_sum_Z C_2` and `Lambda=Z` acting by the shift gives
the lamplighter group. BCV Question Reduction supplies only the finite
Haar-marginal part of item 1. It supplies neither a coherent level shift
nor `(PHT11)`, and `(PHT5)--(PHT9)` exhibit the uncontrolled source fiber
that blocks those conclusions.
