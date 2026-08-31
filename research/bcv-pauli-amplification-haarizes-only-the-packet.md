---
rg: 2
id: bcv-pauli-amplification-haarizes-only-the-packet
kind: claim
title: Exact BCV Pauli amplification makes the packet Haar but leaves the source-fiber trace arbitrary
distinct_from:
  bcv-every-perfect-question-reduction-amplifies-readable-closure: that proves the universal tensor inclusion of readable algebras; this computes the trace on that tensor form and shows why the inclusion is not a canonical groupification.
  controlled-pauli-corner-has-clifford-groupification: that realizes a finite controlled-Pauli covariance by a group element while leaving its multiplicity involution uncontrolled; this applies the same multiplicity boundary to the entire BCV Question Reduction packet.
  finite-invariant-partition-only-reduces-irs-to-fiber-irs: that gives the corresponding IRS boundary for a finite invariant object partition; this gives an explicit Pauli/source tensor formula and a padded one-question ZPC countermodel.
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
equivalently the canonical trace of the twisted Weyl matrix algebra. It is
not the canonical group trace of `P_k`: the Pauli representation has
`tau_S(J)=-1`, whereas `J` is a nonidentity group element and
`tau_(L(P_k))(J)=0`.

For a controlled source observable from BCV equation `(51)` and Remark
4.22 item (6),

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
zero-translation words retain arbitrary source-fiber moments. In
particular,

```text
tau_S(1 tensor b)=tau_T(b).                              (PHT7)
```

## A perfect ZPC countermodel to canonical group trace

Take a padded one-question synchronous tailored game with a fixed dummy
readable coordinate and one linear/unreadable answer bit. The predicate
requires the dummy coordinate to have its fixed value and tests synchronous
equality of the unreadable bit. Equivalently, start with this one-question
game and apply BCV Padding so the Question Reduction source has the required
positive equal answer lengths.

Every signed-permutation involution `U` on `C^m`, used at both ends of
the sole loop, is a perfect ZPC strategy. The readable dummy measurement is
scalar and the sampler is constant. Its honest Question Reduction lift
therefore has

```text
C=1 tensor U
```

and the same forced Pauli packet for every choice of `U`. For `m=3)
take

```text
U=diag(1,1,-1).
```

This is a faithful representation of `C_2`, but
`tau_S(C)=1/3`, while the canonical trace of the nonidentity element of
`C_2` is zero. The choices `I`, `diag(1,1,-1)`, and
`diag(1,-1,-1)` give traces `1,1/3,-1/3` with identical Pauli
relations and packet trace. Hence perfect Question Reduction cannot
promote the whole target character to a canonical group character.

## Recursion does not wash out the tail

For any finite chain of `r` exact inverse steps in the BCV HALT fixed
point, composing the monomial normal forms gives

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

If one separately supplies compatible embeddings for an infinite packet
chain, its norm closure is the `2^infinity` UHF C*-algebra, and its weak
closure in the product trace is the hyperfinite `II_1` factor. The BCV
fixed-point syntax does not itself supply those compatible embeddings. An
attained finite-dimensional strategy cannot contain infinitely many
nontrivial packet factors because its dimension is divisible by every
finite product `product_j 2^(k_j)`. In neither setting do the packet
equations force a nontrivial tail trace to become regular.

There is a second, independent obstruction. On

```text
D=L(F_2^k)=ell^infinity(F_2^k),
```

the packet relation

```text
X^a Z^c X^(-a)=(-1)^(a dot c) Z^c                       (PHT10)
```

acts by translation on the spectrum of `D`. A nonzero translation does
not fix the trivial character, so this action is not dual to an
automorphism of the lamp group. The crossed product
`D rtimes F_2^k=M_(2^k)` is the finite translation pair-groupoid, or
equivalently the negative central Pauli corner. It is not a site-shift
semidirect product. A lamplighter action needs a separate automorphism that
fixes the identity character and permutes lamp coordinates.

## Syntactic self-reference is not a level-shift endomorphism

Lemma 2.59 identifies two game descriptions at a fixed pre-halting index.
The backward decoder sends a chosen strategy `S_j` to a different
strategy `S_(j+1)` for a different index, after restrictions,
coarse-grainings, sheet selection, and a monomial normal form. None of the
printed identities supplies

- a single ambient tracial algebra containing all levels compatibly;
- a functorial choice of the decoder and its packet corners;
- a trace-preserving endomorphism carrying level `j` to level `j+1`;
  or
- a normalizing unitary implementing that endomorphism.

Thus the syntactic fixed point does not imply a unitary `v` with
`v D_j v^*=D_(j+1)`, does not make the finite tensor splittings nested,
and does not create a crossed product. A positive fixed-point
groupification would require these coherent intertwiners as an additional
hypothesis, not merely the existence of each finite-step factorization.

## Exact extra hypothesis that would groupify

Let `A_0` be a countable discrete abelian lamp group,
`K=dual(A_0)`, and let a countable group `Lambda` act on `A_0).
Suppose one additionally has

1. a coherent copy `D=L^infinity(K,Haar)`;
2. a genuine unitary representation `g |-> v_g` of `Lambda`
   normalizing `D` and implementing the dual action; and
3. a trace-preserving conditional expectation satisfying

```text
E_D(v_g)=0 for every g != e,                             (PHT11)
```

equivalently `tau(d v_g)=0` for all `d in D` and `g != e`.

Then the algebraic integrated representation preserves the faithful
canonical crossed-product trace. It therefore extends to a normal
injective homomorphism whose image is `W^*(D,{v_g})), giving a
trace-preserving copy

```text
L(A_0 semidirect Lambda)
  = L^infinity(K) rtimes Lambda.                         (PHT12)
```

Taking `A_0=direct_sum_Z C_2` and `Lambda=Z` acting by the site shift
gives the lamplighter group. BCV Question Reduction supplies only finite
Haar packet marginals. It supplies neither a coherent level/site shift nor
`(PHT11)`, and `(PHT5)--(PHT9)` exhibit the uncontrolled source fiber
that blocks those conclusions.
