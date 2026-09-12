---
rg: 2
id: rf-amenable-two-cell-retains-coefficient
kind: claim
title: Amenable two-letter compression cells retain every residually finite base coefficient
distinct_from:
  amenable-multi-compressors-have-a-joint-hs-telescope: that copies one fixed finite-dimensional representation through a Følner set; this chooses an adaptive regular quotient after the Følner window and proves exact retention of a prescribed algebraic coefficient and finite packet trace.
  rf-hnn-telescope-retains-coefficient-residual: that treats one stable letter by a cyclic interval; this treats simultaneous stable letters, their commutator or nilpotent relations, and every fixed two-cell relation already holding in an amenable compression semigroup.
  agent-aggregate-escape-two-intertwiner-clifford-dichotomy: that classifies exact finite projective packet holonomy by an inverse twisted stabilizer representation; this gives asymptotic countermodels for infinite coefficient endomorphisms and needs no finite packet factorization.
---

**ESTABLISHED AMENABLE TWO-CELL FENCE.**  Let `Lambda` be a finitely
generated residually finite group.  Let `P` be a finitely generated
right-cancellative semigroup with finite right Følner sets `F_n`, and let

```text
alpha:P->End(Lambda),       alpha_(pq)=alpha_p o alpha_q, (RAT1)
```

where every `alpha_p` is injective.  Fix a finite generating set `A` of `P`
and an algebraic coefficient

```text
b in C[Lambda].                                             (RAT2)
```

There are finite-dimensional exact representations `Pi_n` of `Lambda` and
unitaries `T_(n,s)`, `s in A`, such that

```text
||Pi_n(b)||_2=||lambda_Lambda(b)||_2,                       (RAT3)

||T_(n,s)Pi_n(g)T_(n,s)^(-1)-Pi_n(alpha_s(g))||_2
 <=2 sqrt(|F_n s triangle F_n|/|F_n|)                      (RAT4)
```

for every fixed `g in Lambda`.  Every fixed relation between words in the
stable letters which is an equality in `P` also has normalized-HS defect
tending to zero.  The models may simultaneously be made exactly canonical
on any prescribed finite base-group window and retain the canonical trace of
every projection in a prescribed finite packet subgroup.

Consequently no finite two-stable-letter cell whose closed two-cell is only
a relation in an amenable compression semigroup can pay a nonzero base
coefficient by ordinary relator energy.  This covers in particular:

1. two commuting injective endomorphisms, with `P=N^2` and two-cell
   `[u,v]=1`;
2. nilpotent/Hall--Witt stable-letter tables whose positive compression
   monoid is cancellative amenable;
3. the integral Heisenberg compressor monoid, including its relation
   `ab=cba` and every fixed consequence of that relation.

The conclusion still holds when the same coefficient occurrence is used in
both covariance rows: the two rows see the blockwise coefficients
`alpha_p(b)`, and `(RAT3)` shows that sharing the occurrence does not make it
small.

## Proof

Write `b=sum_(g in K)c_g g`.  For each Følner set `F=F_n`, residual
finiteness supplies one finite quotient

```text
q_F:Lambda->Q_F                                           (RAT5)
```

which separates every pair in every finite support set

```text
alpha_p(K),                   p in F.                    (RAT6)
```

It may at the same time separate all nonidentity elements in the finitely
many `alpha_p`-iterates of a requested base window and finite packet.  This
is possible because `F` is finite and every `alpha_p` is injective.

Put `rho_F=lambda_(Q_F) o q_F` and define

```text
H_F=direct_sum_(p in F) ell^2(Q_F),
Pi_F(g)|_(H_p)=rho_F(alpha_p(g)).                         (RAT7)
```

For `s in A`, use the block permutation from
`amenable-multi-compressors-have-a-joint-hs-telescope`: it sends
`H_(ps)` to `H_p` on the common domain and completes the boundary blocks by
an arbitrary bijection.  Covariance is exact on the common blocks, proving
`(RAT4)`.  For two stable-letter words representing the same element of
`P`, the induced block permutations agree whenever the finitely many prefix
translates stay in `F`.  Their disagreement is contained in a finite union
of right Følner boundaries, so every fixed two-cell defect tends to zero.

On the coefficient side, `(RAT6)` prevents collisions among the support
terms of every `q_F(alpha_p(b))`.  Hence for every `p in F`,

```text
||rho_F(alpha_p(b))||_2^2
   =sum_(g in K)|c_g|^2
   =||lambda_Lambda(b)||_2^2.                            (RAT8)
```

Average `(RAT8)` over the equal blocks in `(RAT7)` to obtain `(RAT3)`.
The canonical-window and finite-packet clauses follow by the identical
regular-trace separation argument.

## The coefficient-valued commutator boundary

There is a parallel permanence fence for an automorphic square.  Suppose
`alpha,beta in Aut(Lambda)` and `c in Lambda` define a consistent embedded
extension

```text
G=<Lambda,u,v |
    u g u^(-1)=alpha(g),
    v g v^(-1)=beta(g),
    [u,v]=c>,                                             (RAT9)
```

with amenable quotient `G/Lambda` (for the displayed square the quotient is
a quotient of `Z^2`).  Since residually finite groups are hyperlinear and
hyperlinear-by-amenable extensions are hyperlinear, `G` has canonical matrix
microstates.  For every nonzero `b in C[Lambda]`, those microstates satisfy

```text
E_pres->0,             ||b(U)||_2->||lambda_G(b)||_2>0. (RAT10)
```

Thus even the coefficient-valued commutator in `(RAT9)` cannot be the first
source of a coefficient payment.  The same argument covers any finite
Hall--Witt/nilpotent stable-letter presentation with a normal hyperlinear
kernel and amenable quotient.

This leaves a sharp first unfenced two-cell: it must generate a
**nonamenable** joint compression/holonomy quotient, or use a proper
endomorphism coefficient cocycle for which no amenable-kernel permanence or
right-Følner telescope exists.  Merely adding a second stable letter, a
commutator, a nilpotent Hall--Witt table, or a shared coefficient occurrence
does not cross the matrix-only gate.

The free-holonomy edge of that frontier is now fenced as well under the
natural simultaneous profinite hypothesis.
`profinite-free-compressors-retain-coefficient-residual` shows that if the
proper endomorphisms become automorphisms on common finite quotients, then
the free multiple-HNN covariance presentation has **exact** finite models
retaining every prescribed base coefficient.  This applies to the opposite
Kun--Thom transvections.  Hence the first unfenced cell must use a
stabilizer-sensitive mixed return or another relation that fails on those
common profinite automorphic foldings; nonamenability of the stable-letter
monoid alone is not sufficient.

## Bounded-type specialization

For the bounded-type coefficient `b=z(1-a)` of
`one-bounded-type-coefficient-separates-unbounded-exits`, the regular
representation gives

```text
||lambda_Lambda(b)||_2>=(1-epsilon)sqrt(q).              (RAT11)
```

Equations `(RAT3)--(RAT4)` therefore keep the full positive residual while
all amenable two-cell and covariance defects tend to zero.  A live
payload-sensitive two-cell must lie beyond the amenable cases above.

DERIVATION
rf-amenable-two-cell-telescope-proof
