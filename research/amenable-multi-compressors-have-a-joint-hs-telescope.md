---
rg: 2
id: amenable-multi-compressors-have-a-joint-hs-telescope
kind: claim
title: Amenable multi-compressor covariance has a joint normalized-HS telescope
distinct_from:
  one-compressor-covariance-has-free-hs-telescope: That uses an interval for one injective endomorphism; this uses right Følner sets for an entire cancellative compression monoid and simultaneously respects its finite relations.
  kt-single-compressor-canonical-lamps-do-not-exactify-actor: That supplies canonical lamp-rich microstates for one actual Kun--Thom wreath; this gives the joint two-compressor covariance countermodel for the Heisenberg pair but does not assert the full canonical Bernoulli trace.
  commutator-compressor-carries-no-wall: That uses multiplicativity of exact Pimsner--Popa indices to constrain a commutator wall; this constructs approximate matrix covariance for the two commutator factors at vanishing normalized-HS cost.
---

**ESTABLISHED.**  Let `P` be a right-cancellative
semigroup with finite right Følner sets `F_n`, and let

```text
alpha:P -> End(Lambda),       alpha_(pq)=alpha_p circle alpha_q. (AMC1)
```

For any finite-dimensional representation `rho:Lambda->U(d)`, put

```text
H_F=direct_sum_(p in F) C^d,
Pi_F(g)|_(H_p)=rho(alpha_p(g)).                         (AMC2)
```

For each generator `s` of `P`, define a block permutation `T_s` which agrees
with

```text
T_s:H_(ps)->H_p                                           (AMC3)
```

whenever `p,ps in F`, and complete the remaining equally many source and
target blocks by an arbitrary bijection.  On every good block,

```text
T_s Pi_F(g) T_s^(-1)=Pi_F(alpha_s(g)).                  (AMC4)
```

Consequently

```text
||T_s Pi_F(g)T_s^(-1)-Pi_F(alpha_s(g))||_2
 <=2 sqrt(|Fs triangle F|/|F|).                         (AMC5)
```

The same construction respects every fixed finite semigroup relation.  If
two words `u,v` represent the same element of `P`, the block permutations
`T_u,T_v` agree on the blocks whose finitely many prefix translates stay in
`F`.  Their disagreement is contained in a finite union of Følner
boundaries, hence

```text
||T_u-T_v||_2=o_F(1).                                   (AMC6)
```

Every relation internal to `Lambda` is exact in every block of `(AMC2)`.
Thus finite lamp, Reynolds, selector, and commutant tables carried by
`Lambda` survive unchanged; their compressor transports fail only on the
same Følner boundary.  This is a joint multiplicity-cocycle model, not a
separate one-dimensional telescope for each compressor.

## The Kun--Thom Heisenberg pair

For the explicit polynomial Kun--Thom pair, take

```text
a=u_13=I+e_13,       b=u_32=I+e_32,       c=u_12=I+e_12.
```

They are positive compressors and satisfy

```text
ab=cba,              c central in <a,b>,               (AMC7)
```

so their positive compression semigroup is the integral Heisenberg monoid.
It has normal forms `c^k b^j a^i`.  The boxes

```text
F_L={c^k b^j a^i: 0<=i,j<L, 0<=k<L^2}                 (AMC8)
```

are right Følner.  Right multiplication by `a` loses only the face `i=L-1`.
Using `a^i b=c^i b a^i`, right multiplication by `b` loses the face `j=L-1`
and at most the top `i` values of the `k` coordinate.  Therefore

```text
|F_L a triangle F_L|/|F_L|=O(1/L),
|F_L b triangle F_L|/|F_L|=O(1/L).                    (AMC9)
```

Equations `(AMC5)--(AMC6)` give simultaneous normalized-HS error
`O(L^(-1/2))` for both compressor covariances and the Steinberg commutator
relation `(AMC7)`, uniformly in the dimension and in the coefficient
representation `rho`.

Hence the first two incompatible positive compressors do **not** force actor
exactification or a positive-density adjoint contradiction from covariance
and finitely many local lamp-commutant rows alone.  Any exact coefficient
model, including a selector/Reynolds payload table, can be copied through
the Heisenberg boxes with only boundary error.  The square-root of the number
of blocks never appears in the estimate; only boundary/volume does.

This does not construct canonical microstates of the full Kun--Thom wreath.
The full canonical Bernoulli mixed moments across a finite generating set of
compressors are precisely where the nonsofic coordinate action obstructs
permutation models, and whether unitary models exist is the hyperlinearity
question.  What `(AMC1)--(AMC9)` proves is narrower and load-bearing: neither
two-compressor covariance, their noncommuting Steinberg relation, nor any
fixed local lamp table can by itself yield the desired HS floor.  A successful
multi-compressor proof must use global canonical lamp correlations that do
not factor through this amenable semigroup telescope--equivalently, some
form of lamp-algebra/Cartan recovery or a genuinely nonamenable joint
cocycle obstruction.

DERIVATION
heisenberg-folner-multi-compressor-telescope-proof
