# Full finite involution corners have only power-of-two matrix widths

2026-09-08. This is a restriction on unital matrix algebras inside the
entire negative corner of one involution in a finite group. Centrality
of the involution is not assumed. The proof uses finite permutation
representations and Sylow subgroups; no rigidity estimate or computation
is involved.

## 1. The negative-rank gcd

Let `F` be a finite group and let `J` have order exactly two. For
each complex irreducible representation `rho` put

```text
m_rho=rank((I-rho(J))/2)
     =(dim(rho)-chi_rho(J))/2,
g_J=gcd{m_rho : m_rho>0}.
```

The set is nonempty, since `J` is nonidentity in the regular
representation. Write `|F|=2^a b`, where `b` is odd and `a>=1`.
Then

```text
g_J=2^s for some 0<=s<=a-1.                         (1)
```

First, `g_J` divides the negative rank of every representation of
`F`, by decomposition into irreducibles. On the regular representation,
`J` acts by fixed-point-free pairs, so that rank is `|F|/2`.

Now fix any odd prime `p` dividing `|F|`, and let `P` be a Sylow
`p`-subgroup. Consider the permutation representation on left cosets
`F/P`. The involution `J` fixes no coset: a fixed coset `xP`
would imply `x^-1 J x in P`, impossible in an odd-order group.
Thus this representation has negative rank

```text
[F:P]/2.                                           (2)
```

The index `[F:P]` is prime to `p`, so the integer in (2) is also
prime to `p`. Since `g_J` divides (2), the prime `p` cannot divide
`g_J`. Every odd prime that could divide `g_J` divides `|F|/2`,
and hence has just been excluded. Its remaining power of two is
bounded by the two-part of `|F|/2`. This proves (1).

## 2. The exact unital matrix-embedding criterion

Set `q=(1-J)/2`. Complex finite-group algebra decomposition gives

```text
q C[F] q ~= directSum_(rho:m_rho>0) M_(m_rho)(C).     (3)
```

Indeed, under each irreducible block, `q` is the orthogonal
projection onto the negative eigenspace of `rho(J)`, and compressing
a full matrix algebra by a rank-`m_rho` projection gives the indicated
matrix algebra. The identity of (3) is the entire projection `q`.

Consequently there is a unital star homomorphism

```text
M_D(C) -> q C[F] q
```

if and only if

```text
D divides every positive m_rho,
equivalently D divides g_J.                          (4)
```

Necessity follows by projecting the homomorphism to each summand:
every unital representation of `M_D(C)` has dimension a multiple of
`D`. For sufficiency, on a summand of size `m_rho`, use
`x -> x tensor I_(m_rho/D)`, and take the direct sum of these maps.
Since `M_D(C)` is simple and the target is nonzero, such a unital
homomorphism is automatically injective.

Equations (1) and (4) show that every permitted width `D` is a
power of two. Passing from a central involution to a noncentral one
does not permit an odd factor in a matrix algebra that uses the
whole authenticated negative corner as its unit.

## 3. The upper bound is attained by noncentral involutions

The explicit Fourier construction in
[the affine negative-corner artifact](noncentral-frobenius-negative-rational-matrix-corner-2026-09-08.md)
uses

```text
F=(F_(2^n))_add semidirect (F_(2^n))^times,
J=translation by 1,
q C[F] q ~= M_(2^(n-1))(C).
```

For `n>=2`, this involution is noncentral. Its group has order
`2^n(2^n-1)`, and (3) shows directly that
`g_J=2^(n-1)`. Thus the upper bound in (1) is sharp even for
noncentral involutions. The affine construction also gives the
displayed matrix algebra over the rationals; it establishes that
stronger conclusion explicitly rather than deducing it from (4).

## 4. Scope

The theorem concerns the full corner with unit `q`. A smaller selected
projection can have different matrix sizes, but its nonvanishing is
not authenticated merely by survival of `J`. The result does not
bound the number of summands or the sizes of arbitrary projection
partitions inside the corner. Nor does it impose the same restriction
on a corner of an infinite group algebra.

Over the rational group algebra, complexification makes the
power-of-two condition necessary as well. Sufficiency over the
rationals is not asserted by (4), because the rational simple factors
can have additional field or division-algebra obstructions.
