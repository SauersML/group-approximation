---
rg: 2
id: amenable-core-embedding-uniqueness-proof
kind: route
title: Compare the regular BS core with slowly growing regular congruence models
target: regular-bs14-cores-align-with-congruence-endpoint-restrictions
requires:
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
  - bs14-character-split-leaves-only-the-regular-microstate-face
---

Choose a nested sequence of finite odd congruence quotients

```text
q_j:A -> Q_j                                           (ACE1)
```

which separates the points of `A`.  Replace the sequence by its successive
product if necessary so that `|Q_j|` is nondecreasing.  Condition `(RCA3)`
forces `d_n->infinity`: otherwise a bounded-dimensional subsequence would
converge to a finite-dimensional representation with the regular character
of the infinite group `B`.

Choose `j(n)->infinity` slowly enough that

```text
|Q_(j(n))| <= sqrt(d_n).                               (ACE2)
```

Write

```text
d_n=m_n |Q_(j(n))|+ell_n,       0<=ell_n<|Q_(j(n))|,
```

and define the exact representation

```text
pi_n
 = (lambda_(Q_(j(n))) o q_(j(n)))^(direct sum m_n)
   direct sum 1^(direct sum ell_n).                   (ACE3)
```

It has dimension exactly `d_n` and factors through `Q_(j(n))`.  For every
fixed `a!=e`, separation makes `q_(j(n))(a)!=e` eventually, so the regular
summands have trace zero at `a`, while

```text
ell_n/d_n < |Q_(j(n))|/d_n <= d_n^(-1/2).             (ACE4)
```

Hence the normalized characters of `pi_n` converge to `delta_e` on `A`.
In particular, both `beta_n` and `pi_n|B` have the regular limiting
character of `B`.

Fix a free ultrafilter and put

```text
M=prod_omega (M_(d_n),tr_(d_n)).                       (ACE5)
```

The two sequences define trace-preserving embeddings

```text
iota_beta,iota_pi:L(B) -> M.                          (ACE6)
```

The group `B=BS(1,4)` is amenable, so `L(B)` is a separable hyperfinite
finite von Neumann algebra.  Two trace-preserving embeddings of such an
algebra into the matrix-ultraproduct factor are approximately unitarily
conjugate.  For completeness, approximate a prescribed finite set in
`L(B)` by one finite-dimensional subalgebra `D`.  The two copies of `D` have
the same trace on every minimal central projection.  Matrix units with the
same trace vector are unitarily conjugate in a finite factor, so one unitary
conjugates the two embeddings exactly on `D` and approximately on the
prescribed finite set.  Increasing the finite set and the accuracy proves
approximate unitary conjugacy.

Apply this to the two group generators.  If `(RCA5)` failed along a
subsequence by some fixed `epsilon>0`, take an ultrafilter on that
subsequence.  Approximate unitary conjugacy in `(ACE5)` would give a unitary
whose representing sequence contradicts the uniform lower bound
`epsilon`.  Therefore

```text
inf_(W in U(d_n)) max_(s in {r,t})
 ||beta_n(s)-W pi_n(s)W^*||_2 -> 0.                   (ACE7)
```

Choosing near-minimizing `W_n` proves `(RCA5)`.

The argument is qualitative but contains no moving stability radius and no
comparison with a defect schedule.  Its limitation is structural rather
than quantitative: amenability identifies only the represented BS core.
It does not turn an arbitrary almost-extending involution into the Weyl
operator of `pi_n` or any member of its core-commutant endpoint orbit.
