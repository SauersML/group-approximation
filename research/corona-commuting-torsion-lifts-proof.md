---
rg: 2
id: corona-commuting-torsion-lifts-proof
kind: route
title: Finite-window averaging and spectral rounding lift countable commuting torsion families exactly
target: corona-commuting-torsion-lifts
requires: []
---

# Direct proof

Let

```text
Q = (prod_n M_(d_n)) / (direct-sum_n M_(d_n))
```

be the norm matrix corona and let `(u_j)_(j>=1)` be a countable commuting
family of unitaries in `Q` with `u_j^m=1`.  We construct representatives
`V_(j,n)` such that, at **every** coordinate `n`, all the `V_(j,n)` commute
and satisfy `V_(j,n)^m=1` exactly.

The point is that the well-known obstruction to perturbing arbitrary almost
commuting unitaries disappears here: fixed finite order gives finite spectrum,
and a finite commuting family can be repaired inductively inside successive
commutants.

## Step 1. Choose unitary lifts

Choose bounded matrix representatives `X_(j,n)` for `u_j`.  Since each `u_j`
is unitary in the quotient,

```text
||X_(j,n)^* X_(j,n)-1|| -> 0,
||X_(j,n) X_(j,n)^*-1|| -> 0.
```

Thus for all sufficiently large `n` the polar part

```text
U_(j,n) = X_(j,n) (X_(j,n)^* X_(j,n))^(-1/2)
```

is unitary and `||U_(j,n)-X_(j,n)|| -> 0`; replace the finitely many earlier
coordinates by `1`.  The `U_j=(U_(j,n))_n` represent the same classes.  The
relations in the quotient now say, for each fixed `i,j`,

```text
||[U_(i,n),U_(j,n)]|| -> 0,        ||U_(j,n)^m-1|| -> 0.        (1)
```

## Step 2. Finite exactification lemma

Fix `k`.  For every `eta>0` there is a `delta=delta(k,m,eta)>0` such that any
unitaries `U_1,...,U_k` satisfying

```text
max_i ||U_i^m-1|| < delta,
max_(i,j) ||[U_i,U_j]|| < delta
```

can be perturbed by less than `eta` to commuting unitaries
`V_1,...,V_k` with `V_i^m=1` exactly.

Proof is by induction on `r=1,...,k`.

* For `r=1`, diagonalize `U_1`.  If `lambda` is an eigenvalue then
  `|lambda^m-1|<delta`, so for small `delta` it is uniformly close to one of
  the `m`-th roots of unity.  Replace each eigenvalue by a nearest root.
  Spectral functional calculus gives an exact `m`-torsion unitary `V_1`
  arbitrarily close to `U_1`.

* Suppose commuting exact `m`-torsion `V_1,...,V_(r-1)` have already been
  built close to the corresponding `U_i`.  Their generated group

  ```text
  F = <V_1,...,V_(r-1)>
  ```

  is a finite abelian group of size at most `m^(r-1)`.  Because `U_r`
  almost commutes with the original `U_i` and `V_i` is close to `U_i`, it
  almost commutes with every generator `V_i`, hence (with a constant depending
  only on `m,r`) with every element of `F`.

  Average into the exact commutant:

  ```text
  A = |F|^-1 sum_(g in F) g U_r g^*.
  ```

  Then `A` commutes exactly with every `V_i` and `||A-U_r||` is as small as
  desired when `delta` is small.  In particular `A` is invertible.  Its polar
  part `W=A(A^*A)^(-1/2)` still lies in the common commutant, is unitary, and
  remains close to `U_r`.  Finally diagonalize `W` *inside that commutant* and
  round its spectrum to the nearest `m`-th roots of unity.  The result `V_r`
  is exact `m`-torsion, commutes with all previous `V_i`, and is as close to
  `U_r` as prescribed.

Only finitely many constants occur for fixed `k`, so choosing `delta`
successively smaller proves the lemma.  Notice that no dimension-dependent
constant appears.

## Step 3. Diagonalize the finite windows

For each `k>=1`, apply the finite lemma with target perturbation `eta_k=1/k`
and choose a corresponding tolerance `delta_k>0`.  By (1), choose a strictly
increasing integer sequence `N_k` (also with `N_k>=k`) such that for every
`n>=N_k`, the first `k` lifts have all their commutator and `m`-torsion
defects below `delta_k`.

For a coordinate in the shell

```text
N_k <= n < N_(k+1),
```

apply the finite exactification lemma to
`U_(1,n),...,U_(k,n)`, obtaining a commuting exact `m`-torsion `k`-tuple
within `1/k`; set every `V_(j,n)=1` for `j>k`.  On the finitely many
coordinates before `N_1`, set every `V_(j,n)=1`.

At each coordinate the entire countable family now commutes exactly: only the
first `k` entries can be nontrivial on the `k`-th shell, and those came from
one commuting exact tuple.  Every entry has exact `m`-th power one.

For a fixed `j`, once the shell index `k` is at least `j`,

```text
||V_(j,n)-U_(j,n)|| <= 1/k -> 0.
```

Hence `(V_(j,n))_n` and `(U_(j,n))_n` determine the same corona class `u_j`.
This simultaneously proves exact commutation, exact `m`-torsion and class
preservation for every member of the countable family.

Therefore [[corona-commuting-torsion-lifts]] is established.  In particular
the route `compression-torsion-collapse-assembly`, although no longer the
cheapest proof of its target, becomes independently complete and supplies a
second proof of the compression-torsion collapse through a finite-spectrum
lifting mechanism rather than Fourier projections.
