---
rg: 2
id: unitary-block-energy-transport-proof
kind: route
title: Orthogonal Pythagoras gives the marginals and weak LP duality gives the cost floor
requires: []
target: unitary-block-energy-transport
---

Fix `i`.  Because the `Q_j` are pairwise orthogonal and sum to one, the
operators `Q_j U P_i` are orthogonal in Hilbert--Schmidt inner product.  Hence

```text
sum_j ||Q_j U P_i||_2^2
 = ||U P_i||_2^2
 = tr_D(P_i)
 = alpha_i.                                            (T1)
```

Similarly, for fixed `j`, the operators `Q_j U P_i` are Hilbert--Schmidt
orthogonal as `i` varies, so

```text
sum_i ||Q_j U P_i||_2^2
 = ||Q_j U||_2^2
 = tr_D(U^* Q_j U)
 = tr_D(Q_j)
 = beta_j.                                             (T2)
```

This proves `(UBE2)`.

Now multiply `(UBE3)` by the nonnegative number `m_(j,i)` and sum over all
pairs.  Using `(T1)` and `(T2)`,

```text
sum_(i,j) c_(j,i) m_(j,i)
 >= sum_(i,j) (x_i+y_j) m_(j,i)
  = sum_i x_i alpha_i + sum_j y_j beta_j,
```

which is `(UBE4)`.

For a support graph `E`, take `c_(j,i)=0` on `E` and `1` off `E`.  If `S` has
Hall deficit `gamma=alpha(S)-beta(N(S))>0`, choose

```text
x_i = 1  for i in S,   x_i=0 otherwise,
y_j = -1 for j in N(S), y_j=0 otherwise.
```

Then `x_i+y_j<=c_(j,i)` for every pair and the dual value is exactly `gamma`.
Thus the earlier weighted Hall leakage theorem is contained in this transport
statement.
