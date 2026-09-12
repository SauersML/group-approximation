---
rg: 2
id: smooth-pairing-design-composition-proof
kind: route
title: Compose a Caratheodory permutation design with a random smooth pairing family
target: smooth-pairing-designs-of-size-m-to-the-n-exist
requires: []
---

Put `N = 2n`.

1. **Permutation design.** The `w in R^(S_N)` with `w >= 0` and
   `sum_sigma w_sigma 1[sigma(a) = b] = 1/(N)_(2t)` for all distinct `2t`-tuples
   `a`, `b` form a nonempty (the uniform distribution) bounded rational polytope.
   A vertex has rational coordinates and support at most `(N)_(2t)^2 + 1`. It is
   `2t`-wise uniform, and so are its inverse and its `2k`-point marginals for
   `k <= t`: `sigma(a) = b` iff `sigma^(-1)(b) = a`.
2. **Random smooth family.** Take `M = ceil(3 m^n (2n ln m + 1)/C)` independent
   uniform pairings `pi_1..pi_M`. For a `K`-roughly balanced `z`, `z` is
   `pi`-pair-constant with probability `p_z = m^n nu_(2n,m)(z) <= C m^(-n)`
   (BKM Lemma 4.2). The count `X_z` is dominated by `Bin(M, C m^(-n))`, so
   `Pr[X_z >= 2 C M m^(-n)] <= exp(-C M m^(-n)/3) <= e^(-1) m^(-2n)`. A union
   bound over at most `m^(2n)` points shows that some choice has
   `nu_Q(z) <= 2C m^(-2n)` at every balanced `z`.
3. **Compose.** Sample `sigma ~ w` and `pi` uniform in `Q`, independently, and
   output `sigma(pi)`.
   - *t-wise uniform.* For a partial matching with `k <= t` pairs, listed as
     an ordered tuple `b`, `Pr[its pairs lie in sigma(pi)] = Pr[the consecutive
     pairs of sigma^(-1)(b) lie in pi]`. `sigma^(-1)(b)` is uniform over distinct
     `2k`-tuples, independent of `pi`, and for any fixed perfect matching that
     probability is `prod_(l<k) 1/(N-2l-1)`.
   - *Smooth.* `z` is `sigma(pi)`-pair-constant iff `z o sigma` is
     `pi`-pair-constant, and `z o sigma` has the same symbol counts as `z`. So
     `nu(z) = sum_sigma w_sigma nu_Q(z o sigma) <= 2C m^(-2n)`.
   - *Support.* At most `|supp w| * M`.

Finally, `(2n-1)!! >= n! >= (n/e)^n` exceeds `m^n n^(O(t))` once `n` is large.
