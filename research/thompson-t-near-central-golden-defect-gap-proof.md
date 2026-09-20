---
rg: 2
id: thompson-t-near-central-golden-defect-gap-proof
kind: route
title: Kill [a^2, b] to reach 2I = SL(2,5), read the Lochak--Schneps defect off its 9 irreps, and lift near-central sequences to 2I through the corona
target: thompson-t-near-central-pairs-have-golden-defect-gap
requires:
  - finite-group-corona-tail-exactification
  - thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes
artifacts:
  - experiments/thompson-t-triangle-rep-census-2026-09-17/two_i_table.py
  - experiments/thompson-t-triangle-rep-census-2026-09-17/two_i_table.out
---

Notation is that of the claim. `||.||` is the operator norm. For unitaries and a word `w` of length
`l`, `||w(U) - w(V)|| <= l max_i ||U_i - V_i||`, because `||U^(-1) - V^(-1)|| = ||U - V||`. The word
`r_1` has length 20 and `r_2` has length 34.

## Step 1: G = 2I (item 3, first part)

In `G = < a, b | a^4, b^3, (ba)^5, [a^2, b] >`, the element `a^2` commutes with `a` and with `b`, so it
is central, and `(a^2)^2 = 1`. Therefore `G / <a^2> = < a, b | a^2, b^3, (ba)^5 >`, the (2,3,5) von Dyck
group, which is `A_5` of order 60. Hence `|G| <= 120`.

The script `two_i_table.py` takes unit quaternions from the 120 icosians and sets
`rho_2(a) = -q_4` and `rho_2(b) = q_3`, where `q_4` has trace 0 (order 4), `q_3` has trace -1
(order 3), and `q_3 q_4` has trace `phi`. Then `rho_2(b) rho_2(a)` has trace `-phi`, which makes it of
order 5. So `(ba)^5`, `a^4` and `b^3` map to 1 exactly. Also `rho_2(a)^2 = -1` is central. So `rho_2` is
a homomorphism `G -> SU(2)`.

The script closes `{rho_2(a), rho_2(b)}` under multiplication by breadth-first search and finds exactly
120 elements. Hence `rho_2` is onto a group of order 120 and is injective, so `G = 2I` and `|G| = 120`.

The breadth-first search is exact up to the test `np.allclose`. The icosian entries lie in
`Q(sqrt 5, i)/2`, and distinct icosians differ by at least `1/(2 phi^2) = 0.19` in some matrix entry.
So equality testing at the default `np.allclose` tolerance (about `1e-8`) is exact.

## Step 2: the images of r_1 and r_2

Since `J = a^2` is central with `J^2 = 1`, `JXJ = X`, so `r_1 = [X, X] = 1` in `G`. Also
`J b^2 J X J b J = b^2 X b = b^2 (bab) b = a b^2`, so `r_2 = [bab, ab^2]`.

## Step 3: the defect table (item 3, second part)

The script builds nine representations of `G`, each written as a pair `(A, B)` of unitary matrices:

- `Sym^k rho_2` for `k = 0, ..., 5`, the restriction of the `k`-th tensor power to the symmetric subspace
  in an orthonormal basis;
- `rho_2'`, from a second generating pair `(-q_4', q_3')` with trace of `q_3' q_4'` equal to `-1/phi`;
- `Sym^2 rho_2'`;
- `rho_2 (x) rho_2'`.

The script checks the following for each of them.

- `A^4 = B^3 = (BA)^5 = 1` and `[A^2, B] = 1`, so each is a representation of `G`.
- `a -> a', b -> b'` respects the Cayley graph of `G`, which is how `rho_2'` is defined on `G`.

It then computes all characters on the 120 elements, each written as a word from the breadth-first
search. The 9 characters are orthonormal, so the representations are irreducible and pairwise
inequivalent. Their dimensions satisfy `1 + 4 + 9 + 16 + 25 + 36 + 4 + 9 + 16 = 120 = |G|`, so they are
all the irreducible representations of `G`.

`rho(r_1) = 1` in every representation, by Step 2. The element `q(r_2) = [bab, ab^2]` has order dividing
10 in `2I`: its image under the faithful `rho_2` has eigenvalues `exp(+-i pi/5)`. So the eigenvalues of
`pi(q(r_2))` are 10th roots of unity. Hence `D_12(pi) = 2 sin(j pi / 10)` for an integer `0 <= j <= 5`.

These six values are separated by at least `0.09` (the closest are `1.902` and `2`). The
floating-point values in `two_i_table.out` agree with them to `1e-12`, so the numerics determine the table exactly. The minimum over nontrivial
irreducibles is `2 sin(pi/10) = m`, attained only at `rho_2`.

`D_12(sigma (+) tau) = max(D_12(sigma), D_12(tau))`, and `D_12` is invariant under unitary equivalence.
So **every nontrivial representation `sigma` of `G`, in any dimension, has `D_12(sigma) >= m`**. The
reason is that `sigma` has a nontrivial irreducible summand.

## Step 4: sharpness (item 2)

`rho_2`, viewed as a representation of `Delta(4,3,5)`, has `[A^2, B] = 1` and `(BA)^5 = 1` exactly, so
`c = 0`, and `D_12 = m`.

## Step 5: the near-central gap (item 1)

Suppose item 1 fails for some `delta > 0`. Then there are nontrivial exact pairs
`(A_k, B_k)` in `U(n_k)` with `c(A_k, B_k) -> 0` and `D_12(A_k, B_k) <= m - delta`.

**Nontriviality survives.** For large `k`, `A_k != 1`. If `A_k = 1`, then
`B_k != 1` because the pair is nontrivial, and `||r_P - 1|| = ||B_k^5 - 1|| = ||B_k^2 - 1|| >= |omega^2 - 1| = sqrt 3`.
This is impossible once `c < sqrt 3`. So `A_k` has an eigenvalue in
`{i, -1, -i}`, and `||A_k - 1|| >= sqrt 2`.

**Corona.** Let `Q = prod_k M_(n_k) / (+)_k M_(n_k)`, with the `c_0`-sum. The classes `a = [A_k]` and
`b = [B_k]` are unitaries in `Q` with `a^4 = b^3 = 1`, and, since `c -> 0`, `(ba)^5 = 1` and
`[a^2, b] = 1`. So `a, b` define a homomorphism `pi : G -> U(Q)`, and `G` is finite by Step 1.

By `finite-group-corona-tail-exactification`, after deleting finitely many `k` there are honest
representations `sigma_k : G -> U(n_k)` with `[sigma_k] = pi`. That is,

```text
e_k = max( ||sigma_k(a) - A_k||, ||sigma_k(b) - B_k|| ) -> 0.
```

For large `k`, `||sigma_k(a) - 1|| >= sqrt 2 - e_k > 0`, so `sigma_k` is nontrivial. By Step 3,
`D_12(sigma_k) >= m`. By the word-length bound,

```text
m <= D_12(sigma_k) <= D_12(A_k, B_k) + 34 e_k <= m - delta + 34 e_k,
```

which fails for large `k`. This contradiction proves item 1.

## Step 6: the equivalence with FC (item 4)

**Target implies FC.** By item 3 of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`, the target
gives `epsilon_0 > 0` such that every `epsilon_0`-pair is `(1, 1)`. Then `[A^2, B] = 1` on all such pairs.

**FC implies the target.** Let `eta = eta(m/2)` from item 1, let `epsilon` come from FC for this `eta`,
and put `epsilon' = min(epsilon, eta, m/2)`. Take a pair with `D(A,B) < epsilon'`.

- `||r_P - 1|| < eta`, directly.
- `||[A^2, B] - 1|| < eta`, by FC.

So `c < eta`. If the pair were nontrivial, item 1 would give `D_12 > m/2 >= epsilon'`, contradicting
`D < epsilon'`. So every `epsilon'`-pair is trivial, and the criterion gives the target.

**Refuting sequences.** Let `(A_k, B_k)` be nontrivial with `D -> 0`. Once
`D < min(eta(m/2), m/2)`, item 1 forces `c >= eta(m/2)`. Since `||r_P - 1|| <= D < eta(m/2)`, this
means `||[A_k^2, B_k] - 1|| >= eta(m/2)`.
