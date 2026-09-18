---
rg: 2
id: higman-power-pair-collapse-is-base-uniform-up-to-torsion-proof
kind: route
title: Audit of the descent chain in base n, torsion propagation around the four-cycle, and the involution model D_oo x D_oo for odd n
target: higman-power-pair-collapse-is-base-uniform-up-to-torsion
requires:
  - higman-elementary-amenable-edge-images-collapse
  - nontrivial-higman-quotients-keep-all-four-bs-subgroups
artifacts:
  - experiments/higman-base-n-calibration-2026-09-18/base_n_quotients.py
  - experiments/higman-base-n-calibration-2026-09-18/base_n_quotients-output.txt
---

Conventions: `x^y = y^-1 x y`. `H4(n)` as in the target. Cite
`higman-elementary-amenable-edge-images-collapse-proof` as **[EA]**, the tower route
`higman-bounded-derived-length-tower-chain-proof` as **[T]**, the derived-length-three route
`higman-derived-length-three-edge-collapse-proof` as **[3]**, and
`higman-virtually-solvable-edge-images-collapse-proof` as **[VS]**.

## Step 1 (the substitution lemma in base n)

Fix `m >= 1`, `alpha = a^m`, `gamma = c^m`. From `a^-1 b a = b^n` we get `a^-j b a^j = b^(n^j)` for
`j >= 0`, and from `b^-1 c b = c^n` we get `b^-k c b^k = c^(n^k)` for `k >= 0`. Hence for `j >= 0`

```text
b^-1 (alpha^j gamma alpha^-j) b = alpha^j b^-(n^(mj)) gamma b^(n^(mj)) alpha^-j = alpha^j gamma^(N_j) alpha^-j,
N_j = n^(P^j),  P = n^m.
```

This is Lemma 1 of [3] with `2` replaced by `n`: for `w` in `P_(>=0)` (gamma-letters at nonnegative
alpha-height, alpha-exponent sum 0), `ev(iota_b(w)) = b^-1 ev(w) b`, where `iota_b` raises the
gamma-letter at height `j` to the power `N_j`. The mirror for `d` is the same with `a <-> c`, `b <-> d`.
No other relation of `H4(n)` is used anywhere in [3], [T], [VS] Steps 1–5 or [EA] Steps 1–5; everything
else is a statement about the free group `Phi = <alpha, gamma>` and the integers `N_j`.

## Step 2 (the audit: where the numbers N_j enter)

The integers `N_j` enter in exactly three places. Each needs only `n >= 2`.

1. **Lemma 3 of [3] (separation).** If `delta != 0` is supported on `[h_1, oo)` with
   `||delta||_1 < N_(h_1)`, then `sum_h delta_h N_h != 0`. *Proof in base n.* Let `h_1' >= h_1` be the
   least `h` with `delta_h != 0`. Every `N_h` with `h > h_1'` is divisible by `N_(h_1') N_(h_1')`, since
   `P^h >= 2 P^(h_1')` when `P >= 2`. So `sum delta_h N_h = N_(h_1') (delta_(h_1') + N_(h_1') t)` for an
   integer `t`, and `0 < |delta_(h_1')| < N_(h_1')`, so the bracket is nonzero.
2. **Lemmas A, B of [T] (injectivity of sigma_*).** These use `N_(h+1) >= N_h^2` and the separation of
   distinct finite multisets of heights by `h -> N_h`. In base `n`, `N_(h+1) = N_h^P >= N_h^2`, since
   `P = n^m >= 2`. The proofs go through word for word.
3. **Lemma 2.2 of [EA] (choice of shift).** It needs `N_(h_*) > 2|v|` for a shift `n'` with heights
   `>= n' - c`, while `|v|` grows linearly in `n'`. `N_(n'-c) = n^(P^(n'-c))` grows doubly exponentially
   for every `n >= 2`.

Steps 1 and 3 of [EA] (the free state action, Proposition 1.4, and the parity flip via [VS] Steps 3–5
and the field Lemma 2) contain no `N_j` at all.

**Conclusion (item 1).** Theorem 4.1 of [EA] holds in every base: for each quotient `Q` of `H4(n)` and
each `M`, either `A_M` is free on `a^M, c^M`, or `alpha^Y, gamma^(Y') in A_M'` for some `Y, Y' != 0`, so
`A_M / A_M'` is finite. The same proof applies to `<b^M, d^M>` via the cyclic automorphism
`a -> b -> c -> d -> a` of the presentation, which exists for every `n`.

## Step 3 (the closure and torsion, items 2 and 3)

Lemmas 5.1 and 5.2 of [EA] are pure group theory. Theorem 6.1 of [EA], read in base `n`, gives: if
`A in X`, then `(A; a, c)` is power-perfect (by Step 2), so some `A_M` is finite, of order `e`, and
`a^(Me) = 1`.

**Lemma 3.1 (torsion goes around the cycle).** Let `x_1, x_2, x_3, x_4 = a, b, c, d` (indices mod 4)
satisfy `x_i^-1 x_(i+1) x_i = x_(i+1)^n`. If `x_i^E = 1` with `E >= 1`, then `x_(i+1)^(n^E - 1) = 1`.

*Proof.* `x_i^-E x_(i+1) x_i^E = x_(i+1)^(n^E)`, and the left side is `x_(i+1)`. ∎

Starting from `a^(Me) = 1` and going around the cycle, all four generators have finite order. This is
item 2.

For `n = 2`, a nontrivial quotient has all generators of infinite order
(`nontrivial-higman-quotients-keep-all-four-bs-subgroups`, the smallest-prime argument: if `p` is the
least prime dividing some `ord(x_i)`, then `p | 2^(ord(x_(i-1))) - 1`, which forces a smaller prime
dividing `ord(x_(i-1))`). So `Q = 1`. That lemma is the only statement in the chain
[3] → [T] → [VS] → [EA] whose proof uses `n = 2`; everything upstream was audited in Step 2. This is
item 3. For `n >= 3` the smallest-prime argument fails, because `n^E - 1` has the prime factors of `n - 1`.

## Step 4 (odd bases: the involution model, item 4)

Let `n` be odd. On `Z^2` put

```text
a(x,y) = (-x, y),   c(x,y) = (1-x, y),   b(x,y) = (x, -y),   d(x,y) = (x, 1-y).
```

- **Relations.** `a, c` commute with `b, d` (they act on different coordinates), and all four are
  involutions. So `b^a = b = b^n`, because `n` is odd, and likewise for the other three relations.
  Hence `x -> x` defines a homomorphism `H4(n) -> Q := <a,c> x <b,d>`.
- **The edge image.** `ac(x,y) = (x - 1, y)` up to orientation, a translation of infinite order. So
  `A = <a,c> = D_oo`: it is infinite, virtually `Z`, amenable, and `A/A' = (Z/2)^2` is finite. Also
  `A_2 = <a^2, c^2> = 1`.
- **Consistency with Steps 2–3.** `A` is not free and `A_M / A_M'` is finite for every `M` (it is
  `A/A'` for odd `M` and trivial for even `M`), as Step 2 says. The generators are torsion, as Step 3
  says. `Q` is nontrivial.

For every `n >= 3`, `a, b, c, d -> e_1, ..., e_4` in `(Z/(n-1))^4` satisfies the relations, because in
an abelian group `b^a = b^n` reads `(n - 1) e_2 = 0`. The edge image `(Z/(n-1))^2` is finite and nontrivial.

`base_n_quotients.py` checks the relations of the involution model exactly, as integer affine maps, for
all odd `n <= 39`, and checks that they fail for `n = 2, 4, 6`. It also checks the abelian model for
`2 <= n <= 19`. Output: `base_n_quotients-output.txt`.

## Step 5 (structure of the base-two residue, item 5)

Let `Q != 1` be a quotient of `H4` and let `A` be not free on `a^M, c^M` for any `M` (for instance
amenable, since `F_2` is not). By Step 2, each `A_M / A_M'` is a finite abelian group. So:
- `A_M'` has finite index in the finitely generated group `A_M`, hence is finitely generated;
- `A_M' / A_M''` is a finitely generated abelian group, and `A_M / A_M''` is an extension of it by the
  finite group `A_M/A_M'`, hence virtually free abelian of rank `b_1(A_M')`;
- `a, c` have infinite order (Step 3), so no `A_M` is finite.

## Step 6 (what this rules out)

**Theorem 6.1 (class-killing).** Let `S` be any proof scheme that uses the relations of `H4` only through
the substitution lemma of Step 1 and uses the integers `N_j` only through the three properties of Step 2
(separation, `N_(h+1) >= N_h^2`, doubly exponential growth). Then `S` proves, for base 2, nothing about an
edge image `A` that it does not also prove in every odd base. In particular `S` cannot prove "an
infinite virtually cyclic (or amenable) power-perfect `A` has a finite power subgroup". Such a proof
would apply to `D_oo` in `H4(3)`, but `A_1 = D_oo` is infinite, although `A_2 = 1` is finite. A scheme
concluding `Q = 1` from `A in C` for a class `C` containing `D_oo` is refuted by Step 4 unless it uses
`n = 2` outside Step 2.

*Proof.* Every statement `S` derives holds verbatim in `H4(n)` for every odd `n`, by Steps 1–2. Step 4
gives a nontrivial quotient of `H4(n)` with `A = D_oo`. ∎

**Consequence for amenable edge images.** For the target case (amenable, power-perfect, generators of
infinite order), the torsion lemma is not yet available: it applies only after some `A_M` is finite. So an
extension to all amenable `A` needs one of the following:
- **(a) a base-uniform theorem.** Every amenable power-perfect pair realized in a quotient of some `H4(n)`,
  with generators of infinite order, has a finite power subgroup. The involution model does not refute
  this, since its generators are torsion. A counterexample would need infinite-order generators in an odd
  base.
- **(b) a second use of `n = 2`.** For example, a mod-2 or 2-adic invariant of the chain word. Note that
  every `N_j` is a power of 2 when `n = 2`, so the exponents `Y = sum c_h N_h` of Step 2 are even.

## Calibration

- **Base 2.** Every statement reduces to [EA] and adds nothing new there.
- **Odd base.** The involution model is a nontrivial quotient whose infinite amenable edge image is not
  collapsed. The theorem correctly stops at "torsion generators".
- **Base `n >= 3` abelian.** The abelian model has a finite, nontrivial `A`. This is consistent with item 2.
