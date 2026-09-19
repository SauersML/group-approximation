---
rg: 2
id: fpbs-kesten-margin-collapses-near-lamplighter-proof
kind: route
title: Truncate the lamplighter presentation to virtually free HNN extensions, read the relative thresholds off the tree cogrowth identity, and push the spectral radius to one by lower semicontinuity
target: fpbs-kesten-margin-collapses-near-lamplighter
requires:
  - fpbs-tree-normal-relative-threshold-is-inverse-cogrowth
artifacts:
  - experiments/kesten-margin-collapse-2026-09-17/margin_collapse.py
---

Notation as in the target. `q = 3`, and `a_i = t^i a t^-i` in any quotient of `F_2`.

**Step 1 (Q_n is an HNN extension of a finite group).** Let `E_n` be the
elementary abelian group `(Z/2)^(n+1)` on `a_0, ..., a_n`. Let
`A = <a_0, ..., a_(n-1)>` and `B = <a_1, ..., a_n>`, each of index 2, and let
`theta : A -> B` be the shift `a_i -> a_(i+1)`. The HNN extension
`H_n = E_n *_theta` has generators `a_0, ..., a_n, t` and relations:

* `a_i^2 = 1`;
* `[a_i, a_j] = 1` for `0 <= i < j <= n`;
* `t a_i t^-1 = a_(i+1)` for `i < n`.

The last family eliminates `a_1, ..., a_n` as `a_i = t^i a_0 t^-i`. Then
`a_i^2 = 1` becomes a conjugate of `a^2 = 1`, and `[a_i, a_j] = 1` becomes the
conjugate by `t^i` of `[a, t^(j-i) a t^-(j-i)] = 1`, with `1 <= j - i <= n`.
So `H_n = Q_n`.

The Bass–Serre tree of `H_n` has vertex degree `[E_n:A] + [E_n:B] = 4`.
`Q_n` acts on it with finite vertex stabilisers (conjugates of `E_n`) and one
orbit of vertices. So `Q_n` is quasi-isometric to the 4-regular tree, it is
virtually free of rank at least 2, and it is nonamenable. By Kesten's
criterion, `rho_n < 1`. This is item 1.

**Step 2 (local convergence).** The relator sets increase with `n`, so
`N_n <= N_(n+1)`. Their union is the normal closure of all relators of `L`,
which is `N_L`: the displayed presentation of `L` is the standard presentation
of `Z/2 wr Z`, which is standard and not re-derived here. Since
`N_n <= N_L`, triviality in `Q_n` implies triviality in `L`.

Conversely, let `w` be a word of length at most `2m <= 2n` that is trivial
in `L`. Its `t`-exponent sum is `0`, because `L -> Z`, `t -> 1`, `a -> 0` is
well defined. Hence `w` equals, in `F_2` and so in every quotient, a product
`a_(i_1) ... a_(i_r)`, where `i_j` is the `t`-height of the `j`-th
occurrence of `a` along `w`. All heights lie in an interval `I` of integers
with at most `m + 1` points: the height path moves by at most one per
`t`-letter, returns to `0`, and uses at most `2m` letters, so its range is at
most `m`.

Conjugating by a power of `t`, which preserves triviality, we may assume
`I ⊆ [0, m] ⊆ [0, n]`. In `Q_n` the elements `a_0, ..., a_n` generate a
quotient of `E_n`, which is abelian of exponent 2. By Britton's lemma it is
`E_n` itself, though only the abelian quotient property is needed. So `w`
equals `prod_(i in I) a_i^(c_i)` in `Q_n`, where `c_i` is the number of
occurrences at height `i`.

In `L`, the elements `a_i` are the independent lamp generators of the base
group `+_Z Z/2`. So triviality of `w` in `L` forces every `c_i` to be even,
and then `w = 1` in `Q_n`. This is item 2. It follows that the return
probabilities agree, `mu_n^(*2k)(e) = mu_L^(*2k)(e)` for `k <= n`.

**Step 3 (thresholds from the tree node).** Apply
`fpbs-tree-normal-relative-threshold-is-inverse-cogrowth` with `d = 2`,
`q = 3`, so that `2 sqrt(q)/(q+1) = sqrt(3)/2`. When `rho_n > sqrt(3)/2`, its
item 2 gives `p_c(N_n;T) = s_(N_n)`. Here `s_(N_n)` is the unique
`s in (0, 1/sqrt 3)` with `4 z(s) = 1/rho_n`, where `z(s) = s/(1+3s^2)`.
Multiplying `4s/(1+3s^2) = 1/r` by `r(1+3s^2)` gives
`3 s^2 - 4 r s + 1 = 0`. For `r > sqrt(3)/2` the discriminant
`16 r^2 - 12` is positive. The roots have product `1/3`, so exactly one of
them, the smaller one `s(r) = (4r - sqrt(16 r^2 - 12))/6`, lies in
`(0, 1/sqrt 3)`. So `p_c(N_n;T) = s(rho_n)`.

Its item 4 gives `s(rho_n) > 1/3` because `rho_n < 1`. This is item 3.

**Step 4 (spectral radius tends to one).** For a symmetric probability
measure, `mu^(*(2k+2l))(e) >= mu^(*2k)(e) mu^(*2l)(e)`. By Fekete's lemma,
`rho = sup_k mu^(*2k)(e)^(1/(2k))`. By Step 2, for `k <= n`,

```text
rho_n >= mu_n^(*2k)(e)^(1/(2k)) = mu_L^(*2k)(e)^(1/(2k)).
```

`L` is amenable (metabelian), so by Kesten `rho_L = 1` for the symmetric
generating measure `mu_L`, and `sup_k mu_L^(*2k)(e)^(1/(2k)) = 1`. Given
`eps > 0`, fix `k` with `mu_L^(*2k)(e)^(1/(2k)) > 1 - eps`. Then
`rho_n > 1 - eps` for all `n >= k`. So `rho_n -> 1`, and in particular
`rho_n > sqrt(3)/2` for large `n`.

This is the lower semicontinuity of `rho` in the marked topology. The
artifact evaluates `mu_L^(*2k)(e)` exactly for `k <= 18` by dynamic
programming on (position, lit lamps), with a cross-check that
`mu_L^(*2)(e) = 3/8`. It gives `rho_n >= 0.876044` for `n >= 18`.

**Step 5 (collapse and rate).** `s` is continuous on `(sqrt(3)/2, 1]`, with
`s(1) = (4 - 2)/6 = 1/3`. So `s(rho_n) - 1/3 -> 0`. It is decreasing, because
`f(s) = 4s/(1+3s^2)` is increasing on `(0, 1/sqrt 3)` and `s(r) = f^-1(1/r)`.
So `rho_n >= 0.876044` gives `s(rho_n) - 1/3 <= s(0.876044) - 1/3 < 0.163`.

For the rate, `f(1/3) = 1` and
`f'(s) = 4(1 - 3s^2)/(1+3s^2)^2`, so `f'(1/3) = 4 (2/3)/(16/9) = 3/2`.
From `f(s(r)) = 1/r = 1 + (1-r) + O((1-r)^2)` we get
`s(r) - 1/3 = (2/3)(1-r) + O((1-r)^2)`. This is item 4. The artifact checks
it numerically: at `r = 0.999` it gives `6.6867e-4` against `6.6667e-4`.

**Step 6 (limit).** `rho_L = 1`, so item 4 of the tree node gives
`p_c(N_L;T) = p_c(T)`. It is also the case `rho_Q = 1` of item 2 there, since
the tree node's hypothesis `rho_Q > sqrt(3)/2` holds. This is item 5.

**Step 7 (the kill).** Fix `R`, and let `B` be the radius-`R` ball of
`Cay(L)`. By Step 2, every `Q_n` with `n >= R` has radius-`R` ball `B`, and by
Step 1 it has nonamenable quotient. A local margin certificate would give
`s(rho_n) - 1/3 >= delta(R,B) > 0` for all such `n`, which contradicts
Step 5.

The neighbourhood statement is the same fact read in the Chabauty topology,
since `N_n -> N_L`. The `K_r` statement holds because
`{rho_Q <= r}` is closed, `rho` being a supremum of locally constant
functions. The pairs `(T, N_n)` with `rho_n <= r` lie in `K_r`, so a uniform
margin on `K_r` is at most `s(r_*) - 1/3`, where
`r_* = sup{rho_n : rho_n <= r}`. Since `rho_n < 1` and `rho_n -> 1`, we have
`r_* -> 1` as `r -> 1`, and the bound tends to `0`. ∎
