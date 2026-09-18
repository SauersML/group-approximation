---
rg: 2
id: sl-r-polynomial-no-root-free-laurent-overgroup-proof
kind: route
title: Transvection, Koszul-syzygy double commutator and prime-by-prime valuation extraction
target: sl-r-polynomial-has-no-root-free-laurent-overgroup
requires: []
---

Notation is as in the target: `A` is a UFD, `0 != f in A`, `R = A[1/f]`, `r >= 3`, and
`E_r(A) <= H <= GL_r(R)` with `H ∩ U_12(R) = U_12(A)`. Write `e_1,…,e_r` for the standard
columns and `e_k^T` for the rows. `E_ab = e_a e_b^T`, `e_ab(c) = 1 + c E_ab`, and
`[x,y] = x y x^(-1) y^(-1)`. For a prime `π | f` let `v_π` be the `π`-adic valuation on
`Frac(A)`, with `v_π(0) = +∞`.

**(UFD fact.)** If `g in R` and `v_π(g) >= 0` for every prime `π | f`, then `g in A`.
Proof: write `g = a/f^n`. For each prime `π | f` we have `v_π(a) >= n·v_π(f)`, so
`f^n | a` in the UFD `A`.

The external input is only this UFD fact. For the Laurent corollary, Suslin's theorem
`SL_r(k[x_1..x_d]) = E_r(k[x_1..x_d])` for `r >= 3` is also used. The core statement
`H <= R^×·GL_r(A)` needs no Suslin.

## Step 0. All root modules are polynomial

The Weyl elements `w_ab = e_ab(1) e_ba(-1) e_ab(1)` lie in `E_r(A) <= H`. They permute the
root groups up to sign: `w U_ab(R) w^(-1) = U_(σa,σb)(R)`, and the same holds with `A`
in place of `R`. The permutations `σ` realised this way act transitively on ordered
pairs of distinct indices. Hence

```text
H ∩ U_ab(R) = U_ab(A)    for all a != b.                                   (0)
```

## Step 1. Column lemma

Let `y in R^r` with `y_k = 0` and `X = 1 + y e_k^T in H`. Then `y in A^r`.

*Proof.* Take `b != k` and `a ∉ {b,k}`, which exists because `r >= 3`. Since
`e_k^T E_ab = 0` (because `a != k`),

```text
e_ab(1) X e_ab(-1) = 1 + (y + y_b e_a) e_k^T,
[e_ab(1), X] = (1 + (y + y_b e_a) e_k^T)(1 - y e_k^T) = 1 + y_b E_ak = e_ak(y_b),
```

using `e_k^T y = y_k = 0`. This lies in `H`, so `y_b in A` by (0). ∎

## Step 2. Transvections of H

Fix `h in H` and `i != j`. Put `u = h e_i in R^r` (a column) and `w = e_j^T h^(-1)` (a row).
Then `w u = (h^(-1)h)_(ji) = 0` and

```text
τ := h e_ij(1) h^(-1) = 1 + u w in H,      N := u w = h E_ij h^(-1).
```

For `γ in E_r(A)` the element `γτγ^(-1) = 1 + (γu)(wγ^(-1))` again lies in `H` and has the
same shape. Steps 3 and 4 use only these facts: `τ = 1 + uw in H`, `wu = 0`, and
`u, w != 0`. The row `w` is nonzero because `h^(-1)` is invertible, and `u` is nonzero
because `h` is.

## Step 3. The Koszul double commutator

Let `τ = 1 + uw in H` with `wu = 0` and `w != 0`. Choose `μ in R^×` to be a product of
powers of the primes dividing `f`, such that `q := μ w in A^r`. For example take
`μ = ∏_(π|f) π^(-min_a v_π(w_a))`. By the UFD fact this `q` lies in `A^r`.

**Claim.** For all `k != n` and all `a != k`, we have `u_k w_n q_a in A`.

*Proof.* Pick `b ∉ {a,k}`, which is possible since `r >= 3`. Put

```text
v = q_b e_a - q_a e_b in A^r,      T = 1 + v e_k^T = e_ak(q_b) e_bk(-q_a) in E_r(A) <= H.
```

Then `v_k = 0`, and `w v = μ^(-1)(q_a q_b - q_b q_a) = 0`.

*(1) First commutator.* Using `wv = 0` and `e_k^T v = 0`,

```text
τ T τ^(-1) = 1 + v e_k^T (1 - uw) = 1 + v e_k^T - u_k v w,
X_1 := [τ, T] = (1 + v e_k^T - u_k v w)(1 - v e_k^T) = 1 - u_k v w.
```

The cross terms `v e_k^T v e_k^T` and `v w v e_k^T` vanish because `e_k^T v = 0` and
`wv = 0`.

*(2) Second commutator.* Put `c = -u_k`, so `X_1 = 1 + c v w`, and
`X_1^(-1) = 1 - c v w` since `(vw)^2 = v(wv)w = 0`. Since `n != k`, `e_nk(1)` is
elementary, and `e_nk(1) v = v` because `v_k = 0`. Hence

```text
e_nk(1) X_1 e_nk(-1) = 1 + c v w (1 - E_nk) = 1 + c v w - c w_n v e_k^T,
Y := [e_nk(1), X_1] = (1 + c v w - c w_n v e_k^T)(1 - c v w) = 1 + u_k w_n v e_k^T.
```

The cross terms vanish because `e_k^T v = 0` and `wv = 0`.

*(3) Extraction.* `Y in H` has the form `1 + y e_k^T` with `y = u_k w_n v` and `y_k = 0`.
By Step 1, `y in A^r`, so `u_k w_n q_b in A` and `u_k w_n q_a in A`. ∎

The last application of Step 1 is itself one commutator
`[e_cb(1), Y] = e_ck(u_k w_n q_b)` or `[e_cb'(1), Y] = e_ck(-u_k w_n q_a)`. So when the
conclusion fails, an explicit word of bounded length in `h^(±1)` and `E_r(A)` is a
non-polynomial root element.

## Step 4. Prime-by-prime normalisation

Fix `h in H`, `i != j`, and a prime `π | f`. Let `u = h e_i`, `w = e_j^T h^(-1)` and
`N = uw`.

*Normalise the row.* Let `m = min_a v_π(w_a)`, which is finite because `w != 0`, and pick
`a_0` with `v_π(w_(a_0)) = m`. For each `a != a_0` with `v_π(w_a) > m`, right
multiplication by `e_(a_0 a)(1)` replaces `w_a` by `w_a + w_(a_0)`, which has valuation
exactly `m`. It leaves every other coordinate unchanged, and in particular it leaves
`w_(a_0)` unchanged. Let `γ^(-1)` be the product of these elementary matrices, so
`γ in E_r(A)`, and put `u' = γu`, `w' = wγ^(-1)`. Then

```text
v_π(w'_a) = m for every a,      τ' = γτγ^(-1) = 1 + u'w' in H,      w'u' = 0.
```

*Apply Step 3 to τ'.* Let `μ` be as in Step 3 for `w'`, so `v_π(μ) = -m` and
`v_π(q'_a) = 0` for every `a`. Given `k`, choose any `n != k` and any `a != k`. Step 3
gives `u'_k w'_n q'_a in A`, so

```text
v_π(u'_k) + m + 0 >= 0     for every k.
```

Hence `v_π(N'_(kn)) = v_π(u'_k) + v_π(w'_n) = v_π(u'_k) + m >= 0` for all `k` and `n`,
including `k = n`. That is, `N' = u'w'` has entries of nonnegative `π`-valuation.

*Undo γ.* `N = γ^(-1) N' γ`, and `γ^(±1)` has entries in `A`, so `v_π(N_(kn)) >= 0` for
all `k, n`.

The matrix `N` does not depend on `π`; only the auxiliary `γ` does. Doing this for every
prime `π | f` and applying the UFD fact gives

```text
h E_ij h^(-1) in M_r(A)     for all h in H and i != j.                     (4)
```

*Remark (no diagonal case).* After normalisation `v_π(N'_(kn))` does not depend on `n`.
So when some entry of `N'` has negative valuation, an off-diagonal entry in the same row
does too, and the proof needs no separate case for the diagonal.
The script confirms this: on random samples the diagonal branch it contains is never
entered.

## Step 5. From conjugated matrix units to h itself

Fix `h in H` and write `g = h^(-1)`. For `a != b`, (4) gives `h E_ab h^(-1) in M_r(A)`.
For `a = b`, pick any `j != a` and write
`h E_aa h^(-1) = (h E_aj h^(-1))(h E_ja h^(-1))`, which also lies in `M_r(A)`. The `(k,n)` entry of `h E_ab h^(-1)` is `h_ka g_bn`, so

```text
h_ka g_bn in A      for all k, a, b, n.                                    (5)
```

Fix a prime `π | f`. Let `α_π = min_(k,a) v_π(h_ka)` and `β_π = min_(b,n) v_π(g_bn)`.
Both are finite, since `h` and `g` are invertible. Choosing the minimising entries in
(5) gives `α_π + β_π >= 0`. The identity `1 = (hg)_11 = Σ_a h_1a g_a1` gives
`0 >= min_a v_π(h_1a g_a1) >= α_π + β_π`. Hence `β_π = -α_π`.

Put `c = ∏_(π|f) π^(α_π) in R^×` (a finite product over the prime factors of `f`, up to
units). Then `c^(-1) h` and `c g` have entries in `R` with nonnegative valuation at every
prime `π | f`, so both lie in `M_r(A)` by the UFD fact. They are mutually inverse, so
`h_0 := c^(-1) h in GL_r(A)` and `h = c·h_0 in R^×·GL_r(A)`. This proves the first
assertion.

If also `det h = 1`, then `c^r det h_0 = 1` with `det h_0 in A^×`, so `c^r in A^×` and
`r·α_π = v_π(c^r) = 0` for every `π | f`. Hence every `α_π = 0` and `c = 1`, so
`h = h_0 in SL_r(A)`. ∎

## Laurent corollary

Take `A = k[x_1,…,x_d]` and `f = x_1⋯x_d`. Suslin (1977): `SL_r(A) = E_r(A)` for `r >= 3`.
So `SL_r(A) <= H <= SL_r(R)` with `H ∩ U_12(R) = U_12(A)` forces `H <= SL_r(A)`, that
is, `H = SL_r(A)`. This holds for every `d >= 1`, and no compressor-stability hypothesis
is used.

## What the proof uses, and sanity checks

* `r >= 3` is used in Step 1 (a third index `a`) and in Step 3 (a third index `b`). The
  case `r = 2` is not addressed.
* All elements of `SL_r(A)` used are elementary: `e_ab(1)`, the Weyl elements,
  `e_ak(q_b) e_bk(-q_a)` and the `γ`'s. So `E_r(A) <= H` suffices.
* The scalars in `R^×` are genuinely allowed in `GL_r`. For instance
  `H = <E_r(A), x_1·1>` meets every root group in `U_ab(A)`.
* `experiments/root-free-overgroups-2026-09-17/root_extraction.py` evaluates the word from
  Steps 2–4 as actual matrix products over `F_p[x^(±1)]`, for random non-polynomial `h`
  with `(p,d,r) in {(2,2,3),(2,3,3),(3,3,3),(2,3,4),(3,2,4)}`. It asserts that `Y`
  equals the predicted `1 + u_k w_n v e_k^T` and that the final commutator is a single
  root element with a non-polynomial coefficient. All runs pass.
