---
rg: 2
id: amplified-roots-fail-in-odd-characteristic-proof
kind: route
title: The root forces an almost free rank profile for s - 1 over Z/p^2, while an operator anticommuting with the reflection caps its eigenvalue excess by dim ker(s - 1)
target: amplified-roots-fail-in-odd-characteristic
requires: []
artifacts:
  - research/artifacts/ideas-nonhyperlinear-2026-09-13.md
---

**Setup.** `N = pr`, `rk` is rank, `epsilon = rho(w_p(T) - 1)`. Write `a, b`
for `a (x) 1_r, b (x) 1_r`, and put `c = ab`, `s = T`, `k = (p+1)/2`.

**Rank facts.**
- (F1) `rk(PXQ - PZQ) = rk(X - Z)` for invertible `P, Q`, and
  `rk(X + Z) <= rk X + rk Z`.
- (F2) `rk(X^j - Z^j) <= j rk(X - Z)`, from
  `X^j - Z^j = sum_i X^i (X - Z) Z^{j-1-i}`; and
  `rk(X^{-1} - Z^{-1}) = rk(X - Z)`.
- (F3) `dim ker X <= dim ker Z + rk(X - Z)`.
- (F4) For an operator `y`, `delta_j = rk(y^j) - rk(y^{j+1}) = dim(ker y ∩ im y^j)`
  is nonincreasing in `j`.
- (F5) In characteristic `p`, `(s - 1)^p = s^p - 1`.
- (F6) `c^{-1}` is a `p`-cycle matrix amplified `r` times. Its minimal
  polynomial per copy is `x^p - 1 = (x - 1)^p`, so `c^{-1} - 1` is nilpotent
  with `r` Jordan blocks of size `p`, and `rk((c^{-1} - 1)^j) = (p - j) r` for
  `0 <= j <= p`.

**Step 1.** Put `beta = s^k a s^{-(k-1)}`. Then `w_p(T) = beta b` and
`beta - b = (beta b - 1) b`, so `rk(beta - b) <= epsilon N`.

**Step 2.** Since `b^2 = 1`, (F2) gives `rk(beta^2 - 1) <= 2 epsilon N`. Now
`beta^2 = s^k a s a s^{-(k-1)}`, and multiplying by `s^{-k}` on the left and
`s^{k-1}` on the right turns `beta^2 - 1` into `a s a - s^{-1}`. So
`rk(a s a - s^{-1}) <= 2 epsilon N`.

**Step 3.** `a beta = (a s a)^k s^{-(k-1)}`. By step 2 and (F2),
`rk((asa)^k - s^{-k}) <= 2k epsilon N = (p+1) epsilon N`. Since
`k + (k-1) = p`, `rk(a beta - s^{-p}) <= (p+1) epsilon N`. With
`rk(c - a beta) = rk(b - beta) <= epsilon N` this gives
`rk(c - s^{-p}) <= (p+2) epsilon N`, hence by (F1)
`rk(s^p - c^{-1}) <= (p+2) epsilon N`, using `s^p - c^{-1} = s^p (c - s^{-p}) c^{-1}`.

**Step 4 (rank profile).** Put `y = s - 1` and `d_j = rk(y^j)`. By (F5),
`y^{jp} = (s^p - 1)^j`, so (F2), (F6) and step 3 give
`|d_{jp} - (p - j) r| <= j (p+2) epsilon N` for `j = 1, 2`. Then
`delta_p + ... + delta_{2p-1} = d_p - d_{2p} >= r - 3(p+2) epsilon N`, and by
(F4) the largest of these is `delta_p`, so
`delta_p >= r/p - 3(p+2) epsilon N/p`, and
`delta_1, ..., delta_{p-1} >= delta_p`. Also
`delta_0 + ... + delta_{p-1} = N - d_p <= r + (p+2) epsilon N`. Therefore

```text
dim ker y = delta_0 <= r + (p+2) epsilon N - (p-1)(r/p - 3(p+2) epsilon N/p)
          = N/p^2 + ((p+2)(4p-3)/p) epsilon N .
```

**Step 5 (an almost anticommuting operator).** Put `m = (p^2 + 1)/2`, `h = s^m`
and `Y = h - h^{-1}`. By step 2 and (F2),
`rk(a h a - h^{-1}) = rk((asa)^m - s^{-m}) <= (p^2+1) epsilon N`, and the same
bound holds for `a h^{-1} a - h`. So `rk(a Y a + Y) <= 2(p^2+1) epsilon N`.
Next, `Y - h^{-1} y = h^{-1}(s^{p^2+1} - s) = h^{-1} s (s^{p^2} - 1)`, and
`rk(s^{p^2} - 1) = rk((s^p)^p - (c^{-1})^p) <= p(p+2) epsilon N` by step 3,
(F2) and `c^p = 1`. By (F3), `dim ker Y <= dim ker y + p(p+2) epsilon N`.

**Step 6 (graded count).** `a` is an involution and `p` is odd, so
`L^N = V_+ ⊕ V_-` with eigenvalues `+1, -1`, of dimensions `e_+, e_-`. In this
decomposition `Y = [[A, B], [C, D]]`, `a Y a = [[A, -B], [-C, D]]`, so
`a Y a + Y = [[2A, 0], [0, 2D]]` and `rk A + rk D = rk(a Y a + Y)`. Put
`Y_0 = [[0, B], [C, 0]]`. Then `ker Y_0 = ker C ⊕ ker B`, and
`C : V_+ -> V_-` has `dim ker C >= e_+ - e_-`. By (F3),

```text
e_+ - e_-  <=  dim ker Y_0  <=  dim ker Y + rk A + rk D  <=  dim ker Y + rk(a Y a + Y).
```

**Step 7.** A reflection of the `p`-gon fixes one vertex and swaps `(p-1)/2`
pairs, so per copy its `+1`-eigenspace has dimension `(p+1)/2` and its
`-1`-eigenspace `(p-1)/2`. Hence `e_+ - e_- = r = N/p`. Combining steps 4–6,

```text
N/p <= N/p^2 + [ (p+2)(4p-3)/p + p(p+2) + 2(p^2+1) ] epsilon N ,
```

that is, `epsilon >= (p-1)/(p^2 K_p)`. For `p = 3`, `K_3 = 50` and
`epsilon >= 1/225`.

**Instance.** For `T` in `GL_{3r}(L)` put `s = T a`. Then
`T a T a T^{-1} b = s^2 a s^{-1} b = w_3(s)` exactly, since `a^2 = 1`. So the
word `x a x a x^{-1} b` with `a = (0 1)`, `b = (0 2)` has the same defects.
These are two distinct reflections of the triangle.

**Remark (the adjunction).** At `epsilon = 0`, steps 1–3 read `a^2 = 1`,
`(a x)^2 = 1`, `b = x^p a` and `x^{p^2} = 1` in
`(<a,b> * <x>)/<<w_p>>`. Conversely these relations give
`w_p = x^{2k-1} a x^p a = x^p x^{-p} = 1` and the `D_p` relations. So the
adjunction is `D_{p^2}`, containing `D_p = <a, x^p>`.
