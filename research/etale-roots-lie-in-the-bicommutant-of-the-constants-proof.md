---
rg: 2
id: etale-roots-lie-in-the-bicommutant-of-the-constants-proof
kind: route
title: Differentiate the conjugation action of the centralizer on the root set over the dual numbers, read off the tensor structure of the Fox-derivative operator, and compute the diagonal case
target: etale-roots-lie-in-the-bicommutant-of-the-constants
requires: []
---

Notation as in the claim. `L[eps]` is the ring of dual numbers, `eps^2 = 0`.

**Step 1 (first-order substitution).** For `T` in `GL_N(L)`, `c` in `GL_N(L)^k`
and `Y` in `M_N(L)`,

```text
w(T (1 + eps Y) ; c) = w(T ; c) (1 + eps D_{T,c}(Y)) .
```

*Proof.* Let `z_i` be the value of `y_i` at `(T ; c)`, so `S_i = z_{i+1} ... z_l`.
At `(T(1 + eps Y) ; c)` the value of `y_i` is `z_i v_i`, where:
- `v_i = 1 + eps Y` if `y_i = x`;
- `v_i = T (1 - eps Y) T^{-1}` if `y_i = x^{-1}`, since
  `(T(1 + eps Y))^{-1} = (1 - eps Y) T^{-1} = T^{-1} (T (1 - eps Y) T^{-1})`;
- `v_i = 1` otherwise.

Downward induction on `i`, using `v_i S_i = S_i (S_i^{-1} v_i S_i)`, gives
`z_1 v_1 ... z_l v_l = (z_1 ... z_l) prod_i S_i^{-1} v_i S_i`. Each factor is
`1 + eps (something)`, and over `L[eps]` such a product is `1 + eps` times the
sum. The factor is:
- `1 + eps S_i^{-1} Y S_i` for `y_i = x`;
- `1 - eps (T^{-1} S_i)^{-1} Y (T^{-1} S_i) = 1 - eps S_{i-1}^{-1} Y S_{i-1}` for
  `y_i = x^{-1}`, because `T^{-1} S_i = z_i S_i = S_{i-1}`.

The sum is `D_{T,c}(Y)`. (This is Step 2 of
`etale-roots-of-the-semisimplification-lift-to-exact-roots-proof` with
`A = L[[eps]]` and `j = 1`, truncated at first order.)

**Step 2 (Theorem G).** Let `T` be an etale root and `X` in `C(c)`.
1. `g = 1 + eps X` is invertible in `M_N(L[eps])` with inverse `1 - eps X`, and it
   commutes with every `c_j^{+-1}`.
2. Substituting `x |-> g T g^{-1}` conjugates the value of every letter by `g`, so
   `w(g T g^{-1} ; c) = g w(T ; c) g^{-1} = 1`.
3. `g T g^{-1} = T + eps (XT - TX) = T (1 + eps Y)` with `Y = T^{-1} X T - X`.
4. By Step 1, `1 = w(T ; c)(1 + eps D_{T,c}(Y)) = 1 + eps D_{T,c}(Y)`, so
   `D_{T,c}(Y) = 0`.
5. `D_{T,c}` is invertible, so `Y = 0`, that is `XT = TX`.

**Step 3 (Corollary H).** Identify `M_{Nr}(L) = M_N(L) (x) M_r(L)`.
- *Amplified roots.* Let `T_0` be a root. Then `w(T_0 (x) 1_r ; c (x) 1_r) = w(T_0 ; c) (x) 1_r = 1`.
  Every suffix value is `S_i^0 (x) 1_r`, where `S_i^0` is the suffix value at
  `(T_0 ; c)`. So `D(Y_0 (x) Z) = D_{T_0,c}(Y_0) (x) Z`, that is
  `D = D_{T_0,c} (x) id`, which is invertible if and only if `D_{T_0,c}` is.
- *Every etale root is amplified.* Let `T` be an etale root for `c (x) 1_r`.
  1. For each `Z` in `M_r(L)`, `1_N (x) Z` commutes with every `c_j (x) 1_r`.
     By Theorem G, `T` commutes with `1_N (x) M_r(L)`.
  2. Write `T = sum_{p,q} T_pq (x) E_pq` with `T_pq` in `M_N(L)`. Commuting with
     `1_N (x) E_st` for all `s, t` forces `T_pq = 0` for `p != q` and all `T_pp`
     equal. So `T = T_0 (x) 1_r`, and `T_0` is invertible because `T` is.
  3. `w(T_0 ; c) (x) 1_r = 1` gives `w(T_0 ; c) = 1`, and by the first bullet
     `D_{T_0,c}` is invertible.

**Step 4 (Corollary I).**
- *The bicommutant.* For equivalent `p, q` every `d_j` has equal `(p,p)` and
  `(q,q)` entries, so `E_pq` is in `C(d)`; every `E_pp` is in `C(d)`.
  - Commuting with every `E_pp` forces `T` diagonal.
  - Commuting with `E_pq` for equivalent `p != q` forces `T_pp = T_qq`.

  By Theorem G an etale root is diagonal and constant on classes.
- *Roots.* Diagonal matrices commute, so `w(T ; d) = T^m prod_j d_j^{f_j}`; this is
  the stated equation entry by entry.
- *The operator.* All `S_i` are diagonal and
  `S^{-1} E_pq S = (S_qq / S_pp) E_pq`. So `D_{T,d}` is diagonal in the basis
  `E_pq` with eigenvalues `s_pq`.
  - If `p, q` are equivalent, `T` and every `d_j` have equal `(p,p)` and `(q,q)`
    entries, so every `psi_pq(S_i) = 1` and `s_pq = m`, which is nonzero by
    hypothesis.
  - So `D_{T,d}` is invertible if and only if `s_pq != 0` for all inequivalent
    `p, q`.

**Step 5 (Corollary J).** `a = diag(2, 1)` is invertible when `char L != 2`, and
`2 != 1` in every field, so indices `1, 2` are inequivalent.
1. *No etale root at `r = 1`.* The exponent sums are `m = 1`, `f_a = 0`, `f_b = 1`,
   and `b = 1`. By Corollary I an etale root is diagonal, and diagonal roots
   satisfy `T = 1`. At `T = 1` the suffix values after the two letters `x` are
   `x a x^{-1} a^{-1} b -> 1` and `a x^{-1} a^{-1} b -> 1`. The suffix from the
   letter `x^{-1}` is `x^{-1} a^{-1} b -> a^{-1} = diag(1/2, 1)`. So
   `s_12 = 1 + 1 - 2 = 0`.
2. *No etale root at any `r`,* by Corollary H.
3. *The root set in characteristic 0.*
   - `w(T ; a, 1) = 1` means `T^2 a T^{-1} a^{-1} = 1`, that is `a^{-1} T^2 a = T`.
     So `T` is similar to `T^2`, and the eigenvalue multiset `{lambda, mu}` equals
     `{lambda^2, mu^2}`.
   - Either `lambda = mu = 1`, or `{lambda, mu} = {omega, omega^2}` with `omega` a
     primitive cube root of unity.
   - *Cube-root case.* `T` has distinct eigenvalues `omega, omega^2`, so `det T = 1`
     and `T^3 = 1`, hence `a^{-1} T a = T^{-1}`. The conjugate is
     `[[t_11, t_12/2], [2 t_21, t_22]]` and the inverse is
     `[[t_22, -t_12], [-t_21, t_11]]`. Comparing entries gives `t_12 = t_21 = 0`
     and `t_11 = t_22`, so `T` is scalar, contradicting distinct eigenvalues.
   - *Unipotent case.* `T = 1 + N` with `N^2 = 0`, and `a^{-1} T^2 a = T` becomes
     `a^{-1} N a = N/2`. For `N = [[p, q], [s, -p]]` the left side is
     `[[p, q/2], [2s, -p]]`, so `p = 0` and `s = 0`. Hence `T = 1 + t E_12`.
   - *These are roots.* `T^2 = 1 + 2t E_12` and `a T^{-1} a^{-1} = 1 - 2t E_12`,
     whose product is `1`.
4. *The kernel.* At `T = 1 + t E_12`, the suffix values are:
   - `S_1 = T a T^{-1} a^{-1} = 1 - t E_12`;
   - `S_2 = a T^{-1} a^{-1} = 1 - 2t E_12`;
   - `S_3 = T^{-1} a^{-1}`.

   Upper unitriangular `S` fix `E_12` under conjugation, and
   `S_3^{-1} E_12 S_3 = a T E_12 T^{-1} a^{-1} = a E_12 a^{-1} = 2 E_12`. So
   `D(E_12) = E_12 + E_12 - 2 E_12 = 0`.

**Step 6 (the remark).** The matrix in the claim is `D_{T_0,(a, 1+E_12)}`
computed from the definition with exact rational arithmetic (script
`research/artifacts/hl-kl-etale-g1-2026-09-14-fox-operator-check.py`). The same
script confirms:
- `w(T_0 ; a, 1 + E_12) = 1`;
- `D_{1,1} = m id`;
- rank `3` of `D` at `1 + t E_12` for `t = 0, 1, 3, -2/7`;
- rank `16` at `T_0 (x) 1_2` and rank `12` at `(1 + E_12) (x) 1_2`, as Corollary H
  predicts.

Its determinant `9/4` is the only input to the remark, and Theorem G and
Corollaries H to J do not use it.
