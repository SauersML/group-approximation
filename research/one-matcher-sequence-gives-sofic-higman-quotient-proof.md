---
rg: 2
id: one-matcher-sequence-gives-sofic-higman-quotient-proof
kind: route
title: Conjugate the doubling generator by powers of the matcher, bound relators by bi-invariance, and amplify the Hamming ultralimit by tensor powers
target: one-matcher-sequence-gives-sofic-higman-quotient
requires:
  - base-two-exponential-permutations-iff-sofic-higman-quotient
artifacts:
  - research/one-matcher-sequence-gives-sofic-higman-quotient.md
---

Permutations compose right to left. The distance `d` on `Sym(X)` is bi-invariant
and satisfies `d(st, s't') <= d(s,s') + d(t,t')`. Write `R(u,v) = u v u^-1 v^-2`.
The theorem is about some fixed convention for `b^a`, so "`A,B` is a doubling action"
means `R(A,B) = 1`, or `R'(A,B) = u^-1 v u v^-2 = 1` under the other convention.
Everything below works verbatim for either. For `A(x) = 2x`, `B(x) = x + 1` on `Z/nZ`:
`A B A^-1 (x) = x + 2 = B^2 (x)`.

**Step 1: relator bounds.** Fix `X, A, B, f`. Put `P = f^-1 A f` and
`U_i = f^-i A f^i` for `i = 0,1,2,3,4`.
- `U_(i+1) = f^-i P f^i`.
- The pair `(U_i, f^-i B f^i)` is conjugate to `(A, B)`, so its relator is trivial.
- `U_(i+1)` differs from `f^-i B f^i` by `d(P, B) = eps`, by bi-invariance.
- The relator word contains the second letter three times (with multiplicity), so
  `d(R(U_i, U_(i+1)), 1) <= 3 eps` for `i = 0,1,2`.
- For the closing relator the second letter is `U_0 = A`. It differs from
  `f^-3 B f^3` by at most `d(A, U_4) + d(U_4, f^-3 B f^3)`.
  - `d(A, f^-4 A f^4) = d(f^4 A, A f^4) = r`.
  - `d(U_4, f^-3 B f^3) = d(P, B) = eps`.
- So `d(R(U_3, U_0), 1) <= 3 (eps + r)`.
- `d(U_i, 1) = d(A, 1)` by conjugation invariance.

The relator of the pair `(d, a)` in `H4` is `a^d = a^2`, so the cyclic tuple
`(U_0, U_1, U_2, U_3)` for `(a, b, c, d)` satisfies all four relators of `H4` to
within `3 eps + 3 r`.

**Step 2: the quotient.** Let `F` be free on `a,b,c,d` and, for the sequence of the
theorem, let `phi_j : F -> Sym(X_j)` send the generators to `U_(0,j), ..., U_(3,j)`.
Fix a nonprincipal ultrafilter `w` on the index set. Put

```text
ell(g) = lim_w d(phi_j(g), 1),     N = { g in F : ell(g) = 0 }.
```

- `ell(gh) <= ell(g) + ell(h)` and `ell(h g h^-1) = ell(g)`, so `N` is a normal subgroup.
- Each relator `R` of `H4` has `d(phi_j(R), 1) <= 3 eps_j + 3 r_j -> 0` by Step 1, so
  `R` is in `N`. Hence `Q = F/N` is a quotient of `H4`.
- `ell(a) >= delta > 0`, so `a` is not in `N` and `Q` is nontrivial.

**Step 3: `Q` is sofic.** Use Helfgott--Juschenko's definition: for every finite
`S` in `Q` and `delta' > 0` there is a map `psi : S -> Sym(m)` with
`d(psi(g) psi(h), psi(gh)) < delta'` whenever `g, h, gh` are in `S`, and with fewer than
`delta' m` fixed points for `psi(g)`, `g != 1` in `S`.
- Choose a lift `w_g` in `F` for each `g` in `S`, with `w_1` the empty word. Put
  `c = min { ell(w_g) : g in S, g != 1 } > 0`.
- Choose `k` with `(1 - c/2)^k < delta'`.
- The finitely many words `w_g w_h w_(gh)^-1` lie in `N`. The words `w_g`, `g != 1`,
  have `ell >= c`. So there is an index `j` with
  `d(phi_j(w_g w_h w_(gh)^-1), 1) < delta' / k` for all relevant triples, and
  `d(phi_j(w_g), 1) > c/2` for all `g != 1` in `S`.
- Put `psi(g) = phi_j(w_g)^(x k)`, the coordinatewise action on `X_j^k`.
  - The distance of `s^(x k)` from `t^(x k)` is at most `k d(s,t)`, since a point of
    `X_j^k` is moved differently only if some coordinate is. So the
    multiplicativity defect is below `delta'`.
  - The fixed-point fraction of `s^(x k)` is the `k`-th power of that of `s`, which is
    below `(1 - c/2)^k < delta'`.

So `Q` is a nontrivial sofic quotient of `H4`. This proves the theorem.

**Corollary.**
- (1 => 2): the minimizer of `S(n)` has `f^4 = id`, so its return term vanishes and
  `S'(n) <= S(n)`.
- (2 => 3): take odd `n_j` with `S'(n_j) / n_j -> 0` and minimizers `f_j`. On
  `X_j = Z/n_jZ` let `A(x) = 2x`, `B(x) = x+1`.
  - `f^-1 A f (y) != B(y)` exactly when `2 f(y) != f(y+1)`, so `eps_j` is the first
    count over `n_j`.
  - `f^4 A (x) != A f^4 (x)` exactly on the second count, so `r_j` is at most that
    count over `n_j`.
  - `A` fixes only `0`, and `S'(n) >= 1` (a map with no breakpoints is
    `f(x) = 2^x f(0)`, which is not a bijection for `n > 1`), so `n_j -> infinity`
    and `d(A, 1) = 1 - 1/n_j >= 2/3`.

  The theorem gives item 3.
- (3 => 1): `base-two-exponential-permutations-iff-sofic-higman-quotient`.
- Sharpness: if item 3 fails then item 2 fails, so `liminf S'(n)/n > 0`. Every odd
  `n >= 3` has `S'(n) >= 1`, so `S'(n) >= kappa n` for all odd `n >= 3` and some `kappa > 0`.
