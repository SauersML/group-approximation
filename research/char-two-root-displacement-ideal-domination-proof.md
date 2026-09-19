---
rg: 2
id: char-two-root-displacement-ideal-domination-proof
kind: route
title: Reduce to a finite ring, average one entry of the spectral measure of a two-sided block root group over left and right elementary moves and permutations, and read displacement off the largest two-sided ideal killed by the character
target: char-two-root-displacement-is-two-sided-ideal-dominated
requires:
  - positive-characteristic-steinberg-unitary-images-are-finite
---

Notation as in the target. All rings satisfy `2 = 0`, so signs play no role and `-1 = 1`. The commutator is
`[x, y] = x y x^-1 y^-1`. Steinberg relations in `St_n(B)`: `x_ij(a) x_ij(b) = x_ij(a + b)`;
`[x_ij(a), x_jk(b)] = x_ik(ab)` for distinct `i, j, k`; `[x_ij(a), x_kl(b)] = 1` for `j != k`, `i != l`.

## Step 0. Reduction to a finite ring

By `positive-characteristic-steinberg-unitary-images-are-finite` (with `m = 2`, `n >= 3`), verbatim: "`I := {a in A :
rho(x_12(a)) = 1}` is a two-sided ideal ... `|A/I| <= m^d` ... `rho` factors through the natural map
`St_n(A) -> St_n(A/I)`." So `pi = pi' o St_n(pr)` with `B' = B/I` finite. Then `nu(e)` is computed by `pi'` at the
image `e'`, and `Q in (e_1, ..., e_s)` gives `Q' in (e'_1, ..., e'_s)`. So assume `B` finite.

## Step 1. The block root group and its spectral measure

Choose a partition `{1, ..., n} = I ⊔ K` with `|I| = p`, `|K| = r`, `i0 in I`, `j0 in K`. Put

```text
x(a) = prod_(i in I, k in K) x_ik(a_ik),        a = (a_ik) in X := M_(I x K)(B).
```

- *Homomorphism.* Any two factors commute: for `x_ik`, `x_jl` with `i, j in I` and `k, l in K`, `k != j` and
  `i != l` because `I ∩ K` is empty. With additivity, `x : (X, +) -> St_n(B)` is a homomorphism.
- *Characters.* `X` is a finite `F_2`-vector space. Its characters are
  `psi_c(a) = (-1)^(sum_(i,k) c_ik(a_ik))`, `c = (c_ik)`, `c_ik in B^ := Hom_(F_2)(B, F_2)`.
- *Spectral measure.* `pi o x` splits `C^N = ⊕_c H_c`, with `pi(x(a)) = psi_c(a)` on `H_c`. Put
  `mu(c) = dim H_c / N`. For `e in B`, let `e E` be the matrix with `e` at `(i0, j0)` and `0` elsewhere. Since
  `pi(x_(i0 j0)(e)) = pi(x(eE))` acts on `H_c` by `±1`,

  ```text
  m(e) := nu(e)^2 / 4 = mu{ c : c_(i0 j0)(e) = 1 }.                                    (1)
  ```

- *Invariance.* If `g in St_n(B)` satisfies `g x(a) g^-1 = x(alpha(a))` for an additive bijection `alpha` of `X`,
  then `pi(g) H_c = H_(c')` with `psi_(c')` = `psi_c o alpha^-1`. So `mu` is invariant under `c -> c o alpha`, the
  character `a -> psi_c(alpha(a))`.

## Step 2. The moves

1. **Left elementary moves.** For `j != l` in `I` and `b in B`, conjugation by `x_jl(b)` fixes `x_ik(a)` for
   `i != l` (the commutation relation applies, as `l != i` and `j != k` because `k in K`), and sends `x_lk(a)` to `x_jk(ba) x_lk(a)` by
   `[x_jl(b), x_lk(a)] = x_jk(ba)`. So `alpha(a) = (1 + b E_jl) a`.
2. **Right elementary moves.** For `k != l` in `K`, conjugation by `x_kl(b)` fixes `x_ij(a)` for `j != k`, and
   sends `x_ik(a)` to `x_ik(a) x_il(ab)`, since `[x_kl(b), x_ik(a)] = [x_ik(a), x_kl(b)]^-1 = x_il(ab)^-1 = x_il(ab)`.
   So `alpha(a) = a (1 + b E_kl)`.
3. **Permutations.** Over `F_2`, `(1 + E_jl)(1 + E_lj)(1 + E_jl)` is the permutation matrix of the transposition
   `(j l)`. So the moves generate all row permutations of `I` and all column permutations of `K`.

Write `(b . phi)(x) = phi(xb)` and `(phi . b)(x) = phi(bx)` for `phi in B^`.

- Left move `(1 + b E_jl)`: `psi_c((1 + bE_jl)a) = psi_c(a) * (-1)^(sum_k c_jk(b a_lk))`. So the new character has
  `c'_lk = c_lk + c_jk . b`, and all other entries unchanged.
- Right move `(1 + b E_kl)`: `psi_c(a(1 + bE_kl)) = psi_c(a) * (-1)^(sum_i c_il(a_ik b))`. So `c'_ik = c_ik + b . c_il`,
  and all other entries unchanged.

## Step 3. Two-sided averaging of one entry

Enumerate `I = {i0 = 1, 2, ..., p}` and `K = {j0 = 1, 2, ..., r}`. Take independent uniform
`b' = (b'_2, ..., b'_p) in B^(p-1)` and `b = (b_2, ..., b_r) in B^(r-1)`, with `b'_1 = b_1 = 1`. Let
`alpha_(b', b)(a) = g a h`, where `g = 1 + sum_(j >= 2) b'_j E_j1` and `h = 1 + sum_(l >= 2) b_l E_1l`. These are
products of commuting left and right elementary moves, so `mu` is invariant under each `c -> c o alpha_(b', b)`.

For `a = eE`, `g (eE) h` has entry `b'_j e b_l` at `(j, l)`. Hence the `(1,1)` entry of the moved character, at `e`, is

```text
f_(c,e)(b', b) = sum_(j in I, l in K) c_jl(b'_j e b_l).                                  (2)
```

This is checked by direct block multiplication in the artifact script, not by this formula.

**Lemma 3.1.** *Put `A(c, e) = {(j, l) : c_jl` does not vanish on the two-sided ideal `BeB}`.*
- *If `A(c, e)` is empty, then `f_(c,e) = 0` identically.*
- *If `A(c, e)` contains some `(j, l)` with `j != 1` and `l != 1`, then `P_(b', b)(f_(c,e) = 1) >= 1/4`.*

*Proof.* Read `f = f_(c,e)` as a function on the `F_2`-space `B^(p-1) x B^(r-1)`. It is a sum of
- the constant `c_11(e)`;
- for `l >= 2`, the linear form `lambda_l(b_l) = c_1l(e b_l)`;
- for `j >= 2`, the linear form `lambda'_j(b'_j) = c_j1(b'_j e)`;
- for `j, l >= 2`, the bilinear form `beta_jl(b'_j, b_l) = c_jl(b'_j e b_l)`.

*First case.* Each term is `c_jl` evaluated on an element of `BeB`, so all vanish.

*Second case.* Suppose `f` is constant. Setting every variable to `0` except `b_l` gives `lambda_l = 0`; similarly
`lambda'_j = 0`; setting every variable to `0` except `b'_j` and `b_l` then gives `beta_jl = 0`. But `beta_jl = 0`
means that `c_jl` vanishes on `{x e y}`, hence on its span `BeB`. So if `(j, l) in A(c, e)` with `j, l >= 2`, `f`
is not constant, and in particular not the zero function. In `F_2`-coordinates `f` is a multilinear polynomial of
degree at most 2. A nonzero reduced polynomial of degree at most `d` in `M` variables over `F_2` is nonzero on at
least `2^(M-d)` points (the minimum distance of the Reed--Muller code `RM(d, M)`). Since `f` is `F_2`-valued,
`P(f = 1) = P(f != 0) >= 2^-2 = 1/4`. ∎

## Step 4. Permutations and the two-sided bound

Put `J(c) = {e in B : A(c, e) is empty}`, the set of `e` with `c_jl(BeB) = 0` for all `(j, l)`.

**Lemma 4.1.** *`J(c)` is a two-sided ideal.* It is the largest two-sided ideal on which every `c_jl` vanishes:
`B(e + e')B ⊆ BeB + Be'B`, `B(be)B ⊆ BeB`, `B(eb)B ⊆ BeB`, and each `c_jl` is additive. ∎

Let `N(e) = mu{ c : e not in J(c) }`.

**Lemma 4.2.** `kappa N(e) <= m(e) <= N(e)`, with `kappa = (1/4)(1 - 1/p)(1 - 1/r)`.

*Proof.* Let `sigma, tau` be uniform permutations of `I` and `K`, independent of `b', b`, and let `c^(sigma,tau)`
be the permuted character, `c^(sigma,tau)_jl = c_(sigma j, tau l)`. By Step 2 and Step 1 (invariance),

```text
m(e) = E_(c ~ mu) h_e(c),     h_e(c) = E_(sigma, tau) P_(b', b)( f_(c^(sigma,tau), e) = 1 ).
```

- *Upper.* `A(c^(sigma,tau), e)` is the permuted `A(c, e)`. If `e in J(c)` it is empty for every
  `(sigma, tau)`, so `h_e(c) = 0` by Lemma 3.1. Always `h_e(c) <= 1`.
- *Lower.* If `e not in J(c)`, fix `(j, l) in A(c, e)`. Then `(sigma^-1 j, tau^-1 l)` avoids row `1` and column `1`
  with probability `(1 - 1/p)(1 - 1/r)`, and then Lemma 3.1 gives conditional probability at least `1/4`.
  So `h_e(c) >= kappa`. ∎

So the pointwise inequalities `kappa 1[e not in J(c)] <= h_e(c) <= 1[e not in J(c)]` hold for every character `c`.
They are what the artifact script checks exhaustively.

## Step 5. Conclusion

Let `Q in (e_1, ..., e_s)`. If `Q not in J(c)`, then some `e_i not in J(c)`: otherwise the two-sided ideal `J(c)`
would contain `(e_1, ..., e_s)` and so `Q`. Hence `1[Q not in J(c)] <= sum_i 1[e_i not in J(c)]`, and integrating
against `mu`, `N(Q) <= sum_i N(e_i)`. By Lemma 4.2,

```text
nu(Q)^2 = 4 m(Q) <= 4 N(Q) <= 4 sum_i N(e_i) <= (4 / kappa) sum_i m(e_i) = (1/kappa) sum_i nu(e_i)^2.
```

`1/kappa = 4/((1 - 1/p)(1 - 1/r)) = C_(p,r)`. ∎

## Remarks

- The number of terms needed to write `Q` in the ideal never enters: the comparison is between indicator functions
  of one ideal `J(c)` per character. This is what the one-sided row group of
  `leavitt-cone-head-bound-semisimple-ring-shadows-proof` could not supply for rings with radical: a one-sided row
  group sees only the right ideal `{e : c(eB) = 0}`, which the unit group need not move.
- Where characteristic two is used: the characters are `±1`-valued, and Lemma 3.1 is a statement over `F_2`. For
  characteristic `m` the same proof works with `F_m`-valued characters when `m` is prime, with `1/4` replaced by the
  degree-two Reed--Muller bound over `F_m`; that case is not claimed here.
- `p, r >= 2` is needed: with `p = 1` there is no row outside the cross and Lemma 3.1's second case is empty.
