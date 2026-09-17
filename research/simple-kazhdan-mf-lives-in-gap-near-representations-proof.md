---
rg: 2
id: simple-kazhdan-mf-lives-in-gap-near-representations-proof
kind: route
title: Invert the exponent-sum matrix for local rigidity; use simplicity to force asymptotic triviality; lift the Kazhdan projection through the corona to produce gap models
target: simple-kazhdan-mf-lives-in-gap-near-representations
requires:
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

Notation is as in the claim. All norms are operator norms. A tuple `u` in `U(k)^S` defines `r(u)` for words `r`.

## Step 1. Local linear rigidity (A)

Let `M` in `Z^(R x S)` be the exponent-sum matrix, `M_(r,s)` = the exponent sum of `s` in `r`. Then
`H_1(K;Q) = Q^S / (row space of M)`. So `H_1(K;Q) = 0` gives `rank M = |S|` and a left inverse `L` in
`Q^(S x R)` with `L M = I`. Put:

- `Lambda = max_s sum_r |L_(s,r)|`;
- `ell` = the maximal relator length.

**Sub-lemma 1 (dimension-free second-order bound).** In a unital Banach algebra, take elements `Y_1..Y_ell`
with `||Y_j|| <= eta`, and put `P = prod_j exp(i Y_j)`. Then

```text
||P - 1 - i sum_j Y_j|| <= e^(ell eta) - 1 - ell eta <= (ell eta)^2 e^(ell eta) / 2.
```

*Proof.* Expand each exponential and multiply out. `P - 1 - i sum Y_j` is the sum of all monomials of
total degree `>= 2`. Bound each monomial by the product of the norms of its letters. The resulting
majorant series is the scalar product `prod_j e^eta` with its degree-0 and degree-1 parts removed.
`QED`

**Sub-lemma 2.** For a unitary `u` with `||u - 1|| < 2`, the principal logarithm gives a Hermitian `X` with
`u = exp(iX)` and `||X|| <= (pi/2) ||u - 1||`.

*Proof.* The spectrum of `u` avoids `-1`. By spectral calculus `X = arg(u)` with `arg` taking values in
`(-pi, pi)`, and `|theta| <= (pi/2)|e^(i theta) - 1|` for `|theta| <= pi`, since `|e^(i theta) - 1| = 2|sin(theta/2)|`
and `sin x >= 2x/pi` on `[0, pi/2]`. `QED`

**Proof of (A).** Choose `eta_0 > 0` with `Lambda ell^2 eta_0 e^(ell eta_0) <= 1`, and put
`eps_0 = 2 eta_0 / pi` and `C = pi Lambda`. Let `D(u) <= eps_0`, and put `delta = d(u)`.

1. By Sub-lemma 2, `u_s = exp(i X_s)` with `eta := max_s ||X_s|| <= (pi/2) D(u) <= eta_0`.
2. Take a relator `r = s_1^(e_1) ... s_l^(e_l)` with `l <= ell` and `e_j = ±1`, and put `Y_j = e_j X_(s_j)`.
   Then `r(u) = prod_j exp(i Y_j)` and `sum_j Y_j = Z_r := sum_s M_(r,s) X_s`.
3. By Sub-lemma 1, `||Z_r|| <= ||r(u) - 1|| + (ell eta)^2 e^(ell eta)/2 <= delta + (ell eta)^2 e^(ell eta)/2`.
4. Since `X_s = sum_r L_(s,r) Z_r`, we get `eta <= Lambda delta + Lambda ell^2 eta^2 e^(ell eta)/2`.
5. By the choice of `eta_0`, the last term is at most `eta/2`. So `eta <= 2 Lambda delta`.
6. Finally `||u_s - 1|| = ||exp(i X_s) - 1|| <= ||X_s||`, so `D(u) <= 2 Lambda delta <= C d(u)`.

Every constant depends only on `(S, R)`. `QED`

**Calibration.** Step 1 uses only `H_1(K;Q) = 0`. It holds verbatim for `SL_3(Z)` (Steinberg
presentation, perfect), which is residually finite, hence MF.

## Step 2. Imported facts for (B)

- **(I1)** The Titz Mite--Witzel residuals are finitely presented, infinite, simple and Kazhdan
  (`titz-witzel-simple-kazhdan-cat0-lattices-exist`). Being nonabelian and simple, they are perfect, so
  `H_1(K;Q) = 0`.
- **(I2) Malcev (1940).** A finitely generated subgroup of `GL_k(C)` is residually finite.
- **(I3) Spectral gap from (T).** Let `(S, eps)` be a Kazhdan pair with `S` generating (it exists by (T)).
  Then in every unitary representation, `Delta = sum_s (2 - u_s - u_s^*) >= eps^2 (1 - P_inv)`, where `P_inv`
  is the projection onto the invariant vectors.
  *Proof:* `P_inv` commutes with the representation. For `xi` orthogonal to the invariant vectors, some `s` has
  `||u_s xi - xi|| >= eps ||xi||`, and `<Delta xi, xi> = sum_s ||u_s xi - xi||^2 >= eps^2 ||xi||^2`.
  Apply this in the universal representation. `Delta` has spectrum in `{0} ∪ [kappa, 4|S|]` with
  `kappa >= eps^2 > 0`, and `p = chi_({0})(Delta) = P_inv` is central with `g p = p g = p` for all `g` in `K`.
- **(I4)** Projections in `prod_n M_(k_n) / sum_n M_(k_n)` lift to projections, and positive elements
  lift to positive elements.

**Lemma 2.1 (no nontrivial finite-dimensional representations).** Under (I1), every homomorphism
`rho: K -> U(k)` is trivial.

*Proof.* Suppose `rho` is not trivial. Its kernel is a proper normal subgroup, hence trivial, so `K` embeds in
`GL_k(C)`. By (I2), `K` is then residually finite. An infinite simple group is not residually finite. `QED`

**Lemma 2.2 (sequence dichotomy).** Assume (I1). Let `u^(n)` be in `U(k_n)^S` with `d(u^(n)) -> 0`. Then
either `K` is MF, or `D(u^(n)) -> 0`.

*Proof.* Put `Q = prod_n M_(k_n) / sum_n M_(k_n)`, and let `U_s` be the class of `(u^(n)_s)_n`. Each relator
`r` satisfies `r(U) = 1`, since `||r(u^(n)) - 1|| -> 0`. So `s -> U_s` defines a homomorphism
`pi: K -> U(Q)`, and its kernel is `1` or `K`.

- If the kernel is `1`, then `K` is MF.
- If the kernel is `K`, then `U_s = 1` for every `s`, which means `||u^(n)_s - 1|| -> 0` for every `s`. `QED`

**Corollary 2.3.** Assume (I1), and that `K` is not MF. Then for every `eps > 0` there is `delta > 0` such
that `d(u) <= delta` implies `D(u) <= eps`, in every dimension.

*Proof.* Otherwise there are `eps > 0` and tuples `u^(n)` with `d(u^(n)) <= 1/n` and `D(u^(n)) > eps`. This
contradicts Lemma 2.2. `QED`

## Step 3. Proof of (B)

**3.1. `delta_t(k)` is attained and positive.**

- *Attained.* The set `{u in U(k)^S : Delta(u) >= t}` is compact and nonempty (`u_s = -1` gives
  `Delta = 4|S|`), and `d` is continuous, so the minimum exists.
- *Positive.* If `d(u) = 0`, then `u` is a genuine representation, so it is trivial by Lemma 2.1, and
  `Delta(u) = 0 < t`. That contradicts `Delta(u) >= t`.

**3.2. Gap tuples are far from trivial.** If `Delta(u) >= t` with `k >= 1`, then
`t <= ||Delta(u)|| <= sum_s ||(1 - u_s)^*(1 - u_s)|| = sum_s ||u_s - 1||^2`. So `D(u) >= sqrt(t/|S|)`.

**3.3. Not MF implies `inf_k delta_t(k) > 0`, for any `t > 0`.** By Corollary 2.3 with `eps = sqrt(t/|S|)/2`,
there is `delta > 0` such that `d(u) <= delta` forces `D(u) <= eps`. By 3.2, this excludes `Delta(u) >= t`.
So `delta_t(k) > delta` for every `k`.

**3.4. MF implies `inf_k delta_t(k) = 0`, for `t < kappa`.**

1. *The model.* Let `K` embed in `U(Q)`, with `Q = prod M_(k_n) / sum M_(k_n)`. Lift the generator images to
   unitaries `u^(n)_s`; unitaries in `Q` lift to unitaries of `prod M_(k_n)` by polar decomposition of a lift,
   once `n` is large. Then `d(u^(n)) -> 0`. Extend `pi` to a unital *-homomorphism `pi: C*(K) -> Q`.
2. *A nonzero corner.* Put `e = 1 - pi(p)`. If `e = 0`, then `pi(u_s) = pi(u_s p) = pi(p) = 1` for all `s`, so
   `pi` is trivial on `K`, contradicting injectivity with `K != 1`. So `e != 0`. It is central in `pi(C*(K))`,
   and `e pi(Delta) e >= kappa e`.
3. *The lift.* By (I4), lift `e` to projections `E_n`. Since `e != 0`, `E_n != 0` for `n` in an infinite set `N`.
   Moreover `||[E_n, u^(n)_s]|| -> 0`. Lifting the positive element `e pi(Delta) e - kappa e` gives
   `E_n Delta(u^(n)) E_n >= (kappa - o(1)) E_n`.
4. *The compressed tuple.* For `n` in `N`, let `v^(n)_s` be the polar part of `E_n u^(n)_s E_n` inside
   `E_n M_(k_n) E_n`, which has dimension `rank E_n >= 1`. Then:
   - `||E_n u^(n)_s E_n - u^(n)_s E_n|| -> 0`, so `E_n u^(n)_s E_n` is asymptotically unitary in the corner, and
     `||v^(n)_s - E_n u^(n)_s E_n|| -> 0`;
   - words of bounded length are uniformly continuous in their letters, so `d(v^(n)) -> 0`;
   - `Delta(v^(n)) = E_n Delta(u^(n)) E_n + o(1) >= (kappa - o(1)) E_n`.
5. *Conclusion.* Since `t < kappa`, for large `n` in `N` we get `Delta(v^(n)) >= t` and
   `delta_t(rank E_n) <= d(v^(n)) -> 0`. `QED`

**3.5. (GAP).**

- *Not MF implies (GAP).* Apply Corollary 2.3 with `eps = eps_0` from (A). That gives `delta_0`, and then
  `D(u) <= C d(u)` whenever `d(u) <= delta_0`. So `C' = C`.
- *(GAP) implies not MF.* If `K` were MF, then 3.4 gives tuples with `d -> 0` and `D >= sqrt(t/|S|)` by 3.2.
  That contradicts `D <= C' d`. `QED`

## Step 4. Proof of (C)

`U(k)^S` is a real algebraic set in `R^(2 k^2 |S|)`. The condition "`||A|| < q`" is the positive-definiteness
of `q^2 - A^*A`, which is semialgebraic (leading principal minors). "`Delta(u) >= t`" is
positive-semidefiniteness, which is semialgebraic (all principal minors `>= 0`). So "`delta_t(k) < q`" is an
existential first-order sentence over the real field with rational parameters, and it is computable from
`(k, t, q, S, R)`. It is decidable by Tarski--Seidenberg quantifier elimination. By 3.3, 3.4 and attainment:
`K` is MF iff for every `m` there is `k` with `delta_(t_0)(k) < 1/m`. `QED`

## Where every perturbative method dies

- *The only anchor.* The only genuine finite-dimensional representations are trivial (Lemma 2.1). A method that
  corrects a near-representation towards a genuine one therefore works in some operator-norm neighbourhood of
  the trivial tuple.
- *What it can see.* On that neighbourhood the conclusion `D <= C d` is already Step 1, which uses only
  `H_1(K;Q) = 0` and holds for the MF group `SL_3(Z)`.
- *What it misses.* The models that decide MF-ness are the gap tuples of 3.4, with `D >= sqrt(t/|S|)`.
- *Why padding is no escape.* In operator norm, `D(u ⊕ 1) = D(u)` and `d(u ⊕ 1) = d(u)`. Adding trivial blocks
  neither shrinks nor dilutes a gap block. This is the step where the Hilbert--Schmidt padding argument
  (`padding-makes-local-hs-rigidity-global`) fails.
- *The invariant.* It is `inf_k delta_t(k)`. A proof of the target must bound it from below.
