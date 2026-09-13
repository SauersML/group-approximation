---
rg: 2
id: simple-group-support-and-semisimple-rank-models-collapse-proof
kind: route
title: Normalize on the moved set or moved subspace, then use simplicity to make the ultraproduct homomorphism injective
target: simple-group-support-and-semisimple-rank-models-collapse
requires: []
---

Throughout, `G = <X | R>` is infinite, finitely presented and simple, `g_0 != 1`,
and `f` is nondecreasing and subadditive with `f(0) = 0`.

## 0. Weak soficity of a simple group needs one separated element

- **Models give weak soficity.** Given models `a^(n)` in `(H_n, l_n)` with parameter
  `eps_n -> 0`, put `Q = prod_omega H_n / N_omega`, with `N_omega` the sequences of
  length tending to `0` along `omega`. Here `H_n` is restricted to sequences of
  bounded length, which contain the generator images.
  - `x -> [(a_x^(n))]` kills every relator, so it defines a homomorphism `G -> Q`.
  - `g_0` has limit length at least `1`, so the homomorphism is nontrivial.
  - Its kernel is normal and `G` is simple, so it is injective.
  - A countable subgroup of a metric ultraproduct of finite groups is weakly sofic
    (`metric-ultraproduct-surjunctivity-from-weak-sofic-case`, second bullet).
- **Weak soficity gives models.** Pick a weakly sofic approximation on a finite set
  containing `X`, `g_0` and the prefixes of all relators. For a finitely presented
  group, small multiplicative defect on that set bounds the relator lengths by a
  constant times the defect. Rescale the length so that `g_0` has length at least `1`.

## 1. Support type

**Lemma 1.1 (moved set).** Let `a in Sym(Omega)^X` and
`Omega_0 = union_x supp(a_x)`.
- Every word in the `a_x` fixes `Omega \ Omega_0` pointwise.
- `Omega_0` is invariant.
- `|Omega_0| <= sum_x |supp a_x|`.

*Proof.* A point fixed by every generator is fixed by every word. The complement of
an invariant set is invariant. The last item is the union bound.

**Lemma 1.2 (dichotomy).** If `G` is not sofic, there is `eps_0 > 0` such that every
finite `Omega` and every `a in Sym(Omega)^X` satisfy
`max_(r in R) |supp r(a)| >= eps_0 |Omega_0|`.

*Proof.* Suppose not. Then there are tuples `a^(n)` with `Omega_0^(n)` nonempty and
`max_r |supp r(a^(n))| < |Omega_0^(n)|/n`.
- **Restrict and normalize.** Restrict to `Omega_0^(n)`. This is allowed by Lemma 1.1,
  and it changes no support of any word. Use the normalized Hamming distance on
  `Sym(Omega_0^(n))`. Relator values then have distance `< 1/n` from `1`.
- **One generator stays far.** By Lemma 1.1 some generator `x_n` has
  `|supp a_(x_n)| >= |Omega_0^(n)|/|X|`. Passing to a subsequence, `x_n = x` is
  constant.
- **The homomorphism.** Along `omega` we get a homomorphism
  `psi : G -> prod_omega Sym(Omega_0^(n)) / N_omega`, with the normalized Hamming
  metric, and `psi(x) != 1`.
- **Contradiction.** Simplicity makes `psi` injective. A countable group embedding
  in a Hamming metric ultraproduct of finite symmetric groups is sofic (Elek--Szabo's
  characterization of soficity). This contradicts the hypothesis.

**Proof of Theorem item 1, forward direction, with the constant.** Let `G` be nonsofic
and `(H, Omega, f, a)` a support-type model with parameter `eps`.
- **Transfer.** The action gives permutations of `Omega`, and supports agree with
  those in `H`.
- **Setup.** Put `t = |supp g_0(a)| >= 1`. Then `t <= |Omega_0|`, so by Lemma 1.2 some
  relator satisfies `|supp r(a)| >= eps_0 t`. Being an integer, `|supp r(a)|` is at
  least `ceil(eps_0 t)`.
- **Estimate.** With `k = ceil(1/eps_0)` we have `k ceil(eps_0 t) >= t`. Monotonicity
  and subadditivity give
  ```text
  1 <= f(t) <= f(k ceil(eps_0 t)) <= k f(ceil(eps_0 t)) <= k f(|supp r(a)|) <= k eps.
  ```
- **Conclusion.** So `eps >= 1/k`, and models with smaller parameter do not exist.

**Converse.** A sofic group has permutation models with normalized Hamming defect
tending to `0` and `g_0` moving at least half the points. Take `f(s) = 2s/|Omega|`.

## 2. Rank type, any characteristic

Fix `a in GL(V)^X` over a field `F`. Put `M = max_x rk(a_x - 1)`,
`delta M = max_r rk(r(a) - 1)`, and `U = ∩_x ker(a_x - 1)`.

**Lemma 2.1 (moved quotient).** `U` is fixed pointwise by every word in the `a_x`, it is
invariant, and `dim V/U <= sum_x rk(a_x - 1) <= |X| M`.

*Proof.* Fixed by the generators and their inverses. The codimension of `ker(a_x - 1)` is
`rk(a_x - 1)`.

**Lemma 2.2 (almost abelian collapse).** `G` is perfect.
- **Constants.** Choose integers `c_(x,r)` with `e_x = sum_r c_(x,r) e_r` in `Z^X`, where
  `e_r` is the exponent-sum vector of `r`. Such `c_(x,r)` exist because `H_1(G) = 0`.
  Let `L` bound the relator lengths.
- **Statement.** If `rk_(V/U)(a_x - 1) <= eta M` for every `x`, then
  `M <= |R| (delta + 2 L eta) M + eta M`.

*Proof.*
- **Block form.** In a basis adapted to `U <= V`,
  `a_x - 1 = [[0, N_x], [0, D_x]]` with `rk D_x <= eta M`. Put
  `Nhat_x = [[0, N_x], [0, 0]]`. Then `a_x = 1 + Nhat_x + E_x` with `rk E_x <= eta M`.
- **Inverses.** `a_x^-1 = 1 - Nhat_x + E'_x`, and `rk E'_x <= 2 eta M`: the lower block is
  `-D_x(1 + D_x)^-1`, and the corner differs from `-N_x` by `N_x D_x (1+D_x)^-1`.
- **Words.** Always `Nhat_i Nhat_j = 0`. For a word `w` of length `L_w`, expand
  `prod_i (1 + Nhat_i + E_i)`. The difference from `prod_i (1 + Nhat_i) = 1 + sum_i Nhat_i`
  is `sum_i (prod_(j<i) (1 + Nhat_j + E_j)) E_i (prod_(j>i) (1 + Nhat_j))`, of rank at most
  `2 L_w eta M`. So `w(a) = 1 + sum_x e_(w,x) Nhat_x + E_w` with `rk E_w <= 2 L_w eta M`.
- **Perfection.** `Nhat_x = sum_r c_(x,r) (r(a) - 1 - E_r)`. Integer multiples do not raise
  rank, so `rk Nhat_x <= |R| (delta M + 2 L eta M)`.
- **Conclusion.** `rk(a_x - 1) <= rk Nhat_x + rk E_x`. Take the maximum over `x`.

**Lemma 2.3 (dichotomy).** If `G` is not `F`-linear sofic, there is `delta_0 > 0` such that every
tuple over `F` with `M > 0` has `delta >= delta_0`.

*Proof.* Suppose tuples `a^(n)` with `delta_n -> 0`. Put `eta = 1/(4 |R| L + 2)`.
- **Some generator stays moved.** For large `n`, `|R| delta_n < 1/4`, so Lemma 2.2 excludes
  its own hypothesis. Some `x_n` has `rk_(V/U)(a_(x_n) - 1) > eta M_n`. Pass to a subsequence
  with `x_n = x_0`.
- **Normalize.** On `Z_n = V_n / U_n`, `dim Z_n <= |X| M_n` (Lemma 2.1). So `a_(x_0)` has
  normalized rank at least `eta/|X|`. Relators have rank at most `delta_n M_n`, and
  `dim Z_n > eta M_n`, so their normalized rank is below `delta_n/eta -> 0`.
- **Ultraproduct.** Along `omega` this defines a nontrivial homomorphism from `G` into the
  rank metric ultraproduct of the `GL(Z_n)`. It is injective by simplicity. So `G` is
  `F`-linear sofic (ultraproduct form of Arzhantseva--Paunescu's definition,
  arXiv:1212.6780), a contradiction.

**Theorem item 2.**
- **The estimate.** Let `t = rk(rho(g_0(a)) - 1) >= 1`. Then `t <= |g_0| M`. By Lemma 2.3
  some relator has rank at least `delta_0 M >= delta_0 t / |g_0|`. With
  `k = ceil(|g_0| / delta_0)`, as in Section 1,
  `1 <= f(t) <= k f(rk(r(a) - 1)) <= k eps`.
- **Converse over finite `F`.** `F`-linear sofic models in `GL_n(F)` with normalized rank
  give `f(s) = 2s/n`.

**Item 4 (projective collapse).** Let `Ad : GL(V) -> GL(End V)`, `Ad(g)(A) = g A g^-1`. It is a
homomorphism, so `Ad(w(a)) = w(Ad(a))` for every word. Put `n = dim V` and `rho = rho(g)`.
- **Upper bound.** Write `g = lambda + B` with `rk B = rho`. Then
  `Ad(g)(A) - A = (B A - A B) g^-1`, and `A -> B A` and `A -> A B` each have rank `n rk B`. So
  `rk(Ad(g) - 1) <= 2 n rho`.
- **Lower bound.** `rk(Ad(g) - 1) = n^2 - dim C(g)`, where `C(g)` is the centralizer algebra (its
  dimension does not change under field extension).
  - *Jordan count.* Over an algebraic closure, `dim C(g) = sum_lambda sum_j (mu'_(lambda,j))^2`,
    with `mu'_lambda` the conjugate partition of the Jordan type at `lambda`. All parts sum to `n`,
    and the largest part at `lambda` is the geometric multiplicity `n - rk(g - lambda)`.
  - *Multiplicities.* For `lambda in F` this is at most `n - rho`. For `lambda` outside `F`, a Galois
    conjugate has the same multiplicity, so it is at most `n/2`.
  - *Result.* `dim C(g) <= n max(n - rho, n/2)`, hence `rk(Ad(g) - 1) >= n min(rho, n/2)`.
- **Conclusion.** Lemma 2.3 applied to the tuple `Ad(a)` over `F` gives
  ```text
  2 n max_r rho(r(a)) >= max_r rk(Ad(r(a)) - 1) >= delta_0 max_x rk(Ad(a_x) - 1)
                      >= delta_0 n min(max_x rho(a_x), n/2) .
  ```

## 3. Remark on an earlier version

An earlier version used the moved subspace `[P, V]` and needed `char F` coprime to `|P|`.
The moved quotient `V/U` has the dimension bound in every characteristic. Unipotent corners
`Hom(V/U, U)` are handled by Lemma 2.2, because a tuple that lives in the corner is almost
abelian.
