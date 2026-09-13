---
rg: 2
id: thompson-v-hyperlinear-iff-unitary-gluings-proof
kind: route
title: Amplify the trace, round both finite subgroups, align the two copies of a, pad to regular, and amplify back through simplicity
target: thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words
requires:
  - thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3
  - thompson-v-finitely-presented-infinite-simple
  - gowers-hatami-finite-group-hs-stability
---

Numbering follows the claim. `tr_d` is the normalized trace on `M_d`, `||x||_(2,d) = tr_d(x^* x)^(1/2)`,
and the index is dropped when clear. `|tr x - tr y| <= ||x - y||_2`, `||u x v||_2 = ||x||_2` for
unitaries, and `||x (x) y||_2 = ||x||_2 ||y||_2`. `V` is **hyperlinear** when it has an injective
homomorphism into the unitary group of a tracial ultraproduct `M = prod_omega (M_(k_n), tr_(k_n))`, as in
`thompson-v-hyperlinear`. By `thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`,
`G0 = S4 *_<a> S3` maps onto `V` with kernel `<<r5, ..., r8>>`, and `S4 = <a,b>`, `S3 = <a,c>` embed in
`V`. Fix words `w_h` in `a, b` (for `h in S4`) and in `a, c` (for `h in S3`), with `w_e` empty.

**L1 (models).** Unitaries `x_n` in `U(k_n)` for `x in {a,b,c}` define a homomorphism `V -> U(M)` exactly
when `lim_omega ||w(x_n) - I||_2 = 0` for every word `w` trivial in `V`. Every unitary of `M` lifts to
such a sequence: if `(y_n)` represents `u`, polar decomposition `y_n = u_n |y_n|` gives
`||y_n - u_n||_2 = || |y_n| - 1 ||_2 <= ||y_n^* y_n - 1||_2 -> 0`, since `|t - 1| <= |t^2 - 1|` for `t >= 0`.
Changing each generator by `o(1)` changes a word of length `l` by at most `l . o(1)`, so it changes
neither the homomorphism nor any trace limit.

**L2 (transport).** Let `J : C^k -> C^m` be an isometry, `p = J J^*`, and put `x' = J x J^* + (1 - p)`.
- Since `J^* J = 1` and `J^*(1 - p) = 0`, every word satisfies `w(x') = J w(x) J^* + (1 - p)`. So
  `||w(x') - I||_(2,m)^2 = (k/m) ||w(x) - I||_(2,k)^2` and `tr_m w(x') = (k/m) tr_k w(x) + (m - k)/m`.
- For a unitary `rho` in `U(m)`: `rho - x' = [p rho p - J x J^*] + p rho (1-p) + (1-p) rho p + (1-p)(rho - 1)(1-p)`.
  The first term has norm `(k/m)^(1/2) ||J^* rho J - x||_(2,k)`. Each other term has a factor `1 - p` of
  normalized trace `(m-k)/m` and operator norm at most `2`. So
  `||rho - x'||_(2,m) <= ||J^* rho J - x||_(2,k) + 4((m-k)/m)^(1/2)`.
- If `rho` is a representation on `C^k`, then `J rho J^* + (1 - p)` is a representation on `C^m`: `rho`
  on the range of `p`, trivial on its complement.

**L3 (two involutions).** Let `S, T` be self-adjoint unitaries in `M_m` whose `+1`-eigenspaces have
equal dimension. There is a unitary `Z` with `Z T Z^* = S` and `||Z - I||_2 <= ||S - T||_2 / sqrt 2`.
*Proof.* Put `P = (1+S)/2`, `Q = (1+T)/2`, `D = (P - Q)^2`. Expanding, `P D = D P = P - P Q P`, and
symmetrically for `Q`, so each eigenspace `E_lambda` of `D` (`0 <= lambda <= 1`) is invariant under `P`
and `Q`.
- On `E_0`, `P = Q`; let `Z = 1` there.
- On `E_1`, `P Q P = P - P D P = 0`, so `Q P = P Q = 0` and `P + Q = D = 1`. Equal ranks on the other
  pieces force `rank P = rank Q` on `E_1`. Let `Z` swap orthonormal bases of the two ranges. In each
  swapped plane `||Z - 1||_HS^2 = 4 = 2 ||P - Q||_HS^2`.
- On `E_lambda`, `0 < lambda < 1`, `P Q P = (1 - lambda) P`. For an orthonormal basis `x_i` of the
  range of `P`, the vectors `y_i = Q x_i / (1 - lambda)^(1/2)` are orthonormal, `<x_j, y_i> = 0` for
  `i != j`, and the planes `span{x_i, y_i}` are two-dimensional (otherwise `Q` would have the eigenvalue
  `(1 - lambda)^(1/2)`), invariant, and mutually orthogonal. Their orthogonal complement in `E_lambda`
  is invariant and meets the range of `P` trivially, so `P = 0` and `D = Q` there, which forces it to be
  `0`. In each plane `P, Q` are projections onto lines at angle `theta in (0, pi/2)`. Let `Z` be the
  rotation carrying the `Q`-line to the `P`-line. Then
  `||Z - 1||_HS^2 = 8 sin^2(theta/2) <= 4 sin^2(theta) = 2 ||P - Q||_HS^2`.
Summing, `||Z - I||_2^2 <= 2 ||P - Q||_2^2 = ||S - T||_2^2 / 2`. ∎

**`1 => 2`.** Let `U : V -> U(M)` be injective, and fix `epsilon in (0, 1/10]`.
- **Traces below one.** For a unitary `u`, `|tau(u)| = 1` forces `u = tau(u) 1`, because
  `||u - lambda 1||_2^2 = 2 - 2 Re(conj(lambda) tau(u))`. The elements with scalar image form a normal
  subgroup. If it were nontrivial it would be `V` (simplicity, `thompson-v-finitely-presented-infinite-simple`),
  so `U` would map `V` into the abelian group of scalars and hence be trivial, since a nonabelian simple
  group is perfect. So `|tau(U_h)| < 1` for the `28` nontrivial `h` in `S4 ∪ S3`.
- **Amplify.** Lift the generators to `sigma_n(x)` by L1, and put
  `sigma_n^(m)(x) = (sigma_n(x) (x) conj(sigma_n(x)))^((x) m)`. Tensor products and complex conjugation
  are multiplicative, so `w(sigma^(m)) = (w(sigma) (x) conj(w(sigma)))^((x) m)`. Then
  `||w(sigma^(m)) - I||_2 <= 2m ||w(sigma) - I||_2` (telescoping with `u (x) v - 1 = (u - 1)(x) v + 1 (x)(v - 1)`),
  and `tr w(sigma^(m)) = |tr w(sigma)|^(2m)`. Choose `m` with `|tau(U_h)|^(2m) <= epsilon/2` for all 28 `h`.
  By L1, `sigma^(m)` is a model of `V` in which `lim_omega tr w_h = |tau(U_h)|^(2m)`. Rename it `sigma_n`
  on `C^(k_n)`, with limit trace `tau` and `|tau(h)| <= epsilon/2`.
- **Round `S4`.** `f_n(h) = w_h(sigma_n)` has all-pairs defect
  `epsilon_n = max_(g,h) ||(w_g w_h w_(gh)^-1)(sigma_n) - I||_2 -> 0`, since these words are trivial in
  `V`. For `omega`-almost every `n`, `epsilon_n < 1/16`, and `gowers-hatami-finite-group-hs-stability`
  gives an isometry `J_n : C^(k_n) -> C^(m_n)` with `m_n <= k_n/(1 - 4 epsilon_n^2)`, a representation
  `rho_n` of `S4`, and `||f_n(h) - J_n^* rho_n(h) J_n||_2 <= 42 epsilon_n`. Transport all three
  generators by L2. The new model has the same trace limits, since `m_n/k_n -> 1`. Replacing `a, b` by
  `rho_n(a), rho_n(b)` moves them by `42 epsilon_n + 8 epsilon_n -> 0`. The result is a model
  `(A^1, B^1, C^1)` in which `(A^1, B^1)` is an exact `S4`-representation.
- **Round `S3`.** Apply the same step to `h -> w_h(A^1, C^1)` for `h in S3`. This gives `J'_n`, `m'_n`, and
  a representation `rho'_n` of `S3`. Transport by L2 to `(A^2, B^2, C^2)`. By the last item of L2,
  `(A^2, B^2)` is still an exact `S4`-representation, and `||rho'_n(h) - w_h(A^2, C^2)||_2 -> 0`.
- **Align the two copies of `a`.** Let `s = ||rho'_n(a) - A^2||_2 -> 0`. The `+1`-multiplicities of
  `rho'_n(a)` and `A^2` differ by `j <= m' s/2`. For `chi` the trivial or the sign character, the
  corresponding representation occurs in `rho'_n` with multiplicity
  `(m'/6)(1 + sum_(h != e) chi(h) tr rho'_n(h)) >= m'(1 - 5(epsilon/2 + o(1)))/6`, since
  `tr rho'_n(h) -> tau(h)`. This exceeds `j` for large `n`. Replace `j` trivial summands by sign summands (or conversely): `a`
  and `c` change on `j` dimensions, by `2 (j/m')^(1/2) -> 0`, and the multiplicities now agree. L3 gives
  `Z_n` with `||Z_n - I||_2 <= (s + 2(j/m')^(1/2))/sqrt 2 -> 0` conjugating the new `a`-image onto `A^2`.
  Let `rho''_n` be the conjugated representation.
- **Conclusion.** `(A, B, C) = (A^2, B^2, rho''_n(c))` has `(A, B)` an `S4`-representation and `(A, C)` an
  `S3`-representation. Since `C` is within `o(1)` of `C^2`, L1 gives `||r_i(A, B, C) - I||_2 -> 0` and
  `tr h(A, B, C) -> tau(h)` for `h in S4 ∪ S3`. Choose `n` in the `omega`-large set where these are below
  `epsilon` and `|tr h| <= epsilon`. ∎

**`2 => 3`.** Let `(A, B, C)` satisfy 2 with `epsilon` on `C^N`. Direct sums of copies change no trace
and no defect, so assume `N >= 96/epsilon`.
- **Multiplicities.** An irreducible `pi` of `S4` of degree `d_pi` occurs in `(A, B)` with multiplicity
  `m_pi = (N/24) sum_h conj(chi_pi(h)) tr h`, so `|m_pi - N d_pi/24| <= N d_pi epsilon`. For `S3` in
  `(A, C)`, `|m_pi - N d_pi/6| <= N d_pi epsilon`.
- **Pad.** Let `K = max(max_pi ceil(m_pi(S4)/d_pi), max_pi ceil(m_pi(S3)/(4 d_pi)))` and `D = 24K - N`, so
  `0 <= D <= 24 N epsilon + 24`. Let `pi_4 = sum_pi (K d_pi - m_pi) pi` over `Irr S4` and
  `pi_3 = sum_pi (4K d_pi - m_pi) pi` over `Irr S3`. Both have dimension `D`, and
  `(A, B) + pi_4 ~ K lambda_(S4)`, `(A, C) + pi_3 ~ 4K lambda_(S3)`.
- **Match `a`.** In both `K lambda_(S4)` and `4K lambda_(S3)`, `a` has `+1`-multiplicity `12K`. `A` is
  common, so `pi_4(a)` and `pi_3(a)` have the same spectrum. Conjugate `pi_3` by a unitary of `C^D` so
  that `pi_3(a) = pi_4(a)`.
- **Glue.** `(A + pi_4(a), B + pi_4(b), C + pi_3(c))` is a unitary free gluing of size `24K`, and
  `||r_i - I||_(2,24K)^2 <= ||r_i(A, B, C) - I||_2^2 + 4D/N <= epsilon^2 + 96 epsilon + 96/N <= epsilon^2 + 97 epsilon`.
  This tends to `0` with `epsilon`. ∎

**`3 <=> 4`.** A free `S4`-set of size `24k` has permutation representation `k lambda_(S4)`, and a free
`S3`-set of size `24k` gives `4k lambda_(S3)`. So `(A_0, B_0, W^* C_0 W)` with `W A_0 = A_0 W` is a gluing,
because `(A_0, W^* C_0 W) = W^*(A_0, C_0) W`. Conversely, given a gluing `(A, B, C)`:
- `(A, B) ~ (A_0, B_0)` gives a unitary `X` with `X A X^* = A_0` and `X B X^* = B_0`;
- `(A_0, X C X^*)` and `(A_0, C_0)` are equivalent representations of `S3`, so an intertwining unitary
  `Y` has `Y A_0 Y^* = A_0` and `X C X^* = Y^* C_0 Y`.
Conjugation preserves every `||r_i - I||_2`. ∎

**`4 => 1`.** Take `W_n` with defects `<= 1/n` on `C^(24 k_n)`, and put `M = prod_omega M_(24 k_n)`. By L1 and
the four-relator presentation, `a, b, c -> A_0, B_0, W_n^* C_0 W_n` define a homomorphism `U : V -> U(M)`:
the relators of `G0` hold exactly, and the `r_i` tend to `I`. `A_0` has trace `0`, so
`||U_a - 1||_2^2 = 2` and `U` is nontrivial. Its kernel is a proper normal subgroup, hence trivial by
simplicity. So `U` is injective and `V` is hyperlinear. ∎
