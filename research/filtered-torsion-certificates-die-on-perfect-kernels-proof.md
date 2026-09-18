---
rg: 2
id: filtered-torsion-certificates-die-on-perfect-kernels-proof
kind: route
title: Perfect relations double filtration depth coordinatewise, and idempotent relations are killed by Nakayama
target: filtered-torsion-certificates-die-on-perfect-kernels
requires:
  - mapping-torus-mf-radical-lies-in-finite-residual
  - steinberg-images-die-in-torsion-free-groups
artifacts:
  - experiments/pronilpotent-torsion-certificates-2026-09-17/filtration_depth_check.py
---

Throughout `[a,b] = a b a^-1 b^-1`. For a group `G` with separated filtration
`F^*`, the *depth* of `g` is `nu(g) = sup{m : g in F^m}`, a value in
`{1, 2, ..., infinity}`. Separation means `nu(g) = infinity` exactly when `g = 1`.
The requirements are used only in the consequences paragraph (Step 5).

**Step 0. The filtrations in the examples.**
- *Lower central series.* `[gamma_a, gamma_b] <= gamma_(a+b)` is the standard
  three-subgroup lemma induction, and separation is residual nilpotence.
- *Congruence.* For `X, Y` integral,
  `(1+q^a X)(1+q^b Y)(1+q^a X)^-1(1+q^b Y)^-1 - 1 = q^(a+b)(XY-YX)(1+q^a X)^-1(1+q^b Y)^-1`,
  and the inverses are integral. So `[Gamma(q^a), Gamma(q^b)] <= Gamma(q^(a+b))`,
  and `intersection_m Gamma(q^m) = 1`.
- *Radicals.* For an ideal `J <= Jac(S)`, `1 + J^m` is a group, because
  `(1+x)^-1 = 1 - x(1+x)^-1`. The commutator identity `aba^-1b^-1 - 1 = (ab-ba)a^-1b^-1`,
  with `ab - ba = xy - yx in J^(a+b)`, gives `[1+J^a, 1+J^b] <= 1+J^(a+b)`.

The script `filtration_depth_check.py` tests the congruence and superdiagonal
unipotent inclusions on random samples, including the sharp case
`[e_12(p^a), e_23(p^b)] = e_13(p^(a+b))`.

**Step 1. Proof of (PN1).**
1. Let `s_1, ..., s_k` generate `K`. Since `K` is perfect, each `s_i` lies in
   `[K,K]`. Choose finitely many words `u_ij, v_ij` in the `s^(+-1)` with
   `s_i = prod_(j <= m_i) [u_ij, v_ij]` in `K`.
2. Let `f: K -> prod_omega G_n` be a homomorphism, and choose coordinate lifts
   `g_(i,n) in G_n` of `f(s_i)`. The finitely many identities
   `g_(i,n) = prod_j [u_ij(g_n), v_ij(g_n)]` hold in `omega`-most coordinates `n`.
3. Fix such an `n`, and suppose some `g_(i,n) != 1`. Put
   `d = min_i nu(g_(i,n))`, which is finite and at least `1`. Every `u_ij(g_n)` and
   `v_ij(g_n)` lies in the subgroup `F_n^d`, so every commutator, and hence every
   `g_(i,n)`, lies in `F_n^(2d)`. So `d >= 2d`, which is impossible for
   `1 <= d < infinity`.
4. Hence `g_(i,n) = 1` for all `i` in `omega`-most `n`, so `f(s_i) = 1` and `f` is
   trivial.

Taking `G_n = G` constant and composing with the diagonal embedding
`G -> prod_omega G` gives the single-group statement. ∎

**Step 2. Proof of (PN2).**
1. Let `x_1, ..., x_k` generate `I`, and write `x` for the column vector. Every
   element of `I` is an integer combination of nonempty monomials in the `x_j`.
2. Since `I = I^2`, each `x_i` is a finite sum of products `y z` with `y, z in I`.
   Expanding `z` and splitting off the last letter of each monomial writes
   `y z = sum_j a_j x_j` with `a_j in I`. So `x = A x` for a matrix
   `A = P(x) in M_k(I)`, whose entries `P_ij` are noncommutative integer
   polynomials without constant term.
3. Choose lifts `X_n in S_n^k` of `phi(x)`. The finitely many identities
   `X_n = P(X_n) X_n` hold in `omega`-most `n`.

*Radical case, `J_n <= Jac(S_n)`.* The entries of `A_n = P(X_n)` lie in `J_n`,
because `P` has no constant term. So `A_n in M_k(J_n) = Jac(M_k(S_n))`, and
`1 - A_n` is invertible. From `(1 - A_n) X_n = 0` we get `X_n = 0`.

*Radical case, `intersection_m J_n^m = 0`.* If `X_n != 0`, let `d` be the least
depth of its entries with respect to the powers `J_n^m`, so `d >= 1`. Then
`A_n in M_k(J_n^d)` and `X_n = A_n X_n in J_n^(2d)`. This contradicts minimality,
so `X_n = 0`.

*Perturbative case.* Let `C` be the sum of the absolute values of all
coefficients of all `P_ij`, and put `delta = min(1, 1/(2kC))`. If every
`||X_(n,j)|| <= delta`, then each monomial of degree at least `1` has norm at most
`delta`. So `||P_ij(X_n)|| <= C delta`, and

```text
max_i ||X_(n,i)|| <= sum_j ||P_ij(X_n)|| ||X_(n,j)|| <= k C delta max_j ||X_(n,j)|| <= (1/2) max_j ||X_(n,j)||,
```

which forces `X_n = 0`. The same computation in a single Banach algebra gives
the one-algebra statement.

In every case `phi(x_i) = 0` for all `i`, so `phi = 0`. ∎

**Step 3. Proof of (PN3).**
1. `K` is perfect. Its abelianization is a finitely generated abelian group with
   no nontrivial finite quotient, so it is trivial.
2. There are finitely many groups of order at most `B`, so `omega`-most
   quotients `G_n/N_n` are isomorphic to one finite group `Q`, and
   `prod_omega G_n/N_n ~= Q`.
3. The composite `K -> prod_omega G_n -> Q` is trivial, because `K` has no
   nontrivial finite quotient. So `f(K)` lies in the kernel `prod_omega N_n`, and
   (PN1) gives `f = 1`. ∎

**Step 4. Ultraproducts of bi-ordered groups.** A bi-ordering is given by a
positive cone `P` with `P P <= P`, `G = P ⊔ P^-1 ⊔ {1}` and `g P g^-1 = P`. These
are first-order conditions, so the coordinatewise cone orders
`prod_omega G_n`. A finitely generated nontrivial subgroup of a bi-orderable
group has a `Z` quotient (local indicability), while a perfect group has none.

**Step 5. Consequences.** By `mapping-torus-mf-radical-lies-in-finite-residual`,
the root kernel `K` is finitely generated with no finite quotient, so it is
perfect, and Steps 1, 3 and 4 apply. By (STF3) of
`steinberg-images-die-in-torsion-free-groups`, the surviving relative elementary
gate has `I = I^2`, so Step 2 applies. A filtered certificate places the
generators of `K`, or of `I`, at depth at least `1` in `omega`-most coordinates.
Step 1 or Step 2 then makes the whole map trivial, and a trivial map certifies
nothing about a nontrivial `K`. ∎
