# The linear sofic rung for nonlinear automata: a rank implication per strict datum

Lane `w4-linsofic-surj`, 2026-09-12. This artifact supports:
- `linear-sofic-surjunctivity-is-a-rank-implication-per-datum` (Section 1);
- `gromov-weiss-is-the-monomial-case-of-the-rank-implication` (Section 2);
- `site-pullbacks-are-discontinuous-in-the-rank-metric` (Section 3);
- the open claim `some-linear-sofic-group-is-not-surjunctive` and the Attempts entry on
  `linear-sofic-groups-are-surjunctive` (Section 4).

It continues `metric-ultraproduct-bounded-width-closure-2026-09-12.md` ([MU]) and uses the strict data and
Theorem of `surjunctivity-is-axiomatized-by-rectangle-clauses` ([RC]).

## 0. Conventions

**Strict data.** `D = (S, M, A, mu, nu, T_f, T_r)` is a strict datum as in [RC]. As in [MU] Section 0:
- `F(D)` is the free group on the symbols `x_a`, `a` in `S ⊔ M` other than the two labels `1`, with `x_1 = 1`;
- `R_f(D) = { x_s x_m x_m'^-1 x_s'^-1 : (s,m) T_f (s',m') }` are the forward relators;
- `W_r(D) = { x_m x_s x_s'^-1 x_m'^-1 : (m,s), (m',s') not T_r-related }` are the reverse words, a finite
  nonempty set.
- A homomorphism `lambda: F(D) -> K` *realizes* `D` when every forward relator is trivial and every reverse word
  is nontrivial at `lambda`. By [RC], `K` is not surjunctive iff some strict `D` is realized in `K`.

**Tuples.** For a field `F` and `n >= 1`, a *tuple of dimension n* is a homomorphism `rho: F(D) -> GL_n(F)`,
that is, a choice of invertible matrices `rho(x_a)`. Normalized rank is `rk(X)/n`.

**Rank length.** `g -> rk(g - 1)` is a conjugation-invariant length on `GL_n(F)`:
`rk(k g k^-1 - 1) = rk(g - 1)`, `rk(g^-1 - 1) = rk(g - 1)`, and `rk(gh - 1) <= rk(g - 1) + rk(h - 1)` because
`gh - 1 = g(h - 1) + (g - 1)`.

**Rank ultraproducts.** For dimensions `(n_k)` and a nonprincipal ultrafilter `omega`,
`Q = prod_omega GL_(n_k)(F) / N_omega` with `N_omega = { (a_k) : lim_omega rk(a_k - 1)/n_k = 0 }`. By the rank
length properties `N_omega` is a normal subgroup. A countable group is `F`-linear sofic iff it embeds in such a
`Q` (`sofic-implies-linear-sofic-over-every-field`). So every countable subgroup of every `Q` is `F`-linear sofic.

**The kernel.** `N_lin(F)(D)` is the reflection kernel of [MU] Proposition 2.5 for the class of `F`-linear sofic
groups, which is closed under subgroups, finite direct products and local embeddability.

## 1. The rung is a rank implication, datum by datum

**Lemma 1.1 (amplification).** Let `rho` be a tuple of dimension `n`.
- For `m >= 1`, the block-diagonal tuple `rho^(m)` of `m` copies of `rho` has dimension `nm` and
  `rk(rho^(m)(u) - 1) = m rk(rho(u) - 1)` for every word `u`.
- For tuples `rho_1, ..., rho_k` of one dimension `N`, the direct sum has dimension `kN` and
  `rk((rho_1 ⊕ ... ⊕ rho_k)(u) - 1) = sum_i rk(rho_i(u) - 1)`.
- Both constructions send monomial tuples to monomial tuples.

*Proof.* Words evaluate blockwise, and rank adds over direct sums. QED

**Theorem 1.2.** Let `F` be a field and `D` a strict datum. The following are equivalent.
- **(a)** `W_r(D) ∩ N_lin(F)(D)` is nonempty.
- **(b)** No `F`-linear sofic group realizes `D`.
- **(c)** There is `w` in `W_r(D)` such that for every `eps > 0` there is `delta > 0` with the following property:
  for every `n` and every tuple `rho: F(D) -> GL_n(F)`,

  ```text
  max over r in R_f(D) of rk(rho(r) - 1)  <=  delta n      implies      rk(rho(w) - 1)  <=  eps n.
  ```

*Proof.* **(a) ⇔ (b)** is [MU] Proposition 2.5 for the class of `F`-linear sofic groups.

**(c) ⇒ (b).** Let `K` be `F`-linear sofic and `lambda` realize `D` in `K`.
1. Compose `lambda` with an embedding `K -> Q = prod_omega GL_(n_k)(F) / N_omega`. An injective homomorphism
   keeps realization, so the composite `lambda'` realizes `D` in `Q`.
2. Lift each `lambda'(x_a)` to a sequence `(a_k)` and let `rho_k` be the tuple `x_a -> a_k`. For every word `u` the
   class of `(rho_k(u))_k` is `lambda'(u)`.
3. Forward relators are trivial in `Q`, so `lim_omega rk(rho_k(r) - 1)/n_k = 0` for every `r` in `R_f(D)`. The
   reverse word `w` of (c) is nontrivial, so `c = lim_omega rk(rho_k(w) - 1)/n_k > 0`.
4. Take `eps = c/2` and its `delta`. For `omega`-almost every `k` all forward relators have rank at most
   `delta n_k`, so `rk(rho_k(w) - 1) <= eps n_k`, and the limit is at most `c/2`. Contradiction.

**(b) ⇒ (c).** Suppose (c) fails. Then for every `w` in `W_r(D)` there is `eps_w > 0` such that for every
`delta > 0` some tuple `rho` of some dimension `n` has all forward relators of rank at most `delta n` and
`rk(rho(w) - 1) > eps_w n`.
1. For `j >= 1` pick such tuples `rho_(w,j)` with `delta = 1/j`, of dimensions `n_(w,j)`. Put
   `N_j = prod_w n_(w,j)` and `sigma_j = ⊕_w rho_(w,j)^(N_j / n_(w,j))`, of dimension `|W_r| N_j`.
2. By Lemma 1.1, every forward relator has normalized rank at most `1/j` under `sigma_j`, and every `w'` in
   `W_r(D)` has normalized rank greater than `eps_(w') / |W_r|`.
3. In `Q = prod_omega GL_(|W_r| N_j)(F) / N_omega` put `lambda(x_a) = [(sigma_j(x_a))_j]`. Forward relators lie in
   `N_omega`, and no reverse word does. So `lambda` realizes `D`, and `lambda(F(D))` is a countable subgroup of
   `Q`, hence `F`-linear sofic. So (b) fails. QED

**Corollary 1.3.** Every `F_p`-linear sofic group is surjunctive iff (c) holds over `F_p` for every strict `D`.
So `linear-sofic-groups-are-surjunctive` is the statement that (c) holds over every prime field for every strict
datum. The proof uses no property of `mu` and `nu` beyond strictness: the rung is a statement about matrix tuples
and group words only.

*Proof.* Combine Theorem 1.2 with [RC] and [MU] Proposition 2.5. QED

**Remark 1.4 (linear control and the neighbouring rungs).**
- **Linear control.** Call `D` *linearly controlled over F* when some `w` in `W_r(D)` and `C > 0` satisfy
  `rk(rho(w) - 1) <= C max_r rk(rho(r) - 1)` for every tuple. This implies (c) with `delta = eps / C`.
- **The weak sofic rung gives linear control.** If one `w` lies in `cl(Cons_n^F(R_f(D)))` ([MU] Theorem 1.1(b)),
  then for every tuple over a finite field the finite group `rho(F(D))` puts `w(rho)` in
  `Cons_n(R_f(rho))`, and the rank length gives `C = n`. This is the inclusion `N_ws ⊆ N_lin` seen in matrices.
- **The converse is not automatic.** Adding trivial blocks lowers normalized defects, so a tuple whose forward
  relators and reverse words both have rank `o(n)`, with the reverse word much larger, cannot be amplified into a
  realization. Whether (c) implies linear control is open.

## 2. Gromov–Weiss is the monomial case

Let `F` be a finite field and `Mon_n(F) <= GL_n(F)` the monomial matrices. A *monomial tuple* takes values in
`Mon_n(F)`.

**Theorem 2.1.** For every strict datum `D` there is `w` in `W_r(D)` such that for every `eps > 0` there is
`delta > 0` with: every monomial tuple `rho: F(D) -> Mon_n(F)` whose forward relators all have rank at most
`delta n` has `rk(rho(w) - 1) <= eps n`.

*Proof.* Suppose not. Run the proof of Theorem 1.2, (b) ⇒ (c), with monomial failing tuples. By Lemma 1.1 the
amplified direct sums `sigma_j` are monomial, so `lambda` realizes `D` in
`Q_mon = prod_omega Mon_(N'_j)(F) / (N_omega ∩ prod Mon)`, where `N'_j = |W_r| N_j`.

By `monomial-rank-models-are-hamming-models`, the faithful action `j` of `Mon_N(F)` on
`X_N = F^x × {1, ..., N}` satisfies `(1/2) d_H(j(A), j(B)) <= rk(A - B)/N <= d_H(j(A), j(B))`.
- So a sequence has normalized rank distance tending to `0` along `omega` iff its image has Hamming distance
  tending to `0`.
- Hence `j` induces an injective homomorphism from `Q_mon` into the Hamming ultraproduct
  `prod_omega Sym(X_(N'_j)) / N^H_omega`.
- Countable subgroups of Hamming ultraproducts of finite symmetric groups are sofic.

So `lambda(F(D))` is a sofic group realizing `D`. By [RC] it is not surjunctive, contradicting
`sofic-groups-are-surjunctive`. QED

**Corollary 2.2 (what the rung adds).** Over `F_p`, every `F_p`-linear sofic group is surjunctive iff for every
strict `D` the implication of Theorem 2.1, which holds on monomial tuples for some reverse word, holds on all
invertible tuples for some possibly different reverse word. Over `F_2` the monomial tuples are the permutation
tuples.

**Remark 2.3 (near-monomial tuples add nothing).** Let `rho` and `rho'` be tuples with
`rk(rho(x_a) - rho'(x_a)) <= theta n` for every generator, and `rho'` monomial.
- For a word `u` of length `|u|`, telescoping gives `rk(rho(u) - rho'(u)) <= |u| theta n`.
- So forward relator and reverse word ranks move by at most `L theta n`, with `L` the longest relator or word.
- Theorem 2.1 therefore transfers to tuples within rank `theta n` of monomial ones, with `delta` and `eps` shifted
  by `4 theta` (every relator and reverse word of a strict datum has length at most `4`).

The transfer needs `4 theta < delta(eps)`. So a tuple that witnesses failure of the rung must stay far from every
monomial tuple, generator by generator. Unipotent tuples are the natural far-from-monomial family. For instance the
upper-unitriangular model of `U_4(R)` in `unipotent-frame-relations-cannot-assemble-corner-cuntz-family` carries a
nonzero two-root defect while satisfying every relation of the rank-four frame.
