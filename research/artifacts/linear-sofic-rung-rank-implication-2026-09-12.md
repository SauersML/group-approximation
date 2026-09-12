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

## 3. Nonlinear rules do not run on rank models

Section 1 says the rung is about tuples and words only. The obvious way to use the rules anyway is the Gromov–Weiss
one: evaluate `mu` and `nu` coordinatewise on a model and count. On a Hamming model the coordinates are the points.
This section shows that on a rank model the coordinatewise structure is not stable under small rank errors.

Let `F` be a field, `D_n = F^n` with the coordinatewise product `v * w`, and `m: D_n ⊗ D_n -> D_n` the
multiplication. A rule with a product term, for example `mu(x_(m1), x_(m2)) = x_(m1) x_(m2)`, is evaluated on a model
through `m`. It commutes with the model's operator `a` only up to the *multiplicativity defect*

```text
E(a) = a ∘ m  -  m ∘ (a ⊗ a) :  D_n ⊗ D_n  ->  D_n ,      E(a)(e_i ⊗ e_j) = delta_ij a e_i - (a e_i) * (a e_j).
```

**Proposition 3.1.** Let `a` be in `GL_n(F)`.
- **(a)** `E(a) = 0` iff `a` is a permutation matrix.
- **(b)** `rk E(a) = dim span{ (a e_i) * (a e_j) - delta_ij a e_i : 1 <= i, j <= n }`.
- **(c)** Let `n >= 3` with `n + 1 != 0` in `F`, and `a = I + J`, `J` the all-ones matrix. Then `a` is invertible
  and `rk(a - I) = 1`, while `rk E(a) = n - 1` if `F` has characteristic two and `rk E(a) = n` otherwise.

*Proof.* **(b)** is the formula for `E(a)` on the basis `e_i ⊗ e_j`.

**(a).** `E(a) = 0` says `(a e_i) * (a e_i) = a e_i` and `(a e_i) * (a e_j) = 0` for `i != j`.
- The first makes every entry of the column `a e_i` idempotent in `F`, so `0` or `1`.
- The second makes the supports of distinct columns disjoint.
- Invertibility makes every column nonzero, so the `n` supports partition `{1, ..., n}` into `n` nonempty sets,
  hence singletons, and `a` is a permutation matrix.
- Conversely permutation matrices are algebra automorphisms of `D_n`.

**(c).** `det(I + J) = 1 + n != 0`, and `J` has rank one. The columns are `a e_i = e_i + 1`, where `1` is the
all-ones vector.
- For `i != j`: `(e_i + 1) * (e_j + 1) = e_i + e_j + 1`.
- For `i = j`: `(e_i + 1) * (e_i + 1) - (e_i + 1) = 2 e_i`.
- **Characteristic not two.** The vectors `2 e_i` span `D_n`, so `rk E(a) = n`.
- **Characteristic two.** Here `n` is even. Each `e_i + e_j + 1` has coordinate sum `n = 0`, so the span lies in
  the sum-zero hyperplane. For distinct `j, k` pick `i` outside `{j, k}` (as `n >= 3`); the difference of
  `e_i + e_j + 1` and `e_i + e_k + 1` is `e_j + e_k`, and these span the hyperplane. So `rk E(a) = n - 1`. QED

**Consequence 3.2 (interpretation, not a theorem).**
- **Discontinuity.** The permutation `I` has `E(I) = 0`. A perturbation of normalized rank `1/n` gives normalized
  defect at least `(n - 1)/n`. So the multiplicativity defect is not continuous in normalized rank. An argument that
  runs nonlinear rules on a rank model with small rank errors has no control of the evaluation.
- **Where evaluation works.** The rules run exactly on models whose generators preserve the coordinate algebra,
  that is, permutation-like generators. Those are the monomial and near-monomial tuples of Section 2, which reach
  only sofic groups.
- **So.** A proof of the rung for nonlinear automata must linearize on the group side before it touches models,
  as the recorded route does through stable formalizability and `linear-sofic-group-algebra-is-stably-finite`, or
  find a rank-visible invariant of the pair `(mu, nu)` that is not a coordinatewise evaluation.

## 4. The negation, a separating datum, and where the rung stops

**The negation.** `some-linear-sofic-group-is-not-surjunctive` is the open claim that some `F_p`-linear sofic group
is not surjunctive. By Theorem 1.2 it is a matrix statement: some strict datum `D` and prime `p` admit, for every
reverse word `w`, tuples over `F_p` with forward relators of normalized rank tending to `0` and `w` of normalized
rank bounded below. By Theorem 1.2 (b) ⇒ (c), such tuples assemble into a finitely generated `F_p`-linear sofic
group realizing `D`: the quotient `F(D)/N_lin(F_p)(D)`.

**Task 2 of this lane (a datum separating `N_lin` from `N_sof`).** A strict `D` with `W_r(D) ∩ N_lin(F_p)(D)`
empty, and so by Gromov–Weiss with `W_r(D) ∩ N_sof(D)` nonempty, makes `F(D)/N_lin(F_p)(D)` a finitely generated
group that is `F_p`-linear sofic, not surjunctive, and hence not sofic. So a separating datum answers the finite-field
form of Arzhantseva–Paunescu Question 8.5 (recorded over `C` as `linear-sofic-nonsofic-group`) and refutes
Gottschalk's conjecture in the same stroke. It is at least as hard as either. I did not find one.

**What a witness must be.**
- **Far from monomial.** By Remark 2.3, the witnessing tuples stay at rank distance at least `delta(eps)/4` from
  monomial tuples, generator by generator.
- **Invisible to counting.** By Proposition 3.1, the coordinatewise evaluation of the rules is not stable on such
  tuples. So the witness gives no configuration space on which to count, which is why Gromov–Weiss does not see it.
- **Linear-algebraically finite.** `F_p[K]` is stably finite, so every strict automaton on the witness group `K`
  is nonlinear, and over `p`-power alphabets none is formalizable after identity tracks.

**What a proof of the rung must use.**
- **The only recorded route.** `linear-sofic-surjunctivity-via-formalizability-and-ascent` uses nothing from linear
  soficity beyond stable finiteness of `F_p[G]`. It needs stable formalizability and alphabet ascent, both open.
- **What linear soficity adds.** A Sylvester rank function on `F_p[G]`, strictly more than stable finiteness. The
  per-datum form shows exactly what the rank function must control: word ranks, in all tuples, of words of length
  four, with no coordinatewise structure available. No argument on record uses the rank function past direct
  finiteness.
- **Linear control.** Remark 1.4 records a stronger quantitative form. The weakly sofic rung implies it with
  constant equal to the conjugacy width. Whether the rung implies it is open.

**Where this lane stops.** No proof of the rung for nonlinear automata. No separating datum. The landed results
place the rung between Gromov–Weiss (monomial tuples) and the weakly sofic rung (bounded conjugacy width), and they
explain why coordinatewise counting cannot be pushed from one to the other.
