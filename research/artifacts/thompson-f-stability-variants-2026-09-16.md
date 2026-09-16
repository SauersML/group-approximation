# Stability variants for Thompson's F: weak, local and flexible (2026-09-16)

Supports `thompson-f-weak-and-flexible-stability-are-nonsoficity` through the route
`thompson-f-weak-and-flexible-stability-are-nonsoficity-proof`. The only imported mathematics is
direction `1 => 2` of `thompson-f-sofic-iff-relator-system-unstable` (in the repo) and the structure of
normal subgroups of `F` (Cannon--Floyd--Parry). Everything else is proved here.

## 0. Sources, read from the arXiv TeX sources on 2026-09-16

- **[AP]** G. Arzhantseva, L. Păunescu, *Almost commuting permutations are near commuting permutations*,
  arXiv:1410.2626v2. Source file `Arzhantseva_Paunescu_JFA_revised.tex`, fetched from
  `arxiv.org/e-print/1410.2626v2`. Every theorem-like environment shares one counter per section, and
  the numbers below are computed from the source.
  - Theorem 1.1: an amenable group has weakly stable relators iff it is residually finite.
  - Conjecture 1.2: "A group G is stable whenever every quotient G/N is weakly stable."
  - Open problem, unnumbered, Introduction: "Is the system of two words [ab^-1, a^-1ba] and
    [ab^-1, a^-2ba^2] (weakly) stable in permutations?"
  - Definition 3.2 (stable). Definition 7.1 (weakly stable).
  - Theorem 7.2: (i) weakly stable iff every sofic representation is perfect; (ii) sofic with weakly
    stable relators implies residually finite; (iii) the amenable case.
  - The last sentence of Definition 7.1 reads "is called weakly stable if its set of relator words R is
    stable". From context this is a typo for "weakly stable".
- **[BL]** O. Becker, A. Lubotzky, *Group stability and Property (T)*, arXiv:1809.00632. Source
  `stab-t.tex` from `arxiv.org/src/1809.00632`; arXiv API "updated" 2019-02-22.
  - Definition 1.1: stability challenges, solutions, `G`-stability.
  - §4.4 "A flexible variant of P-stability": `d^flex`, `d^veryflex`, flexible solutions, and the
    remark that a non-residually-finite `P`-flexibly (or very flexibly) stable group is nonsofic.
- **[Br]** H. Bradford, *Local permutation stability*, arXiv:2211.15249v2. Source
  `Local_Permutation_Stability__Accepted_Version_for_GGD_.tex`, dated 2024-09-04.
  - Definitions 1.1--1.3: almost-homomorphism, partial homomorphism, separating, sofic, (weakly) locally
    stable. The source of Definition 1.3 writes `psi_n : Gamma -> Sym(n)`; the comparison
    `d_(k_n)(phi_n(g), psi_n(g))` and Remark 1.4 show that `Sym(k_n)` is meant, and that is used here.
  - Remark 1.4 (stable, weakly stable). Remark 1.5 (the square of implications).
  - Lemma 2.14: for finitely presented groups, (weakly) locally stable implies (weakly) stable.
  - Lemma 2.15: sofic and weakly locally stable implies LEF.
  - Theorem 2.16: quotes [AP] Theorem 7.2(iii).
- **[CFP]** J. W. Cannon, W. J. Floyd, W. R. Parry, *Introductory notes on Richard Thompson's groups*,
  Enseign. Math. 42 (1996). Theorem 4.3: every nontrivial normal subgroup of `F` contains `F'`. This is
  standard and already used on main as Fact 1.1 of
  `research/artifacts/thompson-f-soficity-as-relator-stability-2026-09-12.md`. Not re-fetched.

## 1. Setup

- **Group.** `F_2` is free on `S = {a, b}`, and `pi : F_2 -> F` is the quotient with kernel
  `<<R>>`, where `R = {R_1, R_2}`, `R_1 = [ab^-1, a^-1ba]` and `R_2 = [ab^-1, a^-2ba^2]`, with
  `[u,v] = u v u^-1 v^-1`.
  - As reduced words, `R_1 = a b^-1 a^-1 b a b a^-2 b^-1 a` has length 10.
  - `R_2 = a b^-1 a^-2 b a^2 b a^-3 b^-1 a^2` has length 14.
  - `c = [a,b]` has length 4, and `c` is not in `<<R>>` because `F` is not abelian.
- **Evaluation.** `l(xi)` is reduced word length. For `p = (p_a, p_b)` in `Sym(n)^2`, `xi(p)` is the
  evaluation of `xi`.
- **Hamming distance.** `d(sigma, tau) = |{x : sigma x != tau x}| / n`. It is bi-invariant, so:
  - `d(sigma sigma', tau tau') <= d(sigma, tau) + d(sigma', tau')`;
  - `d(sigma^-1, tau^-1) = d(sigma, tau)`;
  - `d(xi(p), xi(q)) <= l(xi) max_s d(p_s, q_s)`.
- **Flexible distances [BL §4.4].** For `sigma` in `Sym(n)`, `tau` in `Sym(m)`, `m >= n`, with `[n]`
  a subset of `[m]`:
  - `d^vf_n(sigma, tau) = |{x in [n] : sigma x != tau x}| / n`;
  - `d^flex_n(sigma, tau) = d^vf_n(sigma, tau) + (m - n)/n`.

  Both equal `d` when `m = n`.

**Fact 1.1.** Every homomorphism from `F` to a finite group has abelian image. Hence a pair in
`Sym(n)^2` solves `R` iff it commutes. Every homomorphism `F -> Sym(t)` sends `a`, `b` to commuting
permutations.

*Proof.* The kernel has finite index in the infinite group `F`, so it is nontrivial and contains `F'` by
[CFP, Theorem 4.3]. Conversely, if `p_a` and `p_b` commute, every word in them depends only on its
exponent sums, and `R_1`, `R_2` have exponent sums zero. `QED`

## 2. The commutator transfer inequality

**Lemma 2.1.** Let `A, B` be in `Sym(n)` and `A', B'` in `Sym(t)` with `t >= n` and `[n]` a subset of
`[t]`. Put `E_A = {x in [n] : Ax != A'x}`, and define `E_B` likewise. Then

`|{x in [n] : [A,B]x != [A',B']x}| <= 2(|E_A| + |E_B|)`.

*Proof.* `[A,B] = A B A^-1 B^-1`, acting as `x -> A(B(A^-1(B^-1 x)))`.
- **The path.** For `x` in `[n]` put `x_1 = B^-1 x`, `x_2 = A^-1 x_1`, `x_3 = B x_2`, `x_4 = A x_3`.
  All of these lie in `[n]`, since `A` and `B` permute `[n]`, and `x_4 = [A,B]x`.
- **When the path agrees.** Suppose all four of the following hold: `B'^-1 x = x_1`,
  `A'^-1 x_1 = x_2`, `B' x_2 = x_3`, `A' x_3 = x_4`. Then `[A',B']x = x_4`.
- **Step 1** holds iff `B' x_1 = x = B x_1`, i.e. iff `x_1` is not in `E_B`. The map `x -> x_1` is a
  bijection of `[n]`, so at most `|E_B|` points fail step 1.
- **Step 2** holds iff `A' x_2 = x_1 = A x_2`, i.e. iff `x_2` is not in `E_A`. The map `x -> x_2` is a
  bijection, so at most `|E_A|` points fail.
- **Step 3** holds iff `x_2` is not in `E_B`: at most `|E_B|` failures.
- **Step 4** holds iff `x_3` is not in `E_A`: at most `|E_A|` failures.

The points where the commutators differ are among the failures, which gives the bound. `QED`

**Sharpness.** `experiments/thompson-f-stability-variants-2026-09-16/transfer_check.py` checks the
inequality over all `A, B` in `Sym(n)` and all `A', B'` in `Sym(t)` for
`(n,t) in {(2,2),(2,3),(2,4),(3,3),(3,4),(3,5),(4,4)}`, plus 20000 random near-extensions with
`n <= 60`. It found no violation, and equality `2(|E_A|+|E_B|)` occurs for `(2,3), (2,4), (3,4), (3,5)`
and `(4,4)` (output in `transfer_check.out`). The constant 2 in the lemma cannot be lowered. The proof
does not depend on the script.

An explicit equality case, checkable by hand, has `n = t = 4`, points `{0,1,2,3}`, `A = (2 3)`,
`B = (0 2)(1 3)`, `A' = id` and `B' = B`.
- `A'` and `B'` commute, `|E_A| = 2` and `|E_B| = 0`.
- `A` and `B` generate a dihedral group of order 8, and `[A,B] = (0 1)(2 3)`. It moves all 4 points,
  which is `2(|E_A| + |E_B|)`.
- Taking `k` disjoint copies gives pairs with `d([A,B], id) = 1` and commuting corrections of total error
  `1/2`. So the bound `1/2` in Corollary 2.2 is attained for general pairs. Whether it is attained on
  sofic approximations of `F` is not addressed.

**Corollary 2.2.** Let `(A_k, B_k)` be in `Sym(n_k)^2` with `d([A_k,B_k], id) -> 1`. Let
`(A'_k, B'_k)` be commuting pairs in `Sym(t_k)^2`, `t_k >= n_k`. Then

`liminf_k ( d^vf_(n_k)(A_k, A'_k) + d^vf_(n_k)(B_k, B'_k) ) >= 1/2`.

*Proof.* Since `[A'_k, B'_k] = id`, Lemma 2.1 gives
`d([A_k,B_k], id) <= 2 (d^vf(A_k,A'_k) + d^vf(B_k,B'_k))`. If the liminf were `L < 1/2`, then along a
subsequence the left side tends to 1 and the right side to `2L < 1`. `QED`

## 3. Approximations of F

Following [Br, Definitions 1.1--1.2]:
- an *almost-homomorphism* is `phi_n : F -> Sym(k_n)` with `d(phi_n(gh), phi_n(g)phi_n(h)) -> 0` for all
  `g, h`;
- it is *separating* if `d(phi_n(g), id) -> 1` for every `g != e`;
- `F` is *sofic* iff it has a separating almost-homomorphism;
- a *partial homomorphism* satisfies `phi_n(gh) = phi_n(g)phi_n(h)` for all `n >= N(g,h)`.

Following [BL]:
- a *stability challenge* is `f_k : S -> Sym(n_k)` with `d(xi(f_k), id) -> 0` for every `xi` in
  `<<R>>`;
- it is a *sofic approximation* if moreover `d(xi(f_k), id) -> 1` for every `xi` not in `<<R>>`.

Following [AP, Definition 7.1], `p` in `Sym(n)^2` is a *`delta`-strong solution* if, for every `xi` with
`l(xi) < 1/delta`, `d(xi(p), id) < delta` when `xi` is in `<<R>>` and `> 1 - delta` otherwise.

**Monotonicity.** If `delta' <= delta`, a `delta'`-strong solution is `delta`-strong. There are fewer
words to test, and the thresholds are weaker.

**Lemma 3.1.**
- **(a)** If `phi_n` is an almost-homomorphism and `f_n = phi_n|_S`, then
  `d(xi(f_n), phi_n(pi xi)) -> 0` for every `xi` in `F_2`. In particular `f_n` is a stability
  challenge.
- **(b)** If `phi_n` is separating, then `f_n` is a sofic approximation. For every `delta > 0`, `f_n` is a
  `delta`-strong solution for all large `n`. Moreover `d([phi_n(a), phi_n(b)], id) -> 1`.
- **(c)** If `delta`-strong solutions exist for every `delta > 0`, then `F` is sofic.

*Proof.*
- **(a), the identity.** From `d(phi_n(e)phi_n(e), phi_n(e)) -> 0` and left invariance,
  `d(phi_n(e), id) -> 0`.
- **(a), inverses.** From `d(phi_n(g)phi_n(g^-1), phi_n(e)) -> 0` we get
  `d(phi_n(g^-1), phi_n(g)^-1) -> 0`.
- **(a), induction on `l(xi)`.** The empty word is handled by the identity case. For `xi = xi' s` with
  `s` a letter:

  `d(xi(f_n), phi_n(pi xi)) <= d(xi'(f_n), phi_n(pi xi')) + d(s(f_n), phi_n(pi s)) + d(phi_n(pi xi')phi_n(pi s), phi_n(pi xi))`.

  The first term tends to 0 by induction. The second is 0 for `s` in `S`, and tends to 0 by the inverse
  case for `s` in `S^-1`. The third tends to 0 by the almost-homomorphism property. For `xi` in `<<R>>`,
  `d(xi(f_n), id) <= d(xi(f_n), phi_n(e)) + d(phi_n(e), id) -> 0`.
- **(b).** For `xi` not in `<<R>>`, `d(xi(f_n), id) >= d(phi_n(pi xi), id) - o(1) -> 1`. Only finitely
  many words have `l(xi) < 1/delta`, which gives the `delta`-strong statement. The last assertion is
  the case `xi = c`.
- **(c).** Let `p^(k)` be a `(1/k)`-strong solution on `n_k` points, fix words `w_g` with
  `pi(w_g) = g`, and put `phi_k(g) = w_g(p^(k))`.
  - By bi-invariance, `d(phi_k(gh), phi_k(g)phi_k(h)) = d((w_g w_h w_(gh)^-1)(p^(k)), id)`. The word
    `w_g w_h w_(gh)^-1` lies in `<<R>>` and has fixed length, so this is `< 1/k` for large `k`.
  - For `g != e`, `w_g` is not in `<<R>>`, so `d(phi_k(g), id) > 1 - 1/k` for large `k`.

  So `phi_k` is a separating almost-homomorphism. `QED`

**Lemma 3.2.** If `psi_n : F -> Sym(k_n)` is a partial homomorphism, then `(psi_n(a), psi_n(b))` solves
`R` for all large `n`. In particular the pair commutes.

*Proof.*
- **Identity and inverses.** For large `n`, `psi_n(e) = psi_n(e)^2`, so `psi_n(e) = id`. Then
  `psi_n(a)psi_n(a^-1) = id`, and likewise for `b`.
- **Words.** Write `R_j = s_1 ... s_L`. Finitely many instances of the partial homomorphism property
  give `psi_n(pi(s_1...s_i)) = psi_n(pi(s_1...s_(i-1))) psi_n(pi s_i)` for all `i`, for large `n`. Hence
  `R_j(psi_n(a), psi_n(b)) = psi_n(pi R_j) = psi_n(e) = id`.
- **Commuting.** Fact 1.1. `QED`

(This is the argument of [Br, Lemma 2.14], restricted to the two relators.)

## 4. The theorem

**Theorem 4.1.** The following are equivalent.
1. `F` is not sofic.
2. `R` is stable in permutations [AP, Definition 3.2]: for every `epsilon > 0` there is `delta > 0` such
   that every `p` in `Sym(n)^2` with `max_j d(R_j(p), id) < delta` has a solution `p~` with
   `d(p_s, p~_s) < epsilon` for `s = a, b`.
3. `R` is weakly stable in permutations [AP, Definition 7.1]: the same, for `delta`-strong solutions only.
4. Bradford's four senses [Br, Definition 1.3, Remark 1.4]:
   - (a) stable: every almost-homomorphism `phi_n : F -> Sym(k_n)` has homomorphisms
     `psi_n : F -> Sym(k_n)` with `d(phi_n(g), psi_n(g)) -> 0` for all `g`;
   - (b) weakly stable: the same, for separating `phi_n`;
   - (c) locally stable: as (a), with `psi_n` partial homomorphisms;
   - (d) weakly locally stable: as (b), with `psi_n` partial homomorphisms.
5. Becker--Lubotzky's three senses:
   - (a) `P`-stable [BL, Definition 1.1]: every challenge `f_k` has homomorphisms `g_k : F -> Sym(n_k)`
     with `sum_s d(f_k(s), g_k(s)) -> 0`;
   - (b) `P`-flexibly stable [BL, §4.4]: every challenge has homomorphisms `g_k : F -> Sym(t_k)`,
     `t_k >= n_k`, with `d^flex_(n_k)(f_k(s), g_k(s)) -> 0` for each `s`;
   - (c) `P`-very-flexibly stable: as (b), with `d^vf`.
6. For every sofic approximation `f_k : S -> Sym(n_k)` of `F` there are homomorphisms
   `g_k : F -> Sym(t_k)`, `t_k >= n_k`, with `liminf_k sum_s d^vf_(n_k)(f_k(s), g_k(s)) < 1/2`.

### Proof

**(A) Definitional implications.**
- `4a => 4b => 4d` and `4a => 4c => 4d`, because homomorphisms are partial homomorphisms and separating
  almost-homomorphisms are almost-homomorphisms [Br, Remark 1.5].
- `5a => 5b => 5c`: a solution is a flexible solution with `t_k = n_k`, and `d^vf <= d^flex`.
- `5c => 6`: a sofic approximation is a challenge, and a limit 0 has liminf `< 1/2`.

**(B) `1 => 2`.** This is `thompson-f-sofic-iff-relator-system-unstable`, direction `1 => 2`.

**(C) `2 => 3`.** Given `epsilon`, let `delta` be as in 2 and put `delta' = min(delta, 1/15)`. A
`delta'`-strong solution has `d(R_j(p), id) < delta'` for `j = 1, 2`, because `R_j` lies in `<<R>>` and
has length `<= 14 < 1/delta'`. So it is a `delta`-solution, and 2 corrects it.

**(D) `2 => 5a`.** Let `f_k` be a challenge on `n_k` points.
- **Choosing the precision.** Put `delta_k = max_j d(R_j(f_k), id)`, so `delta_k -> 0`. For
  `m = 1, 2, ...` fix `delta(1/m)` as in 2. Let `m_k` be the largest `m <= k` with
  `delta_k < delta(1/m)`, or `m_k = 0` if there is none. For each `M`, all large `k` have
  `delta_k < delta(1/M)`, so `m_k >= M`. Hence `m_k -> infinity`.
- **Correcting.** When `m_k >= 1`, statement 2 gives a solution `p~^(k)` with
  `d(f_k(s), p~^(k)_s) < 1/m_k`. It defines a homomorphism `g_k : F -> Sym(n_k)` with
  `g_k(s) = p~^(k)_s`. When `m_k = 0`, let `g_k` be trivial.
- **Conclusion.** `sum_s d(f_k(s), g_k(s)) < 2/m_k -> 0`.

**(E) `2 => 4a`.** Let `phi_n` be an almost-homomorphism and `f_n = phi_n|_S`.
- **A solution on the generators.** By Lemma 3.1(a), `f_n` is a challenge. By (D) there are homomorphisms
  `psi_n : F -> Sym(k_n)` with `d(phi_n(s), psi_n(s)) -> 0` for `s` in `S`.
- **All group elements.** For `g` in `F` fix a word `w_g`. Then

  `d(phi_n(g), psi_n(g)) <= d(phi_n(g), w_g(f_n)) + d(w_g(f_n), w_g(psi_n(a), psi_n(b))) <= o(1) + l(w_g) max_s d(f_n(s), psi_n(s)) -> 0`.

  The first term is Lemma 3.1(a). The second uses bi-invariance and `psi_n(g) = w_g(psi_n(a), psi_n(b))`.

Together with (A), statements 2 through 6 all follow from 1.

**(F) `6 => 1`.** Suppose `F` is sofic.
- **Setup.** Let `f_k` be a sofic approximation. It exists by Lemma 3.1(b), and
  `d([f_k(a), f_k(b)], id) -> 1` because `c` is not in `<<R>>`.
- **Any correction commutes.** For homomorphisms `g_k : F -> Sym(t_k)` with `t_k >= n_k`, the pairs
  `(g_k(a), g_k(b))` commute by Fact 1.1.
- **Conclusion.** Corollary 2.2 gives `liminf_k sum_s d^vf(f_k(s), g_k(s)) >= 1/2`, so 6 fails.

By (A), this gives `5a, 5b, 5c => 1`.

**(G) `4d => 1`.** Suppose `F` is sofic.
- **Setup.** Let `phi_n` be a separating almost-homomorphism. Suppose `psi_n` are partial homomorphisms
  with `d(phi_n(g), psi_n(g)) -> 0` for every `g`.
- **Commuting corrections.** By Lemma 3.2, `(psi_n(a), psi_n(b))` commutes for large `n`.
- **Contradiction.** By Lemma 3.1(b), `d([phi_n(a), phi_n(b)], id) -> 1`. Lemma 2.1 with `t = k_n` gives
  `d([phi_n(a), phi_n(b)], id) <= 2(d(phi_n(a), psi_n(a)) + d(phi_n(b), psi_n(b))) -> 0`.

So 4d fails. By (A), this gives `4a, 4b, 4c => 1`.

**(H) `3 => 1`, with explicit constants.** Suppose `F` is sofic. Fix any `epsilon < 1/4`, and let
`delta > 0` be arbitrary.
- **A strong solution far from commuting.** Put `delta' = min(delta, 1/5, 1 - 4 epsilon)`. By Lemma
  3.1(b) some `p` in `Sym(n)^2` is a `delta'`-strong solution, hence a `delta`-strong solution. Since
  `l(c) = 4 < 1/delta'` and `c` is not in `<<R>>`, `d([p_a, p_b], id) > 1 - delta' >= 4 epsilon`.
- **No close solution.** If a solution `p~` had `d(p_s, p~_s) < epsilon` for both `s`, it would commute
  (Fact 1.1). Lemma 2.1 with `t = n` would give `d([p_a,p_b], id) < 4 epsilon`, a contradiction.

So no `delta` works for this `epsilon`, and 3 fails.

**(I) Unconditional part.**
- `1 => 3`: by Lemma 3.1(c) and monotonicity, under 1 there is `delta_0` such that no `delta`-strong
  solution exists for `delta <= delta_0`, so 3 holds vacuously.
- `1 => 6`: under 1 there is no sofic approximation.
- `1 => 4b`, `1 => 4d`: under 1 there is no separating almost-homomorphism.

With (F), (G), (H), this shows that 1, 3, 4b, 4d and 6 are equivalent without (B). Only the strict,
local and flexible senses 2, 4a, 4c, 5a, 5b, 5c need (B). `QED`

## 5. Consequences and scope

- **Both readings of the Open problem.** [AP] ask whether `R` is "(weakly) stable". Reading 2 is the
  root `thompson-f-relator-system-stable-in-permutations`, and reading 3 is equivalent to it. The root's
  remark that the weak variant "is not recorded here" is thereby discharged: it is the same question.
- **What [AP] could already conclude.** After the Open problem, [AP] say that an affirmative answer
  gives nonamenability of `F` (weak reading, via their Theorem 1.1) and nonsoficity (strict reading).
  Their Theorem 7.2(ii), with the fact that `F` is not residually finite, already gives nonsoficity
  from the weak reading. (H) is that argument with constants.
- **Explicit failure if `F` is sofic.**
  - Weak stability fails at every `epsilon < 1/4`.
  - [BL]'s liminf condition (§4.4, "smaller than some small enough constant depending on |S| and on the
    length of the shortest word exhibiting the non-residual-finiteness") needs only the constant `1/2`
    for `F` with `S = {a, b}` and `c = [a,b]`.
- **[AP] Conjecture 1.2 holds for `G = F`.** The hypothesis "every quotient `F/N` is weakly stable"
  includes `N = 1`. Then `3 => 1 => 2` gives stability. For `N != 1` the quotient is abelian by [CFP].
  Finitely generated abelian groups are residually finite and amenable, hence weakly stable by [AP,
  Theorem 1.1], so the hypothesis reduces to 3.
- **Firewall.** None of 3--6 is an intermediate target between the root and nonsoficity of `F`. A
  proof that `F` is flexibly, very flexibly, locally or weakly stable proves nonsoficity of `F` without
  (B), and proves the root with (B).
- **Novelty.** Every implication into 1 is an instance of a known general principle for groups that are
  not residually finite:
  - [AP, Theorem 7.2(ii)];
  - Glebsky--Rivera, cited by [AP] as Proposition 3 and by [Br] as Theorem 2 (recorded in
    `sofic-stable-implies-residually-finite`; not re-fetched);
  - [Br, Lemma 2.15] with LEF finitely presented groups being residually finite;
  - [BL, §4.4].

  The vacuous directions are immediate. The one nontrivial input is (B). The contribution is a single
  inequality (Lemma 2.1) covering all variants for `F`, with sharp constant, and the bookkeeping that
  lets the root record both readings. No priority is claimed.
