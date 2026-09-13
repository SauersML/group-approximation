# Finitely generated simple weakly sofic groups are linear sofic over finite fields

Lane `ex3-weak-sofic-fg-dichotomy`, 2026-09-13. Unreviewed.

## 0. Statement, credit, scope

**Theorem.** Let `G` be a finitely generated simple group. Then `G` is weakly sofic (Glebsky--Rivera) iff `G` is
*linear sofic over finite fields*, i.e. `G` embeds in a metric ultraproduct `prod_omega GL_(n_i)(F_(q_i)) / N_omega`
with the normalized rank length `rk(g - 1)/n_i` (definition on `simple-group-psl-width-is-finite-field-linear-soficity`).

**Corollary (existence level).** Some group is not weakly sofic iff some group is not linear sofic over finite fields.

**Credit.** The group-theoretic content is Nikolov--Schneider--Thom (arXiv:1703.06092v2). Their proof of Theorem 4
(pp. 12--14) produces, for a nontrivial finitely generated perfect **Fin**-approximable group, a nontrivial homomorphism
into a metric ultraproduct of groups `PSL_(n_i)(q_i)` with the projective rank length `l^pr`. What this note adds:
- the adjoint representation turns projective-rank ultraproducts of `PSL_n(q)` into rank ultraproducts of `GL_(n^2)(q)`
  (Section 1; the same computation is Proposition 3 of
  `research/artifacts/free-minimal-crossed-product-rings-and-permutive-rigidity-2026-09-13.md`);
- so the finitely presented dichotomy of `fp-simple-weak-soficity-is-finite-field-linear-soficity` holds for every
  finitely generated simple group, and the existence corollary follows by Schupp's embedding;
- a second proof (Section 3) that uses only the *statement* of NST Theorem 4. It shows directly that the "near-scalar
  horn" recorded on `fg-simple-weakly-sofic-groups-are-finite-field-linear-sofic` is empty, by running the reviewed
  covering argument of `simple-group-psl-width-is-finite-field-linear-soficity-proof` over a finite set of relations
  supplied by compactness.

**Novelty check (bounded).** Read: NST pp. 1--5, 10--14, 19--20; Arzhantseva--Paunescu arXiv:1212.6780v1 pp. 1--3.
Neither states the theorem or the corollary on those pages. Not read: Stolz--Thom (Proc. LMS 108, 2014), Thom--Wilson,
later papers citing NST. No web search. The corollary may be folklore among experts; do not frame it as new before an
`ex-novelty` pass.

## 1. The adjoint lemma

For `h in GL_n(F)` put `rho(h) = min_(lambda in F) rk(h - lambda)`. On `PSL_n(q) <= PGL_n(q)` this is well defined, and
`l^pr(h) = rho(h)/n` is NST's projective rank length (NST p. 4: `(1/n) min{rk(1 - hat g) : hat g some lift of g}`).
Let `Ad(h)` be `X -> h X h^(-1)` on `M_n(F)`, an element of `GL_(n^2)(F)`.

**Lemma 1.** For every finite field `F`, every `n` and every `h in GL_n(F)`:
`min(rho(h)/n, 1/2) <= rk(Ad(h) - 1)/n^2 <= 2 rho(h)/n`.

*Upper bound.* Write `h = lambda (1 + B)` with `rk B = rho(h)`. Then `h X h^(-1) - X = (hX - Xh) h^(-1)
= lambda (BX - XB) h^(-1)`, whose image over all `X` lies in `(B M_n + M_n B) h^(-1)`, of dimension `<= 2 n rho(h)`.

*Lower bound.* `rk(Ad(h) - 1) = n^2 - dim_F C(h)`, where `C(h)` is the commutant of `h` in `M_n(F)`. Its dimension does
not change under extension to the algebraic closure. Over `Fbar`, `F^n` splits into generalized eigenspaces `V_mu` of
dimensions `m_mu`, and `C(h) <= (+)_mu End(V_mu)`. On `V_mu` the commutant of the nilpotent part with Jordan partition
`p` has dimension `sum_j (p'_j)^2 <= p'_1 m_mu`, where `p'_1 = k_mu = dim ker(h - mu)`. So
`dim C(h) <= sum_mu k_mu m_mu <= n max_mu k_mu`.
- If the maximum is attained at `mu in F`, then `k_mu = n - rk(h - mu) <= n - rho(h)`.
- If `mu notin F`, its Frobenius conjugates are at least two distinct eigenvalues with the same `k`, so `k_mu <= n/2`.

Hence `dim C(h) <= n max(n - rho(h), n/2)`, and `rk(Ad(h) - 1) >= n min(rho(h), n/2)`.

**Corollary 2.** For every sequence `(n_i, q_i)` and ultrafilter `U`, `Ad` induces an injective homomorphism
`prod_U (PSL_(n_i)(q_i), l^pr) -> prod_U (GL_(n_i^2)(F_(q_i)), rk(. - 1)/n_i^2)`. So every group that embeds in a
projective-rank ultraproduct of groups `PSL_n(q)` is linear sofic over finite fields.

*Proof.* `Ad` is a homomorphism trivial on scalars, so it factors through `PGL_n(q) >= PSL_n(q)`. By Lemma 1 a sequence
is null for `l^pr` iff its image is null for the normalized rank, so the induced map is well defined and injective. A
countable group embedding in an ultraproduct over any index set has finite partial approximations along a sequence, so
it embeds in one indexed by `N`. QED

## 2. First proof, through the proof of NST Theorem 4

NST p. 2: "In Section 4, using results of the first author from [18] and of Liebeck and Shalev from [16], we prove that
any non-trivial group which is approximable by finite groups has a non-trivial homomorphism into a metric ultraproduct
of finite simple groups of type PSL_n(q) with conjugacy length function (see Theorem 4)."

NST pp. 13--14 (proof of Theorem 4, `P = F/N` perfect): `P` has a nontrivial homomorphism onto a nontrivial image of the
metric ultraproduct `K/L` of the simple factors `S_i` with conjugacy length; "Since the latter is simple by Proposition
3.1 of [25], we are only left to show that K/L [...] embeds into a metric ultraproduct of groups PSL_(n_i)(q_i)
equipped with the conjugacy length function". The last step is sketched: bounded rank and alternating factors are
absorbed, and "Hence we can embed our ultraproduct K/L into an ultraproduct of groups PSL_(n_i)(q_i) equipped with the
projective length function l^pr_i (i in I)."

**Proof of the Theorem.**
1. Finite simple groups embed in `GL_(|G|)(F_2)` by the regular representation, where a nontrivial element has
   normalized rank at least `1/2`. So let `G` be infinite, hence nonabelian and perfect.
2. Weakly sofic = **Fin**-approximable (NST Example 1, p. 5).
3. By the proof of NST Theorem 4, `G` has a nontrivial homomorphism into `prod_U (PSL_(n_i)(q_i), l^pr)`. `G` is simple,
   so it is injective.
4. By Corollary 2, `G` is linear sofic over finite fields.
5. Conversely, `GL_n(F_q)` is finite and the normalized rank length is bi-invariant, so linear soficity over finite
   fields gives weak soficity. QED

## 3. Second proof, from the statement of NST Theorem 4 only

This avoids the sketched last step of NST. It reuses `simple-group-psl-width-is-finite-field-linear-soficity-proof`
(below: "the PSL proof"), which passed `ex-verify-groups`.

Let `G = <X | R_inf>` be infinite, finitely generated and simple, where `R_inf` is the set of all words trivial in `G`.
Assume `G` is not linear sofic over finite fields. We show `G` is not weakly sofic.

**3.0 Uniform collapse over a finite relation set.** *There are a finite `R' <= R_inf` and `delta_0 > 0` such that every
finite field `F`, every `m` and every `b in GL_m(F)^X` satisfy `max_(r in R') rk(r(b) - 1) >= delta_0 max_x rk(b_x - 1)`.*

*Proof.* Otherwise enumerate `R_inf = {r_1, r_2, ...}`. For each `j` there is a tuple `b^(j)` over some `F_j`, `m_j` with
`max_(r in R_j) rk(r(b^(j)) - 1) < p_j / j`, where `R_j = {r_1, ..., r_j}` and `p_j = max_x rk(b^(j)_x - 1) >= 1`.
- *Localize.* Let `U` be the common fixed space of the `b_x` (codimension `<= |X| p_j`) and `I` the sum of the images of
  the `b_x - 1`. Take `Y >= I` with `Y + U = V` and `dim Y <= 2|X| p_j`, and `Z <= U` a complement of `Y cap U` in `U`.
  Then `V = Y (+) Z`, every word in `b` is `(.)|_Y (+) 1_Z`, and `dim Y >= p_j`.
- *Normalize.* Put `c^(j) = b^(j)|_Y in GL_(d_j)(F_j)`. Relations in `R_j` have normalized rank `< p_j/(j d_j) <= 1/j`,
  and the maximizing generator has normalized rank `>= p_j/(2|X| p_j) = 1/(2|X|)`.
- *Ultraproduct.* Fix a nonprincipal ultrafilter `omega` and `x_0` maximizing for `omega`-almost all `j`. Every
  `r in R_inf` lies in `R_j` eventually, so `x -> (c^(j)_x)` induces a homomorphism
  `G -> prod_omega GL_(d_j)(F_j)/N_omega` with `x_0` not in its kernel. By simplicity it is injective, so `G` is
  linear sofic over finite fields. That contradicts the assumption. QED

**3.1 Template.** `G` is perfect. For each `x in X` fix words with
`x = [u_(x,1), v_(x,1)] ... [u_(x,J), v_(x,J)] q_x` in `F(X)`, where `q_x in R_inf`. For every group `Q` and `a in Q^X`,
`a_x = prod_j [u_(x,j)(a), v_(x,j)(a)] q_x(a)` exactly.

**3.2 Weak models.** Suppose `G` is weakly sofic. By NST Theorem 4 it is **PSL**-approximable, and by the remark after
NST Definition 1 we may take `l_H <= 1` and `delta = 1`. Taking finite sets `S_i` that exhaust `G` and contain every prefix of
the template words, `eps_i -> 0`, and `a^(i)_x = phi_i(x)`, we get groups `H_i = PSL_(n_i)(q_i)`, invariant lengths
`l_i <= 1`, and tuples `a^(i)` such that
- `l_i(r(a^(i))) -> 0` for every `r in R_inf`, since each `r` is evaluated by `|r|` multiplications inside `S_i`;
- `l_i(a^(i)_x) = 1` for every `x in X` with `x != 1` in `G`.

**3.3 Conjugacy and projective lengths are dominated by `l`.**
- *Covering.* Let `c` be the Liebeck--Shalev constant (`liebeck-shalev-normal-subset-covering`) and `h in H_i` with
  `l_i(h) <= 1/4`. Let `S = h^H cup (h^(-1))^H`. Then `S^k = H` for `k = ceil(c log|H| / log|S|) <= c/l^c(h) + 1`, so
  `1 = l_i(a_x) <= k l_i(h) <= c l_i(h)/l^c(h) + 1/4`, hence `l^c(h) <= 4 c l_i(h)`.
- *Projective length.* By the Lipschitz equivalence of `l^c` and `l^pr` on nonabelian finite simple groups (NST p. 4,
  from Liebeck--Shalev), there is `C` with `l^pr <= C l^c <= 4cC l_i` wherever `l_i <= 1/4`.

So `x -> (a^(i)_x)` induces a homomorphism `Phi : G -> prod_U (H_i, l^pr)`. By simplicity it is injective or trivial.

**3.4 Injective case.** Corollary 2 makes `G` linear sofic over finite fields, contrary to the assumption.

**3.5 Trivial case: the near-scalar horn.** Here `rho(a^(i)_x)/n_i -> 0` along `U` for every `x`. Put
`P_i = max_x rho(a^(i)_x)`. Then `P_i >= 1`, since a central `a_x` has length `0`, so `n_i -> infinity` and
`P_i < n_i/(8|X|)` for `U`-almost all `i`. For such `i`, run Section 5 of the PSL proof on a lift of `a^(i)` to
`SL_(n_i)(q_i)`, with two substitutions:
- the collapse constant of its Section 0 is replaced by 3.0: for the scalar-normalized tuple `b`, some `r* in R'` has
  `rk(r*(b) - 1) >= delta_0 P_i` (its 5.3);
- the fixed finite relator set `R` is replaced by `R'`.

Sections 5.1--5.5 use neither finite presentation nor (E1)/(E2); they need only `4 d_0 < n` and `n >= D`, which hold for
large `i`. They give, with `k_2 = ceil(8c|X|D/delta_0)` independent of `i`,
`[u_(x,j)(a), v_(x,j)(a)] in Cons_(4 k_2)(R'(a))`: products of at most `4 k_2` conjugates of values `r(a)^(+-1)`,
`r in R'`. So by 3.1, for a generator `x != 1`,
```text
1 = l_i(a_x) <= 4 J k_2 max_(r in R') l_i(r(a^(i))) + l_i(q_x(a^(i))) -> 0,
```
a contradiction. So `G` is not weakly sofic.

With 3.4 this proves: *not linear sofic over finite fields => not weakly sofic*. The converse is step 5 of Section 2. QED

**Byproduct (quantitative form).** For finitely generated simple `G` not linear sofic over finite fields, there are a
finite `R'' = R' cup {q_x}` and a constant `K` with `l(a_x) <= K max_(r in R'') l(r(a))` for every `PSL_n(q)`, every
invariant length `l` with `sup l = 1` attained by some generator, and every tuple `a`. Combined with the proportional case
(Section 4 of the PSL proof, using the projective collapse derived from 3.0 by Lemma 1), this is the finitely generated
replacement for the width bound (ii) of the finitely presented theorem.

## 4. Existence corollary and consequences

**Corollary.** Some countable group is not weakly sofic iff some countable group is not linear sofic over finite
fields.
- *If.* Linear soficity over finite fields is local and passes to subgroups. So a non-example has a finitely generated
  non-example `Gamma_0`. By Schupp (`countable-group-embeds-in-two-generator-simple-group`), `Gamma_0` embeds in a
  two-generator simple group `S`, which is then not linear sofic over finite fields. By the Theorem, `S` is not weakly
  sofic.
- *Only if.* Linear sofic over finite fields implies weakly sofic.

**Consequences.**
- Glebsky--Rivera Conjecture 4.5 (`non-weakly-sofic-group-exists`) is equivalent to the existence of a group that is
  not linear sofic over finite fields. By Arzhantseva--Paunescu Theorem 8.2 / Observation 8.4, as recorded on
  `non-linear-sofic-group`, `C`-linear soficity passes to finite fields of varying characteristic. So such a group is not
  `C`-linear sofic, which answers that root with `F = C`.
- The rigidity claim `fg-simple-weakly-sofic-groups-are-sofic` is equivalent to: *every finitely generated simple group
  that is linear sofic over finite fields is sofic*. Kind (b) (weak models only through other finite targets) is empty
  for every finitely generated simple group, not only finitely presented ones.
- The Kun--Thom Kazhdan envelope `S` of route `non-weakly-sofic-group-from-simple-weak-sofic-rigidity` is weakly sofic
  iff it is linear sofic over finite fields.

**Model tests.**
- *Sofic infinite simple groups* (e.g. derived full groups of minimal subshifts): weakly sofic and linear sofic over
  finite fields, as the Theorem requires.
- *Section 3.5 on a sofic group.* The horn cannot occur for a group that is linear sofic over finite fields, because
  3.0 fails for it. Consistently, permutation models of such groups have `rho` proportional to `n`, not `o(n)`.
- *Hypothesis check.* Simplicity is used for injectivity of the ultraproduct maps (3.0, 3.3, step 3 of Section 2) and
  for perfectness (3.1). Finite generation is used in 3.0 (a finite `X`) and in NST Theorem 4.
