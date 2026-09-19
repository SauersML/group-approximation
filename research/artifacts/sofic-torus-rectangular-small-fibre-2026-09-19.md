# Sofic torus degree regularity and the local rectangular small-fibre lemma

swarm-0917-w16-w16-gs-pull, 2026-09-19, family stability-approximation.

Target: `injective-torus-automata-have-regular-degree` (C2). Builds on
`research/artifacts/lef-torus-small-fibre-2026-09-18.md` (cited as [LEF]; Theorem 1 is
the dimension-free small-fibre lemma, Lemmas A–C the exact-model estimates, Theorem 3
the obstruction to a defect-tolerant version).

## 0. Summary

1. **Reduction (Theorem R, complete).** For every sofic group `G`, C2 at `G` follows
   from a group-free statement LRSF about finite-dimensional tori: a *local*,
   *rectangular* map `T^(dI) -> T^(dJ)` whose every input site is controlled by a
   bounded set of outputs, and which has only `|J| - |I| <= beta |I|` surplus output
   sites, loses at most `delta |I| d` of rank on `H^1`, with `beta = beta(K, d, delta)`.
   This covers every amenable group, where C2 is not known beyond the LEF, locally
   indicable, RLA, RPP and LI-kernel classes.
2. **Sharpness of the constant (Proposition S).** The rank loss per surplus output site
   can be at least `K` for locality `K`. So LRSF must be *proportional*, never
   defect-free, and no argument with a locality-free constant can work (this contains
   [LEF] Theorem 3).
3. **Exact-relation models (Theorem E, complete).** The pull-back certificate of
   [LEF] Lemma C needs only the finitely many relations `w f = w' f'` and `w f = 1`
   (`w, w' in W`, `f, f' in F`) of `G`, not a partial multiplication table. Let
   `Gamma_(W,F)` be the finitely presented group on `W ⊔ F` with these relations and
   `N_(W,F)` the kernel of `Gamma_(W,F) -> <W ∪ F> ≤ G`. If `N_(W,F)` is co-sofic in
   `Gamma_(W,F)` (Becker–Lubotzky–Thom: `delta_N` is a weak-* limit of the stabiliser
   IRSs of finite `Gamma`-sets), then `D` is regular over `Q[G]`. In particular this
   holds when `G` is sofic and `Gamma_(W,F)` is permutation stable.
4. **Obstruction (Proposition B, class kill).** Theorem E is exactly what *square*
   finite models can give. Call a finite model *square-certified* for `(W,F)` if every
   input site has a pull-back certificate. Then:
   - a square-certified model for `(W,F)` is the same thing as a finite
     `Gamma_(W,F)`-set;
   - square-certified models with sofic statistics exist for *every* finite `(W,F)`
     if and only if `G` is LEF.
   So every square strategy (dropping surplus outputs, rewriting defect rows, adding
   registers, per-vertex modulus sets, choosing a cleverer sofic approximation)
   proves, uniformly over all automata of `G`, nothing beyond LEF. The invariant is
   the exact satisfaction of `R_(W,F)` at every vertex. The step that dies is the
   well-definedness of the pulled-back configuration in Lemma C at a vertex where a
   relator of `R_(W,F)` fails; there the input is uncontrolled and [LEF] Theorem 3
   shows a single uncontrolled coordinate can kill all of `H^1`.
5. **Open.** LRSF itself (`local-rectangular-small-fibre-maps-lose-proportional-rank`).
   Beyond LEF, C2 for sofic groups must pass through a defect-tolerant rectangular
   statement of this kind.

## 1. Setup and notation

- `X = (T^d)^G`, `T = R/Z`, sup metric `|.|` on `T^d`.
- `tau: X -> X` injective, continuous, `G`-equivariant; `mu = ev_1 o tau`.
- Degree matrix `D in M_d(Z[G])`: `tau^*(xi) = xi D` on `H^1(X; Z) = Z[G]^d`
  (row vectors).
- From [LEF] Lemmas A and B (valid for every group, no approximation used):
  - (A) finite `W ⊆ G`, `eta > 0`: if `|tau(x)_w - tau(y)_w| < eta` for all `w in W`
    then `|x_1 - y_1| < 1/16`.
  - (B) finite `F ⊆ G` and continuous `mu': (T^d)^F -> T^d` with
    `sup |mu - mu' o res_F| < eta/3`, homotopic to `mu` through maps with the same
    memory, so the degree data of `mu'` is `D`: writing `D = sum_f f D_f`, the
    `H^1`-degree of `mu'` in the variable `u_f` is `D_f` (with the convention of
    [LEF] Section 2).
- `K := max(|F|, |W|)`.

A **sofic approximation** is a sequence `sigma_n: G -> Sym(V_n)` with `|V_n| -> inf`
such that for all `g, h`, `sigma_n(gh) v = sigma_n(g) sigma_n(h) v` and (for `g != h`)
`sigma_n(g) v != sigma_n(h) v` for a `(1 - o(1))`-fraction of `v in V_n`.
For `a = sum a_g g in M_{p x q}(Z[G])` write `sigma(a)` for the integer
`p|V| x q|V|` matrix with blocks
`sigma(a)_(v,u) = sum { a_g : u = sigma(g)^-1 v }` (a `p x q` block for each pair of
vertices). Then row `v` of `sigma(a) sigma(b)` equals row `v` of `sigma(ab)` whenever
`sigma(h)^-1 sigma(g)^-1 v = sigma(gh)^-1 v` for all `g in supp a`, `h in supp b`.

**The model map.** `tau_sigma: (T^d)^V -> (T^d)^V`,
`tau_sigma(u)_q = mu'((u_(sigma(f)^-1 q))_(f in F))`.
On `H^1 = Z^(dV)` (row vectors, coordinate 1-forms as basis) `tau_sigma^*` is right
multiplication by `sigma(D)`. This is the computation of [LEF] Lemma C with `phi`
replaced by `sigma`: the pull-back of coordinate `(q, i)` is
`sum_f (e_i D_f)` placed at vertex `sigma(f)^-1 q`. For `G` itself (`V = G`,
`sigma(g) v = v g^-1`, an exact action) it reproduces `tau^*(xi) = xi D`, since
`tau(x)_g = mu'((x_(gf))_f)`.

## 2. The pull-back certificate

Let `V` be a finite set with permutations `s(w)` (`w in W`) and `s(f)` (`f in F`);
`W` and `F` are used as disjoint labels, so `s(w)` and `s(f)` may differ even when
`w = f` in `G`. Put `tau_s(u)_q = mu'((u_(s(f)^-1 q))_(f in F))`.

**Definition.** A vertex `v` is *certified* if
- (i) `w f = w' f'` in `G` implies `s(f)^-1 s(w)^-1 v = s(f')^-1 s(w')^-1 v`, and
- (ii) `w f = 1` in `G` implies `s(f)^-1 s(w)^-1 v = v`,

for all `w, w' in W`, `f, f' in F`. Its *control set* is
`C(v) = { s(w)^-1 v : w in W }`, of size at most `|W|`.

**Lemma P.** If `v` is certified and `u, u' in (T^d)^V` satisfy
`|tau_s(u)_q - tau_s(u')_q| < eta/3` for all `q in C(v)`, then `|u_v - u'_v| < 1/16`.

*Proof.* By (i) and (ii) the rule `x_(wf) := u_(s(f)^-1 s(w)^-1 v)`, `x_1 := u_v`
defines `x` on `WF ∪ {1}` without conflict; set `x_g = 0` elsewhere. Define `x'` from
`u'` in the same way. With `(g.x)_h = x_(g^-1 h)` we have
`tau(x)_w = mu(w^-1 . x)` and `(w^-1 . x)_f = x_(wf)`. By Lemma B,
`|tau(x)_w - mu'((x_(wf))_f)| < eta/3`, and
`mu'((x_(wf))_f) = mu'((u_(s(f)^-1 q))_f) = tau_s(u)_q` for `q = s(w)^-1 v in C(v)`.
The same holds for `x'`. So `|tau(x)_w - tau(x')_w| < eta` for every `w in W`, and
Lemma A gives `|x_1 - x'_1| < 1/16`, that is `|u_v - u'_v| < 1/16`. ∎

No injectivity of `s` on any set is used, and no relation outside
`R_(W,F) = { w f f'^-1 w'^-1 : wf = w'f' in G } ∪ { w f : wf = 1 in G }` is used.

- In an LEF model (the setting of [LEF]) every vertex is certified.
- In a sofic model `s = sigma`, a vertex `v` is certified as soon as
  `sigma(w) sigma(f) y = sigma(wf) y` at `y = sigma(wf)^-1 v` for all pairs `(w, f)`,
  and `sigma(1) v = v`. Each condition fails on `o(|V|)` vertices (the substitution
  `v -> sigma(wf)^-1 v` is a bijection), so `v` is certified for a
  `(1 - epsilon_n)`-fraction of `v`, with `epsilon_n -> 0`. Write `V^c` for the set of
  certified vertices and `V^b = V \ V^c`.
- **Locality.** The output `tau_s(u)_q` depends only on the inputs at `s(F)^-1 q`, at
  most `|F| <= K` sites.

## 3. Sofic rank and the reduction

Fix a sofic approximation `sigma = sigma_n` of `G`, and suppose `xi D = 0` with
`0 != xi in Q[G]^(1 x d)`; clearing denominators, `xi in Z[G]^(1 x d)`. Let
`E = ∪_j supp xi_j`.

**Lemma Q (a non-zero element has proportional rank).** Let `V^E` be the set of
`v` for which `g -> sigma(g)^-1 v` is injective on `E`. Then
`rank sigma(xi) >= |V^E| / (|E|^2 + 1)`.

*Proof.* For `v in V^E`, row `v` of `sigma(xi)` has the block `(xi_(j,g))_j` at column
vertex `sigma(g)^-1 v` for each `g in E`, with no two `g` merged. So it is non-zero
and supported on `S_v = sigma(E)^-1 v`. If `S_v ∩ S_v' != ∅` then
`v' = sigma(g') sigma(g)^-1 v` for some `g, g' in E`; this symmetric conflict relation
has degree at most `|E|^2`. A greedy choice gives `|V^E| / (|E|^2 + 1)` vertices of
`V^E` with pairwise disjoint row supports, and such non-zero rows are linearly
independent. ∎

**Lemma Z (the relation survives).** Let `V^m` be the set of `v` with
`sigma(f)^-1 sigma(h)^-1 v = sigma(hf)^-1 v` for all `h in E`, `f in F`. Then
`rank(sigma(xi) sigma(D)) <= |V \ V^m| = o(|V|)`.

*Proof.* By Section 1, rows `v in V^m` of `sigma(xi) sigma(D)` equal the same rows of
`sigma(xi D) = 0`. ∎

**Proposition (sofic full-rank criterion).** With `c = 1/(|E|^2 + 1)`,
`rank sigma_n(D) <= d|V_n| - c|V_n| + o(|V_n|)`.

*Proof.* Sylvester's inequality over `Q`, with inner dimension `d|V|`:
`rank(sigma(xi) sigma(D)) >= rank sigma(xi) + rank sigma(D) - d|V|`. Insert Lemmas Q
and Z; `|V^E| = (1 - o(1))|V|` by soficity. ∎

So C2 holds at `tau` as soon as `rank sigma_n(D) >= d|V_n| - o(|V_n|)` along one
sofic approximation. Since `rank sigma_n(D) = rank tau_sigma^*`, this is an
almost-full-rank statement for the model maps.

**Theorem R.** If LRSF (Section 4) holds, then every sofic group satisfies C2, and
hence (by `torus-automata-with-regular-degree-are-surjective`) is torus surjunctive.

*Proof.* Put `I = V^c`, `J = V` and `g(u) = tau_sigma(u ⊕ 0)`, with the inputs at the
uncertified vertices `V^b` frozen at `0`.
- *Control.* Each `v in I` has the control set `C(v)`, `|C(v)| <= K`, with modulus
  `eta/3 -> 1/16`, by Lemma P. Lemma P applies to all `u, u'`, frozen or not.
- *Locality.* Output `q` depends on at most `|F| <= K` input sites of `I`.
- *Surplus.* `|J| - |I| = |V^b| <= epsilon_n |V|`, and `epsilon_n -> 0`.

The inclusion `iota: T^(dI) -> T^(dV)` (zero on `V^b`) gives `g = tau_sigma o iota`, so
`rank g^* <= rank tau_sigma^* = rank sigma(D)`. For any `delta > 0`, LRSF with
constants `(K, d, eta/3, delta)` gives `rank g^* >= (1 - delta) d |I|` once
`epsilon_n <= beta / 2`. Then `rank sigma(D) >= (1 - delta)(1 - epsilon_n) d |V|`.
Choose `delta` with `2 delta d < c/2`. This contradicts the Proposition for large
`n`, so `xi D = 0` forces `xi = 0`. ∎

**Amenable groups.** They are sofic, so Theorem R covers them. A Følner set `Phi` gives the same
rectangular problem directly, with no defects: inputs on `Phi` (zero outside),
outputs on `J = Phi W ∪ Phi F^-1`, and surplus `|J| - |Phi| = o(|Phi|)`. Every input is
certified, because the action is exact. This remark is not needed for Theorem R.

## 4. The local rectangular small-fibre lemma (LRSF)

A *`(K, eta)`-local rectangular map* is a continuous `g: (T^d)^I -> (T^d)^J`
(`I`, `J` finite) such that:
- **(L) locality.** Each output site `j` depends only on the inputs at a set
  `F_j ⊆ I` with `|F_j| <= K`.
- **(C) control.** Each input site `i` has a set `C_i ⊆ J` with `|C_i| <= K` such
  that `|g(u)_j - g(u')_j| < eta` for all `j in C_i` implies `|u_i - u'_i| < 1/16`.

**LRSF.** For all `K, d, eta` and `delta > 0` there is `beta = beta(K, d, eta, delta) > 0`
such that every `(K, eta)`-local rectangular map with `|J| - |I| <= beta |I|` has
`rank g^* >= (1 - delta) d |I|` on `H^1`.

The *linear form* is `rank g^* >= d|I| - C(K, d, eta) d (|J| - |I|)`. It implies LRSF.

**Remarks.**
1. *Square case.* If `|J| = |I|`, then (C) gives fibres of sup-diameter `<= 1/16`, and
   [LEF] Theorem 1 gives full rank, even without (L). So LRSF is the defect-tolerant
   extension of Theorem 1.
2. *Without (L) it is false.* [LEF] Theorem 3 gives `T^(N-1) -> T^N`, an injection into
   a small ball: all inputs are controlled, the surplus is one site, and `g^* = 0`.
3. *Which form is used.* Theorem R uses LRSF exactly as stated, with `eta` fixed by
   `tau` and uniform in `n`. The fibre form (replace (C) by "`g(u)_(C_i) = g(u')_(C_i)`
   implies `|u_i - u'_i| <= 1/16`") would be a stronger statement.

**Proposition S (the loss per surplus site is at least `K - 1`).** For every
`k >= 1` there is `eta_k > 0` such that, for every `m`, there is a
`(k + 1, eta_k)`-local rectangular map with `d = 1`, `|I| = km`, `|J| = (k+1) m` and
`g^* = 0`. Hence, for `eta <= eta_k`, necessarily `beta(k+1, 1, eta, delta) < 1/k` for
every `delta < 1`, and `C(K, 1, eta) >= K - 1`.

*Proof.* Take a smooth embedding `T^k -> R^(k+1)` (the iterated tubular construction:
`T^k` embeds in `R^(k+1)` for every `k`). Rescale it into the ball of radius `1/8`
and project to `T^(k+1)`, which is injective on that ball; call the result `e`.
- Its image lies in a contractible ball, so `e^* = 0`.
- `e^-1` is uniformly continuous on the compact image, which gives `eta_k`.

Let `g = e x ... x e` (`m` blocks), with `F_j` = the block of `j` (`k` sites) and
`C_i` = the `k + 1` outputs of the block of `i`. Then `g^* = 0`, and
`|J| - |I| = m = |I|/k`. ∎

So the constant in LRSF must depend on the locality, and any proof must be
*proportional*: the loss must be charged to surplus sites at rate at least `K - 1`.
No defect-free statement can replace LRSF.

## 5. Exact-relation models (Theorem E)

Let `Gamma = Gamma_(W,F)` be the group generated by symbols `w in W` and `f in F`
(disjoint), with relators `R_(W,F)` from Section 2. Let `G_0 = <W ∪ F> ≤ G`, let
`pi: Gamma -> G_0` be the evident surjection, and let `N = ker pi`. Following
Becker–Lubotzky–Thom, call `N` *co-sofic* if there are finite `Gamma`-sets `V_n`
with `|Fix_(V_n)(gamma)| / |V_n| -> 1_N(gamma)` for every `gamma in Gamma`. For normal
`N` this is weak-* convergence of the stabiliser IRSs to `delta_N`.

**Theorem E.** Let `G` be any group and `tau` injective with Lemma A and B data
`(W, eta, F, mu')`. If `N_(W,F)` is co-sofic in `Gamma_(W,F)`, then `xi -> xi D` is
injective on `Q[G]^d`.

*Proof.*
1. *Reduction to `G_0`.* `supp D ⊆ F ⊆ G_0`. Write `Q[G] = ⊕_t t Q[G_0]` over left
   coset representatives `t`, and `xi = sum_t t xi_t`. Then `xi D = sum_t t (xi_t D)`
   with `xi_t D in Q[G_0]^d`, so `xi D = 0` forces every `xi_t D = 0`. Assume
   `0 != xi in Z[G_0]^(1 x d)`, `xi D = 0`, and let `E = ∪_j supp xi_j`.
2. *Square models.* Let `s` be the action of `Gamma` on `V = V_n`. Every relator of
   `R_(W,F)` is trivial in `Gamma`, so every vertex is certified. By Lemma P,
   `tau_s(u) = tau_s(u')` gives `|u_v - u'_v| < 1/16` at every `v`. So `tau_s` has
   fibres of sup-diameter `<= 1/16`, and [LEF] Theorem 1 gives
   `tau_s^* in GL_(d|V|)(Z)`. Here `tau_s^*` is right multiplication by the matrix
   `s(D)` whose block at `(v, s(f)^-1 v)` gets `D_f`.
3. *Transport of `xi`.* Choose lifts `gamma_g in Gamma` of the elements `g in E ∪ EF`,
   and let `s(xi)` have block `sum { xi_h : u = gamma_h^-1 v }` at `(v, u)`.
   - Row `v` of `s(xi) s(D)` puts `xi_h D_f` at column `(gamma_h f)^-1 v`.
   - Now `gamma_(hf) (gamma_h f)^-1 in N` for all `h in E`, `f in F`. At the
     `(1 - o(1))`-fraction of `v` fixed by these finitely many elements, the column is
     `gamma_(hf)^-1 v`. So row `v` equals `sum_g (sum_(hf = g) xi_h D_f)` placed at
     `gamma_g^-1 v`, which is `0` because `xi D = 0`.
   - Hence `rank(s(xi) s(D)) = o(|V|)`, and since `s(D)` is invertible,
     `rank s(xi) = o(|V|)`.
4. *Lower bound.* For `h != h'` in `E`, `gamma_h gamma_(h')^-1 notin N`, so it fixes
   only `o(|V|)` vertices. So `h -> gamma_h^-1 v` is injective on `E` for a
   `(1 - o(1))`-fraction of `v`. The disjoint-support argument of Lemma Q gives
   `rank s(xi) >= (1 - o(1)) |V| / (|E|^2 + 1)`. This contradicts step 3. ∎

`G` itself need not be sofic. Co-soficity of `N` makes `G_0` sofic, but the models
are exact actions of a finitely presented cover, not sofic approximations of `G`.

**Corollary E1 (stable local presentations).** If `G_0` is sofic and
`Gamma_(W,F)` is permutation stable, then `N_(W,F)` is co-sofic, so C2 holds at
`tau`.

*Proof.* A sofic approximation of `G_0`, read on the generators, is an almost action
of `Gamma`. Stability moves it by `o(1)` in normalised Hamming distance to an exact
action. For each fixed `gamma`, the fixed-point proportions change by `o(1)`, and for
the sofic approximation they tend to `1_(pi(gamma) = 1) = 1_N(gamma)`. ∎

Permutation-stable finitely presented groups include:
- finite groups;
- free groups (no relators);
- finitely generated abelian groups (Arzhantseva–Păunescu);
- polycyclic-by-finite groups (Becker–Lubotzky–Thom, Duke 2019).

Whenever `tau`'s local presentation is one of these and `G_0` is sofic, C2 holds at
`tau`, with no LEF hypothesis on `G`.

- Example: if `W F` has no coincidences (`wf = w'f'` only trivially, and `wf != 1`),
  then `Gamma` is free on `|W| + |F|` generators.

**Remark (where Theorem E is informative).** Suppose `G` is finitely presented and
`W = F = B` is a ball containing `1` and every subword of a finite presentation.
Then `Gamma_(W,F) = G` and `N = 1`, as in step 3 of Section 6. Co-soficity of the
trivial subgroup means finite `G`-sets on which every `gamma != 1` fixes a vanishing
proportion of points, so `G` is residually finite. Theorem E is therefore informative
only when `(W, F)` is small compared with the relations of `G`. At group level
Section 6 caps it at LEF.

## 6. Square certification is exactly LEF (Proposition B)

A *square-certified model* for `(W, F)` is a finite set `V` with permutations
`s(w), s(f)` in which every vertex is certified. Only then does [LEF] Theorem 1
apply to the whole model map, with no surplus.

**Lemma B1.** Square-certified models for `(W, F)` are exactly the finite
`Gamma_(W,F)`-sets.

*Proof.* Condition (i) at every `v` says `s(w) s(f) = s(w') s(f')` as permutations,
and (ii) says `s(w) s(f) = id`. These are the relators `R_(W,F)`. ∎

To transport a relation `xi D = 0` (Theorem E, steps 3–4), a model also needs sofic
statistics: lifts of trivial elements fix most points, and lifts of non-trivial
elements fix few. Along a sequence of models this is exactly co-soficity of
`N_(W,F)`.

**Proposition B.** `G` is LEF if and only if `N_(W,F)` is co-sofic in
`Gamma_(W,F)` for every pair of finite sets `W, F ⊆ G`.

*Proof of "if".* Given a finite `K ⊆ G`, put `W = F = K ∪ {1}`, writing `w_k, f_k`
for the two copies of `k`. Take a finite `Gamma`-set `V` with good statistics on the
finitely many elements below, let `Q ≤ Sym(V)` be the image of `Gamma`, and set
`phi(k) = s(w_k) s(f_1)`.
- In `G`: `w_1 f_1 = 1`, `w_1 f_b = b = w_b f_1`, and `w_a f_b = ab = w_(ab) f_1`
  whenever `a, b, ab in K`.
- So in `Q`: `s(f_1) = s(w_1)^-1`, hence `s(f_b) = s(w_1)^-1 phi(b) = s(f_1) phi(b)`, and
  `phi(a) phi(b) = s(w_a) (s(f_1) phi(b)) = s(w_a) s(f_b) = s(w_(ab)) s(f_1) = phi(ab)`.
  Also `phi(1) = s(w_1) s(f_1) = 1`.
- For `a != b` in `K`, `gamma = w_a f_1 (w_b f_1)^-1` maps to `a b^-1 != 1`. So
  `gamma notin N`, it moves most points, and `phi(a) != phi(b)`.

Hence `phi: K -> Q` is an injective partial homomorphism, and `G` is LEF.

*Proof of "only if".* Fix `W, F` and a radius `r`. Choose an LEF model `phi: K -> Q`
with `K` containing `W ∪ F ∪ WF ∪ {1}`, all inverses, and all evaluations in `G` of
prefixes of words of length `<= r` in `W ∪ F` and their inverses. Let `Gamma` act on
`Q` by `s(x) q = phi(x) q`.
- The relators hold: `wf = w'f'` gives `phi(w) phi(f) = phi(wf) = phi(w'f') =
  phi(w') phi(f')`, and `wf = 1` gives `phi(w) phi(f) = phi(1) = 1`.
- By induction on prefixes, a word `gamma` of length `<= r` acts by
  `phi(pi(gamma))`. By injectivity this is the identity if `gamma in N`, and
  otherwise it has no fixed point.

Letting `r -> inf` gives exact statistics `1_N`. ∎

**Consequence (class kill).** Square certification is a property of the triple
`(G, W, F)` alone. A method that uses nothing of `tau` beyond Lemmas A and B and
certifies every vertex of a finite model therefore proves C2 for all automata of `G`
only for LEF groups. This covers:
- dropping the surplus outputs;
- rewriting or deleting the rows at defect vertices;
- adding registers at defect vertices;
- per-vertex modulus sets;
- choosing a special sofic approximation.

Beyond LEF, a proof must do one of two things. It can use which `(W, F)` actually
occur for automata with a non-regular degree, which is Theorem E's per-automaton
room. Or it can tolerate uncertified vertices, which is LRSF.

- **Invariant.** Exact satisfaction of `R_(W,F)` at every vertex.
- **Dying step.** Lemma P's pull-back `x_(wf) := u_(s(f)^-1 s(w)^-1 v)` is not
  well-defined at a vertex where a relator of `R_(W,F)` fails. There the input is
  uncontrolled, and [LEF] Theorem 3 shows that one uncontrolled coordinate can kill
  all of `H^1` in the absence of locality.

## 7. What the model route really needs, and attempts on LRSF

**The target is L^2-injectivity.** By the sofic rank approximation of Elek–Szabó
(Math. Ann. 2005), `rank sigma_n(D) / |V_n| -> d - dim_vN ker(. D on l^2(G)^d)` for
sofic `G` and `D in M_d(Q[G])`. So the almost-full-rank condition of Section 3 is
equivalent to injectivity of `D` on `l^2(G)^d`, which is stronger than C2.

- Any finite-model proof of C2 for sofic groups therefore proves `l^2`-injectivity of
  the degree.
- A counterexample to `l^2`-injectivity of `D(tau)` for an injective `tau` over a
  sofic group would refute LRSF, since Theorem R's proof gives `l^2`-injectivity.
- This remark is not used in any proof above.

**Attempts on LRSF, and where each dies.**
1. *Patchwise Theorem 1.* Apply Theorem 1 to a patch `A ⊆ I` with the inputs outside
   `A` frozen. The outputs controlling `A` are `C(A)`, and the patch map
   `T^(dA) -> T^(dC(A))` is again rectangular, with surplus `|C(A)| - |A|`. The problem
   is self-similar and nothing is gained. It dies at the same boundary as Section 6.
2. *Dimension and counting.* Small fibres give covering-dimension and
   mean-dimension lower bounds on the image. But Proposition S's blocks have
   full-dimensional images and `g^* = 0`: dimension does not see `H^1` rank.
3. *Local kernel vectors.* If LRSF fails, `ker g_*` on `H_1 = Z^(dI)` has dimension
   `>= delta d |I|`, and `g_*` is a `K`-sparse integer matrix. One wants a kernel
   vector supported on a bounded set, which would give a bounded sub-torus mapped to a
   small ball, then contradict control. Sparse matrices need not have local kernel
   vectors, and even a local kernel torus is allowed (Proposition S). This dies for
   lack of a quantitative trade-off between kernel support and surplus.
4. *Adding perturbation registers.* Add `|J| - |I|` dummy inputs to make the map
   square. The dummies must be controlled with a modulus independent of `|I|`. That
   needs `omega(eta(2 eps)) < c eps` for the moduli of `tau` and `tau^-1`, which fails
   for merely continuous `tau`.
5. *Top homology with supports.* Theorem 1's final step (`H_N(O) = 0` for a proper open
   `O ⊂ T^N`) is global. A version for the rectangular case would need
   `H^(d|I|)` of a neighbourhood of `g(T^(dI))` inside `T^(dJ)`, where the image has
   codimension `d(|J| - |I|)`. This is where a proof would have to use (L), and no such
   estimate was found.

LRSF stays OPEN. The first test cases are:
- the linear form at `K = 2`, `d = 1` (chains and cycles of sites);
- the rectangular maps that Følner sets produce for an amenable group that is not
  LEF, where Proposition B rules out square models.
