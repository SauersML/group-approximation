# Spectral fold-seed floor: strongly ergodic actions of F(a,b) have sigma_b > 0

Agent swarm-0917-w13-w13-fp-last1, 2026-09-18. Scripts:
`experiments/fpbs-z3-overgroup-2026-09-17/` (`spectral_check.py`, `search_alpha.py`).

## 0. Summary

Setting as in `research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md`:
`L = F(a, b)`, `K = <a, b a b^{-2}>`, triples `T_w = (w, a w, b w)`, `cl(A)` the
closure of `A` under "two of the three entries (with multiplicity) in the set
forces the third", `sigma_b(X) = inf { μ(A) : cl(A) conull }`.

For a p.m.p. action `L ↷ (X, μ)` on a **non-atomic** space put

```text
kappa'(X) = inf over μ(I) = 1/2 of  μ( I \ (a^{-1} I ∩ b^{-1} I) ),
kappa(X)  = inf over μ(I) = 1/2 of  max_{s ∈ {a,b}} μ(I Δ s I),
rho_X     = sup { <M f, f> / ||f||^2 : 0 ≠ f ∈ L^2_0(X, μ) real },
M         = (1/4)(a + a^{-1} + b + b^{-1})  (Koopman operators).
```

**Theorem S.** `sigma_b(X) ≥ kappa'(X) ≥ kappa(X)/2 ≥ (1 − rho_X)/4`.

No freeness is used. Consequences (§3):

1. **Strong ergodicity suffices.** If `X` is strongly ergodic then
   `kappa(X) > 0`, so `sigma_b(X) > 0`. This is the open direction of the
   conjecture in §4.4 of `research/artifacts/fpbs-congruence-fold-census-2026-09-18.md`
   (w11), for all actions, not only profinite ones.
2. **Bernoulli class, explicit constant.** If `X` is non-atomic and weakly
   contained in a Bernoulli shift of `L`, then
   `sigma_b(X) ≥ (1 − rho)/4`, where `rho = rho(F_2, {a^{±1}, b^{±1}})` is the
   Kesten spectral radius. With Kesten's value `rho = √3/2` this is
   `(2 − √3)/8 = 0.03349...`, which is about 2.4 times the w8 constant `0.01406`
   (`fpbs-weakly-bernoulli-fold-seeds-have-density-floor`), with a one-page
   deterministic proof and no random-graph first moment.
3. **Uniform in depth.** The same bound holds for `X ∘ φ^j` for every `j ≥ 0`
   (`φ(a) = a`, `φ(b) = b a b^{-2}`), for every non-atomic `X` weakly contained
   in Bernoulli.
4. **Chord floors.** With Theorem B (`fpbs-mal-graphing-b-length-weighted-floor`),
   every generating graphing of `R_L` over `R_K` has
   `Σ |h|_{K,b} μ(D_h) ≥ (1 − rho_X)/4` on every free action with `rho_X < 1`.

Finite exhaustive check (`spectral_check.py`, `n = 12, 16`): `r(Q) ≥ kappa'
≥ n(1 − λ_2)/4` on every random Schreier graph tested, with equality
`r = kappa'` in 3 of 10 samples at `n = 16`.

## 1. The combinatorial step: `sigma_b ≥ kappa'`

**Rounds.** Put `C_0 = A` and let `C_k` be `C_{k-1}` together with every `z`
for which some triple `T_w` has `z` in one position and its two other positions
in `C_{k-1}`. Each `C_k` is measurable (a finite Boolean combination of
translates of `C_{k-1}`), the sequence increases, and `cl(A) = ∪_k C_k`, since
every derivation is finite. A new point never fills two positions of its own
derivation triple: if `z` filled two positions, the rule would need `z` itself
in `C_{k-1}`.

**Lemma 1.1 (derivation map).** Let `A ⊆ I ⊆ C_k` with `C_{k-1} ⊆ I`. For
`z ∈ I \ A`, let `j(z)` be the round in which `z` enters. Choose `w(z)` as the
first element, in the fixed order `z, a^{-1} z, b^{-1} z`, such that `T_{w(z)}`
has `z` in one position and its two other positions in `C_{j(z)-1}`. Then:

1. `z ↦ w(z)` is measurable, and on each of the three pieces where
   `w(z) = z`, `a^{-1} z` or `b^{-1} z` it is the restriction of a
   measure-preserving bijection;
2. `T_{w(z)} ⊆ I`, so `w(z) ∈ I ∩ a^{-1} I ∩ b^{-1} I`;
3. `z ↦ w(z)` is injective on `I \ A`.

*Proof.* (1) The pieces are defined by finitely many translates of the
`C_i`, so they are measurable. (2) The two other positions lie in
`C_{j(z)-1} ⊆ C_{k-1} ⊆ I`, and `z ∈ I`. (3) Suppose `w(z) = w(z') = w` with
`z ≠ z'`, and say `j(z) ≤ j(z')`. Then `z'` is a position of `T_w` other than
`z`, so `z' ∈ C_{j(z)-1} ⊆ C_{j(z')-1}`. This contradicts `z'` entering at
round `j(z')`. ∎

By (1) and (3) the three images are disjoint and each has the measure of its
piece. So `μ(w(I \ A)) = μ(I \ A)`, and by (2),

```text
μ(I ∩ a^{-1} I ∩ b^{-1} I)  ≥  μ(I) − μ(A).                        (1.1)
```

**Proposition 1.2.** If `X` is non-atomic then `sigma_b(X) ≥ kappa'(X)`.

*Proof.* Let `cl(A)` be conull. If `μ(A) ≥ 1/2`, then
`μ(A) ≥ 1/2 ≥ kappa'` (as `kappa' ≤ μ(I) = 1/2`). Otherwise
`μ(C_k) → 1`, so there is `k ≥ 1` with `μ(C_{k-1}) ≤ 1/2 < μ(C_k)`. As `μ` is
non-atomic, pick `D' ⊆ C_k \ C_{k-1}` with `μ(C_{k-1} ∪ D') = 1/2` and put
`I = C_{k-1} ∪ D'`. Then `A ⊆ C_{k-1} ⊆ I ⊆ C_k`, and (1.1) gives

```text
μ(A)  ≥  μ(I) − μ(I ∩ a^{-1} I ∩ b^{-1} I)  =  μ(I \ (a^{-1} I ∩ b^{-1} I))  ≥  kappa'(X).
```

Take the infimum over `A`. ∎

**Remark (the invariant).** Every point of the crossing set `I` that is not a
seed uses up its own triple inside `I`, and different points use different
triples. So the seeds pay for at least the part of `I` whose triple leaves
`I`. This is an isoperimetric statement about the triple hypergraph, and it
is the whole mechanism.

## 2. The spectral step: `kappa' ≥ kappa/2 ≥ (1 − rho_X)/4`

Let `μ(I) = 1/2`. For `s ∈ {a, b}`, `I \ s^{-1} I ⊆ I \ (a^{-1} I ∩ b^{-1} I)`,
and `μ(I \ s^{-1} I) = μ(I) − μ(I ∩ s^{-1} I) = μ(s I \ I)`, since `s` preserves
`μ`. As `μ(sI) = μ(I)`, `μ(I Δ s I) = 2 μ(sI \ I)`. So

```text
μ(I \ (a^{-1} I ∩ b^{-1} I))  ≥  max_s μ(I Δ s I) / 2,
```

and taking infima, `kappa' ≥ kappa/2`.

Put `f = 1_I − 1/2`. It is real, has mean `0` and `||f||^2 = 1/4`. Write
`π(s)` for the Koopman unitary, with `π(s) 1_I = 1_{sI}`. Then
`μ(I ∩ sI) = <1_I, π(s) 1_I> = <f, π(s) f> + 1/4`, so

```text
μ(I Δ s I) = 2 (1/2 − μ(I ∩ s I)) = 2 (1/4 − <f, π(s) f>).
```

Because `f` is real, `<f, π(s) f> = <π(s^{-1}) f, f> = <f, π(s^{-1}) f>`. So
`<f, π(a) f> + <f, π(b) f> = 2 <M f, f>`, and

```text
μ(I Δ a I) + μ(I Δ b I) = 1 − 4 <M f, f>  ≥  1 − 4 rho_X ||f||^2 = 1 − rho_X.
```

The maximum is at least the average, so `max_s μ(I Δ s I) ≥ (1 − rho_X)/2`.
Hence `kappa ≥ (1 − rho_X)/2`, and Theorem S follows with Proposition 1.2. ∎

**Remark.** The same computation at `μ(I) = t` gives the average
`t(1 − t)(1 − rho_X)`, which is largest at `t = 1/2`; the crossing level 1/2 is
the best one for this argument.

## 3. Consequences

**Corollary 3.1 (strong ergodicity).** If `L ↷ X` is strongly ergodic
(every almost invariant sequence `A_n`, i.e. `μ(A_n Δ g A_n) → 0` for all
`g`, has `μ(A_n)(1 − μ(A_n)) → 0`), then `kappa(X) > 0` and
`sigma_b(X) ≥ kappa(X)/2 > 0`.

*Proof.* If `kappa(X) = 0`, pick `I_n` with `μ(I_n) = 1/2` and
`μ(I_n Δ s I_n) → 0` for `s = a, b`. By the triangle inequality this holds
for every `g ∈ L`, so `(I_n)` is almost invariant with
`μ(I_n)(1 − μ(I_n)) = 1/4`. ∎ (Strongly ergodic actions of an infinite group
are ergodic, hence non-atomic when free; in general we assume non-atomic.)

**Lemma 3.2 (monotone under weak containment).** If `X ≺ Y`, both
non-atomic, then `kappa(X) ≥ kappa(Y)`.

*Proof.* Kechris' definition of `X ≺ Y` (the one imported by
`fpbs-weakly-bernoulli-fold-seeds-have-density-floor-proof`): for Borel
`A_1..A_n ⊆ X`, finite `F ⊆ L` and `ε > 0` there are `B_1..B_n ⊆ Y` with
`|μ(g A_i ∩ A_j) − ν(g B_i ∩ B_j)| < ε` for `g ∈ F`. Apply it with `n = 1`,
`A_1 = I`, `μ(I) = 1/2`, `F = {1, a, b}`. This gives `B` with
`|ν(B) − 1/2| < ε` and `|ν(sB ∩ B) − μ(sI ∩ I)| < ε`. Change `B` by a set of
measure `< ε` to get `B'` with `ν(B') = 1/2`; this moves each `ν(sB ∩ B)` by
less than `2ε`. So `ν(B' Δ s B') = 1 − 2ν(sB' ∩ B') ≤ μ(I Δ sI) + 6ε`. Hence
`kappa(Y) ≤ max_s μ(I Δ s I) + 6ε`. ∎

**Lemma 3.3 (Bernoulli spectrum).** Let `Y = (Ω, ν)^L` be a Bernoulli shift of
`L`, `Ω` a standard probability space, and let `ψ : L → L` be any injective
homomorphism. Then the Koopman representation of `Y ∘ ψ` on `L^2_0` is a
multiple of `λ_L`, so `rho_{Y∘ψ} ≤ rho(F_2, {a^{±1}, b^{±1}}) =: rho`.

*Proof.* Take an orthonormal basis `1 = e_0, e_1, e_2, ...` of `L^2(Ω)`. The
products `⊗_g e_{c(g)}` over finitely supported `c : L → N` form an
orthonormal basis of `L^2(Y)`, and `L` permutes them by translating `c`. The
nonconstant ones have nonempty finite support, whose stabilizer in `L` is a
finite subgroup of a torsion-free group, hence trivial. So
`L^2_0(Y) = ⊕ l^2(L)` as `L`-representations. The image `ψ(L)` acts freely on
`L` by left translation, so `l^2(L)|_{ψ(L)}` is a multiple of `λ_{ψ(L)}`, and
pulling back by the isomorphism `ψ : L → ψ(L)` gives a multiple of `λ_L`. A
multiple of `λ_L` has `||M|| = rho`. ∎

**Corollary 3.4 (Bernoulli class, all depths).** Let `X` be non-atomic and
weakly contained in a Bernoulli shift `Y` of `L`. Then for every `j ≥ 0`,

```text
sigma_b(X ∘ φ^j)  ≥  (1 − rho)/4,
```

and `rho = √3/2` by Kesten's formula, so the bound is `(2 − √3)/8`.

*Proof.* `X ∘ φ^j ≺ Y ∘ φ^j`: the definition only involves the finitely many
group elements `φ^j(F)`. `Y ∘ φ^j` is non-atomic. By Lemmas 3.2 and 3.3 and §2,
`kappa(X ∘ φ^j) ≥ kappa(Y ∘ φ^j) ≥ (1 − rho)/2`. Apply Proposition 1.2 and
§2 (`sigma_b ≥ kappa/2`). ∎

**Corollary 3.5 (chord floors).** For every free p.m.p. action of `L` and every
graphing `Φ = ⊔ h|_{D_h}` with `R_K ∨ Φ = R_L`,
`Σ_h |h|_{K,b} μ(D_h) ≥ (1 − rho_X)/4`, by Theorem B of
`fpbs-mal-graphing-b-length-weighted-floor`. In particular, on the Bernoulli
class, `relC_{≤ r}(R_L; R_K) ≥ (2 − √3)/(8r)`, replacing `1/(80 r)`.

**Imports.** (i) Kechris' definition of weak containment (as in w8).
(ii) `kesten-amenable-stabilizer-uniform-gap` (ESTABLISHED) with `H = {1}`,
`A = F_2`: `rho < 1`. (iii) For the numerical value only, Kesten's formula for
the free group: the simple random walk on `F_k` with the `2k` generators
`s^{±1}` has spectral radius `√(2k−1)/k` (H. Kesten, *Symmetric random walks
on groups*, Trans. AMS 92 (1959) 336–354, Theorem 3), so `rho = √3/2` for
`k = 2`. Everything with an explicit constant uses (iii); every positivity
statement uses only (ii).

## 4. What this changes, and where the argument stops

1. **w11 conjecture, half settled.** §4.4 of the census artifact conjectures
   `sigma_b(X) > 0` iff `X` is strongly ergodic, for free ergodic profinite
   `X`, with "not strongly ergodic implies 0" proved there only for the K1 and
   K2 types. Corollary 3.1 proves "strongly ergodic implies
   `sigma_b > 0`" for every non-atomic action, profinite or not. It also gives
   level-wise lower bounds: for a profinite `X` with levels `Q_n`,
   `sigma_b(X) ≥ inf_n (1 − λ_2(Q_n))/4`, the finite counterpart of the w11
   upper bound `sigma_b(X) = inf_n r(Q_n)/|Q_n|`. The remaining direction is
   open: does `kappa(X) = 0` force `sigma_b(X) = 0`?
2. **Profinite witnesses at depth `j`.** The spectral gap of `X ∘ φ^j` is a
   gap for the subgroup `L_j = φ^j(L)`, which has infinite index. For
   Bernoulli it is uniform in `j` (Lemma 3.3). For a congruence tower it holds
   at each fixed `j` whenever the level quotients of `L_j` form an expander
   family, but Theorem S gives nothing uniform in `j` there. This matches the
   w11 census dips at `j = 5`.
3. **Target not closed.** `fpbs-mal-bernoulli-single-stage-floor` needs a floor
   on `relC(E_rho; E_K)` over all graphings. Theorem S bounds only the
   one-double-coset quantity `sigma_b`, and through Theorem B it bounds
   graphings of bounded `b`-length, with loss `|h|_{K,b}`.
4. **Where the spectral argument stops for chords.** Lemma 1.1 needs a
   derivation process in which every new point has a witness (its triple)
   *inside the crossing set* `I`, and different points have different
   witnesses. For a general graphing, a point `z` joins the class of `bz`
   through a circuit made of one or more chords and `R_K`-paths, of unbounded
   length. Adding a chord set of measure `δ` can raise the derived mass
   `μ{ w : w ~ bw }` by an amount not bounded by any multiple of `δ` (the w12
   non-exactness example `bab ⊔ bbab`). So no crossing set with injective
   witnesses exists in general. Theorem B avoids this by unfolding each chord
   into `|h|_{K,b}` seeds, and that is exactly the loss. A uniform floor needs
   a crossing set whose witnesses are the chords themselves, counted once.
   That is a **chord isoperimetry**, and it is the precise remaining content of
   the target on spectral-gap actions.
5. **Z/3 * Z/3 overgroup (negative).** `search_alpha.py` looked for an order-3
   automorphism, conjugate to the triangle rotation of the triple hypertree,
   that maps `K` to a conjugate of `K`. Over all conjugators up to 5 Nielsen
   moves it found none (`search_alpha_out.txt`). So the triangle symmetry does
   not preserve the `K`-coset colouring in that range, and an index-3
   normalizer route is not supported.

## 5. Not claimed

- No floor on `relC(E_rho; E_K)` for graphings of unbounded `b`-length.
- Not the converse "`kappa(X) = 0` implies `sigma_b(X) = 0`".
- No claim that `(2 − √3)/8` is sharp. The census and iid values (.11 and
  `5/32`) are about 3 to 5 times larger.
- No uniform-in-depth bound for profinite congruence witnesses.
