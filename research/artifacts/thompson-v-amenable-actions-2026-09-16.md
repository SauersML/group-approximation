# Invariant means on V-sets: the soficity reduction, freeness off the fixed set, and excluded stabilizers

2026-09-16. Written proofs only. No computation, build or Lean verification is claimed.
Target lane: `thompson-v-is-sofic`.

- Section 1 turns soficity of `V` into one question about amenable actions. It uses only simplicity and
  Elek–Szabó.
- Sections 2–6 prove, for every invariant mean on every `V`-set, that the part off the global fixed set
  is essentially free. They also show that its typical stabilizers avoid several natural families of
  subgroups.
- Section 7 records what survives.

## 0. Notation and imports

**Cantor set.**
- `C = {0,1}^N`. For a finite word `w`, `[w]` is the cone of sequences with prefix `w`, and `|w|` is
  its length. `[∅] = C`.
- Every clopen set is a finite disjoint union of cones.

**The group V.**
- `V = G_(2,1)` is the group of homeomorphisms `g` of `C` such that there are complete prefix codes
  `u_1, ..., u_k` and `v_1, ..., v_k` with `g(u_i ξ) = v_i ξ` for all `i` and all `ξ`.
- Such a table *witnesses depth ≤ d* if all `|u_i|, |v_i| ≤ d`. Every `g` has some finite depth, and
  the reversed table shows that `g^-1` has the same depth.
- `S` is a finite symmetric generating set of `V` not containing `e`.

**Rigid stabilizers.**
- For a clopen `U`, `V_U = {g ∈ V : gξ = ξ for all ξ ∉ U}`.
- `g V_U g^-1 = V_(gU)`.
- `V_[w] ≠ {e}`: the swap `w0ξ ↔ w1ξ`, identity off `[w]`, is a nontrivial element of `V_[w]`. Call it
  `h_w`.

**V-sets and means.**
- `Ω` is a `V`-set and `m` is an invariant mean on `ℓ∞(Ω)`: positive, `m(1) = 1`, and
  `m(1_(gE)) = m(1_E)`. By linearity and norm density of simple functions, `m(f∘g) = m(f)` for all
  `f ∈ ℓ∞(Ω)` and `g ∈ V`.
- `Fix(g) = {x : gx = x}` and `Fix(V) = ⋂_(s ∈ S) Fix(s)` is the global fixed set. `Stab(x)` is the
  stabilizer, and `Stab(gx) = g Stab(x) g^-1`.
- "Null" means `m`-null. Finite unions of null sets are null. Countable unions need not be, and no
  argument below uses one.

**Imports (the only external inputs).**
- (S) `thompson-v-finitely-presented-infinite-simple`: `V` is finitely generated, infinite and simple.
- (CS) `thompson-v-character-simplex` (Dudko–Medynets): every normalized positive-definite class function
  on `V` is `b·1 + (1-b)·δ_e` with `0 ≤ b ≤ 1`.
- (ES) `elek-szabo-essentially-free-amenable-actions`: Definition 1.3 and Proposition 5.1 of Elek–Szabó,
  Math. Ann. 332 (2005).
- (IRS) The general statement of §§1–3 of
  `research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md`. Let `G` be a
  countably infinite group with no proper finite-index subgroup, every normalized positive-definite
  class function of which is `b·1 + (1-b)δ_e`. Then every IRS of `G` is `(1-b)δ_({e}) + bδ_G`.
  - `V` has no proper finite-index subgroup: the normal core of one would be a proper normal subgroup of
    finite index, and it cannot be trivial since `V` is infinite. So (S) and (CS) give the hypotheses.
- (H) Halving, from `thompson-v-cantor-orbits-have-no-folner-sets-proof`: there is no `V`-invariant
  finitely additive probability on the clopen algebra of `C`. The table `{0,10,11} → {00,01,1}` maps
  `[0]` onto `[00]`, the table `{0,10,11} → {01,00,1}` maps it onto `[01]`, and the swap of `[0]` and
  `[1]` finishes.
- (Tr) *Transitivity.* `V` acts transitively on proper nonempty clopen sets. Write `U` and `C \ U` as
  disjoint unions of `k` and `l` cones, and `U'` and `C \ U'` as `k'` and `l'` cones. Splitting
  `[u] = [u0] ⊔ [u1]` raises a count by one, so we may assume `k = k'` and `l = l'`. The two complete
  prefix codes then have the same size, and matching them defines `g ∈ V` with `gU = U'`.

The isoperimetric constant of a `V`-set `X` is, as in (0.1) of Tucker-Drob arXiv:1407.7474,

```text
φ_S(X) = inf { Σ_(s ∈ S) |sP \ P| / |P| : P ⊆ X finite nonempty }.
```

## 1. The reduction: soficity from one amenable action

**Theorem 1.** The following are equivalent.

1. Some `V`-set without global fixed points carries a `V`-invariant mean.
2. `V` has an essentially free amenable action (Elek–Szabó Definition 1.3): a `V`-set with invariant
   mean `m` and `m(Fix g) = 0` for all `g ≠ e`.
3. `inf { φ_S(V/H) : H < V proper } = 0`.
4. `N_V ≠ V`, where `N_V` is the characteristic subgroup of Elek–Szabó §5.

Each of them implies that `V` is sofic. A proper co-amenable subgroup `H < V`, that is, an invariant mean
on `V/H`, gives item 1 with `Ω = V/H`.

*Proof.*

**(1 ⇒ 4).** Let `Ω` have no global fixed point and invariant mean `m`. Then
`1 = m(Ω \ Fix V) ≤ Σ_(s ∈ S) m(Ω \ Fix s)`, so some `s` has `m(Fix s) < 1`. Hence `s ∉ N_(V,Ω,m)`, and
`N_V ⊆ N_(V,Ω,m) ≠ V`.

**(4 ⇒ 2).** `N_V` is normal, and `V` is simple (S), so `N_V = 1`. Proposition 5.1(2) of (ES) gives
item 2.

**(2 ⇒ 1).** Let `(X, µ)` be essentially free and pick `s ∈ S`. Then `µ(Fix V) ≤ µ(Fix s) = 0`.
`X' = X \ Fix V` is invariant with `µ(X') = 1`, so `µ` restricted to `X'` is an invariant mean on a
`V`-set without global fixed points.

**(2 ⇒ 3).** Let `(X, µ)` be essentially free and `ε ∈ (0, 1/2)`.
- Theorem 3, (1) ⇒ (3), of (ES) gives a finite `F ⊆ X` with `|sF Δ F| < ε|F|` for `s ∈ S` and
  `|Fix(s) ∩ F| < ε|F|` for one fixed `s ∈ S`.
- Put `F' = F \ Fix V`, so `|F'| > (1-ε)|F|`. As `Fix V` is `s`-invariant,
  `sF' Δ F' = (sF Δ F) \ Fix V`.
- So `Σ_s |sF' \ F'| ≤ Σ_s |sF Δ F| < |S|ε|F| < 2|S|ε|F'|`.
- Split `F'` along the `V`-orbits `O` it meets. Each `s` preserves every orbit, so
  `Σ_O Σ_s |sF'_O \ F'_O| = Σ_s |sF' \ F'|` and `Σ_O |F'_O| = |F'|`. Some orbit therefore has
  `Σ_s |sF'_O \ F'_O| < 2|S|ε |F'_O|`.
- That orbit is `V/H` with `H` a point stabilizer. `H` is proper because `O ∩ Fix V = ∅`.

**(3 ⇒ 1).** Choose proper `H_n` and finite `P_n ⊆ V/H_n` with `Σ_s |sP_n \ P_n| < |P_n|/n`. Put
`Ω = ⊔_n V/H_n`, which has no global fixed point.
- Let `m` be a weak*-cluster point of the uniform averages `m_n` on `P_n`.
- For `s ∈ S` and `E ⊆ Ω`, `|m_n(1_(sE)) - m_n(1_E)| ≤ |s^-1 P_n Δ P_n| / |P_n| < 2/n`.
- So `m(1_(sE)) = m(1_E)`, and since `S` generates `V`, `m` is invariant.

**Soficity.** By item 4 and simplicity, `N_V = 1`. Proposition 5.1(3) of (ES) says that `V/N_V = V` is
sofic. ∎

*Remarks.*
- No character theory is used in Theorem 1.
- Item 3 is a single-orbit form. By Kazhdan's trick (Tucker-Drob §0.B), an amenable action without
  global fixed points exists iff there are almost-invariant finite sets on single orbits `V/H`, `H`
  proper.
- Item 3 does not say that some proper `H` is co-amenable.

## 2. The individual dichotomy: every invariant mean is free off the fixed set

**Theorem 2.** Let `Ω` be a `V`-set with invariant mean `m`, and put `b = m(Fix V)`.
1. `m(Fix g) = b` for every `g ≠ e`. Equivalently, `m(Fix g \ Fix V) = 0`.
2. The stabilizer IRS `ν_m` below equals `(1-b)δ_({e}) + bδ_V`.
3. If `b < 1`, the normalized restriction of `m` to `Ω \ Fix V` is an essentially free amenable action.

*Proof.*

**The stabilizer measure.**
- `Sub(V) ⊆ {0,1}^V` is compact, metrizable and zero-dimensional. Its clopen algebra is generated by
  `U_g = {K : g ∈ K}`.
- For a clopen `E`, the set `{x : Stab(x) ∈ E}` is the same finite Boolean combination of sets
  `Fix(g)`. So `ν_0(E) = m({x : Stab(x) ∈ E})` is a finitely additive probability on the clopen algebra.
- If a clopen set is a countable disjoint union of nonempty clopen sets, compactness makes the union
  finite. So `ν_0` is countably additive on the algebra.
- The algebra generates the Borel σ-algebra, so Carathéodory's theorem extends `ν_0` uniquely to a
  Borel probability `ν_m`.

**Conjugation invariance.**
- `{x : Stab(x) ∈ gEg^-1} = {x : Stab(g^-1 x) ∈ E} = g{x' : Stab(x') ∈ E}`, so invariance of `m` gives
  `ν_0(gEg^-1) = ν_0(E)`.
- Two Borel measures that agree on the generating algebra agree everywhere. So `ν_m` is an IRS.

**Rigidity.**
- (IRS) gives `ν_m = (1-b')δ_({e}) + b'δ_V` for some `b'`.
- `{V} = ⋂_(s ∈ S) U_s` is clopen, because a subgroup containing `S` is `V`. So
  `b' = ν_0({V}) = m(⋂_s Fix s) = m(Fix V) = b`.
- For `g ≠ e`, `m(Fix g) = ν_0(U_g) = b`. Since `Fix V ⊆ Fix g`, `m(Fix g \ Fix V) = 0`.

**Item 3.** `Ω \ Fix V` is invariant with mass `1 - b > 0`. The normalized restriction `m'` is invariant
and `m'(Fix g) = m(Fix g \ Fix V)/(1-b) = 0` for `g ≠ e`. ∎

*Remarks.*
- Theorem 2 strengthens Theorem 1 from "some action" to "every invariant mean". It is the V-analogue of
  the main statement (AF2) of `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`, with
  finitely additive means in place of finite permutation almost actions. (Referee 2026-09-16: this
  pointer previously said "item 3", which is the free-local-charts item there.)
- It is used below only through `m(Fix g \ Fix V) = 0`.

**Corollary 2.1 (confining sets).** For every finite `P ⊆ V \ {e}`,
`m({x ∉ Fix V : Stab(x) ∩ P ≠ ∅}) ≤ Σ_(p ∈ P) m(Fix p \ Fix V) = 0`.
- *Confined subgroups.* A proper `H < V` is *confined by `P`* if every conjugate of `H` meets `P`. Such
  an `H` is not co-amenable. On `V/H` every point has a stabilizer meeting `P`, and no point is fixed by
  `V`, so an invariant mean on `V/H` would have total mass 0.

## 3. Stabilizers that fix a mean on a non-amenable V-set

**Theorem 3 (transfer).** Let `G` be any group and `Ω` a `G`-set with invariant mean `m`. Let `Y` be a
`G`-set and `𝒜` a `G`-invariant algebra of subsets of `Y` that carries no `G`-invariant finitely
additive probability. Let `Ω_0` be the set of `x` such that `Stab(x)` fixes some finitely additive
probability on `𝒜`. Then `m(Ω_0) = 0`.

*Proof.*
- For a finitely additive probability `λ`, put `(g_*λ)(E) = λ(g^-1 E)`. If `Stab(x)` fixes `λ`, then
  `Stab(gx)` fixes `g_*λ`, so `Ω_0` is invariant.
- In each orbit `O ⊆ Ω_0` choose a representative `x_O` and a `Stab(x_O)`-fixed `λ_O`, and put
  `λ_(g x_O) = g_*λ_O`. This is well defined: if `g x_O = g' x_O`, then `g^-1 g'` fixes `λ_O`. It gives
  `λ_(gx) = g_*λ_x` on `Ω_0`.
- Suppose `t = m(Ω_0) > 0`. Put `Λ(E) = t^-1 m(f_E)` with `f_E(x) = 1_(Ω_0)(x) λ_x(E)`.
  - `Λ` is finitely additive and `Λ(Y) = 1`.
  - `f_(gE)(x) = 1_(Ω_0)(x) λ_(g^-1 x)(E) = f_E(g^-1 x)`, so `Λ(gE) = Λ(E)`.
  - This contradicts the hypothesis on `𝒜`. ∎

**Corollary 3.1 (the family 𝓜).** Let `𝓜` be the set of subgroups of `V` that fix a Borel probability
measure on `C`. For every invariant mean on every `V`-set, `{x : Stab(x) ∈ 𝓜}` is null.
- *Proof.* Take `Y = C` and `𝒜` the clopen algebra, and apply (H).
- *Members.* `𝓜` is closed under conjugation and under passing to subgroups. It contains:
  - every amenable subgroup, since an amenable group acting on a compact space fixes a Borel
    probability;
  - every subgroup with a finite orbit on `C`, through the uniform measure on the orbit. This covers
    point stabilizers, pointwise and setwise stabilizers of finite subsets of `C`, and `F`;
  - every subgroup preserving the uniform Bernoulli measure.
- *Consequence.* No subgroup in `𝓜` is co-amenable in `V`, and `V`-sets of finite configurations in
  `C` carry no invariant mean, however large the configurations. This contrasts with Thompson's `F`,
  where configurations meeting every interval are one surviving witness shape
  (`thompson-f-mean-free-actions-dense-configurations-or-unconfined`, item 2(I)).
- *Other choices.* With `Y = V` and `𝒜` all subsets, Theorem 3 is item 4 of
  `mean-free-amenable-actions-residually-amenable-and-sofic` (amenable stabilizers are null).

## 4. Rigid covers

For `x ∈ Ω` put

```text
𝒲(x) = { cones W : V_W ≤ Stab(x) },
O(x) = ⋃ { clopen U : V_U ≤ Stab(x) } = ⋃ 𝒲(x),
S_n  = { x : some [w] ∈ 𝒲(x) has |w| ≤ n },
Ω_𝒞  = { x ∉ Fix V : O(x) = C }.
```

- The second equality in `O(x)` holds because a clopen `U` is a finite union of cones `W ⊆ U`, and
  `V_W ≤ V_U`.
- `O(gx) = gO(x)`, since `V_(gU) = g V_U g^-1`. So `Ω_𝒞` is invariant.
- By compactness, `x ∈ Ω_𝒞` iff `Stab(x)` is proper and contains `V_(U_1), ..., V_(U_k)` for some finite
  clopen partition `{U_i}` of `C`. Call the family of such proper subgroups `𝓒`. It is closed under
  conjugation.
- `𝓒` contains the setwise stabilizer of every proper nonempty clopen set, and the stabilizer of every
  finite clopen partition with at least two pieces.

**Lemma 4.0.** `m(S_n \ Fix V) = 0` for every `n`.

*Proof.* `S_n ⊆ ⋃_(|w| ≤ n) Fix(h_w)`, which is a finite union. Apply Theorem 2.1. ∎

**Lemma 4.1 (partition).** For `x ∈ Ω_𝒞`, let `P(x)` be the set of maximal elements of `𝒲(x)`. Then
`P(x)` is a finite partition of `C` into cones.

*Proof.*
- **Maximal elements above every member.** `C ∉ 𝒲(x)`, because `V_C = V` and `x ∉ Fix V`. The cones
  containing `[w]` are the `[w_0]` for prefixes `w_0` of `w`. The shortest such prefix with
  `[w_0] ∈ 𝒲(x)` gives a maximal element containing `[w]`.
- **Disjoint.** Two cones that meet are nested, so distinct maximal elements are disjoint.
- **Cover.** They cover `O(x) = C`.
- **Finite.** A cover of the compact `C` by disjoint open sets is finite. ∎

**Lemma 4.2 (cones to cones).** Let `g` have depth ≤ `d`, witnessed by `u_i ↦ v_i`, and let
`|w| ≥ d`. Then `w = u_i w'` for a unique `i`, and `g[w] = [v_i w']` with `|v_i w'| ≤ |w| + d`.

*Proof.* Every sequence with prefix `w` has a unique `u_i` as a prefix, and `|u_i| ≤ d ≤ |w|` forces
`u_i` to be a prefix of `w`. ∎

**Lemma 4.3.** If `g` has depth ≤ `d` and `x ∉ S_(2d)`, then `gx ∉ S_d`.

*Proof.*
- Suppose `[w] ∈ 𝒲(gx)` with `|w| ≤ d`. Extend `w` to a word `wz` of length exactly `d`.
- `g^-1` has depth ≤ `d`, so Lemma 4.2 makes `g^-1[wz]` a cone `[y]` with `|y| ≤ 2d`.
- `[y] ⊆ g^-1[w]`, so `V_[y] ≤ V_(g^-1[w]) = g^-1 V_[w] g ≤ Stab(x)`. Hence `x ∈ S_(2d)`, a
  contradiction. ∎

**Lemma 4.4 (equivariance).** If `g` has depth ≤ `d` and `x ∈ Ω_𝒞 \ S_(2d)`, then `P(gx) = gP(x)`.

*Proof.* Let `W = [w] ∈ P(x)`.
- **gW lies in 𝒲(gx).** `|w| > 2d ≥ d` because `x ∉ S_(2d)`. So `gW` is a cone (Lemma 4.2), and
  `V_(gW) = g V_W g^-1 ≤ Stab(gx)`.
- **gW is maximal.** Suppose `gW ⊊ [z] ∈ 𝒲(gx)`.
  - By Lemma 4.3, `gx ∉ S_d`, so `|z| > d`.
  - Then `g^-1[z]` is a cone (Lemma 4.2, applied to `g^-1`) that strictly contains `W`, and
    `V_(g^-1[z]) ≤ Stab(x)`. This contradicts maximality of `W`.
- **Conclusion.** `gP(x) ⊆ P(gx)`. Both are partitions of `C`, so they are equal. ∎

**Lemma 4.5 (additivity).** Let `𝒜_n` be the finite algebra of unions of cones of length `n`. For
`x ∈ Ω_𝒞` and clopen `E`, put `ν_x(E) = #{W ∈ P(x) : W ⊆ E} / |P(x)|`. If `x ∉ S_n`, then `ν_x` is
additive on `𝒜_n` and `ν_x(C) = 1`.

*Proof.* Every `W ∈ P(x)` has length `> n`, so it lies inside one cone of length `n`. Hence for `E ∈ 𝒜_n`
either `W ⊆ E` or `W ∩ E = ∅`, and counting is additive. ∎

**Theorem 4.** For every invariant mean on every `V`-set, `m(Ω_𝒞) = 0`. That is, `{x : Stab(x) ∈ 𝓒}`
is null.

*Proof.* Suppose `t = m(Ω_𝒞) > 0`. For clopen `E` put `λ(E) = t^-1 m(1_(Ω_𝒞)(x) ν_x(E))`.
- **Finite additivity.** Let `E, E'` be disjoint in `𝒜_n`. The function
  `1_(Ω_𝒞)(x)(ν_x(E ∪ E') - ν_x(E) - ν_x(E'))` is bounded by 2 and vanishes off `S_n` (Lemma 4.5). By
  Lemma 4.0 its mean is 0. Every pair of disjoint clopen sets lies in some `𝒜_n`, so `λ` is finitely
  additive on clopen sets, and `λ(C) = 1`.
- **Invariance.** Let `g` have depth ≤ `d`, let `E` be clopen, and let `x ∈ Ω_𝒞 \ S_(2d)`. By
  Lemma 4.4,
  `ν_(gx)(gE) = #{gW : W ∈ P(x), gW ⊆ gE} / |P(x)| = ν_x(E)`.
  - So `f(x) = 1_(Ω_𝒞)(x) ν_x(gE)` satisfies `f(gx) = 1_(Ω_𝒞)(x) ν_x(E)` off `S_(2d) ∩ Ω_𝒞`, which is
    null by Lemma 4.0.
  - Hence `λ(gE) = t^-1 m(f) = t^-1 m(f∘g) = λ(E)`.
- **Contradiction.** `λ` is a `V`-invariant finitely additive probability on clopen sets, contradicting
  (H). ∎

## 5. Uniform isoperimetric bounds

**Theorem 5.** There is `c = c_S > 0`, and for each finite `P ⊆ V \ {e}` a `c_P > 0`, with the following
property. Let `H < V` be proper and `H ≤ K` with `K` in `𝓜 ∪ 𝓒`, or `K` proper and confined by `P`.
Then `φ_S(V/H) ≥ c`, respectively `≥ c_P`.

*Proof.*
- **Setup.** Suppose `H_n ≤ K_n` with `φ_S(V/H_n) → 0`, all `K_n` in one of the families. As in
  (3 ⇒ 1) of Theorem 1, `⊔_n V/H_n` carries an invariant mean.
- **Push forward.** The equivariant map `gH_n ↦ gK_n` pushes it to an invariant mean on
  `Ω' = ⊔_n V/K_n`.
- **Stabilizers in Ω'.** Every point of `Ω'` has a stabilizer conjugate to some `K_n`, so it lies in the
  same conjugation-invariant family. In the confined case no point of `Ω'` is fixed by `V` and every
  stabilizer meets `P`.
- **Contradiction.** Corollary 3.1, Theorem 4 and Corollary 2.1 make `Ω'` null. ∎

## 6. A density principle and the invariant clopen algebra

**Theorem 6 (density).** Let `x ↦ K(x) ⊆ C` be any map on a `V`-set with `K(gx) = gK(x)`. For every
proper clopen `U`, `m({x : ∅ ≠ K(x) ⊆ U}) = 0`. Hence for each `n`, `m`-almost every `x` has `K(x)`
empty or meeting every cone of length `n`.

*Proof.*
- **Constant on proper clopens.** Put `f(U) = m({x : ∅ ≠ K(x) ⊆ U})`. Then
  `{x : ∅ ≠ K(x) ⊆ gU} = g{x : ∅ ≠ K(x) ⊆ U}`, so `f(gU) = f(U)`. By (Tr), `f` is a constant `c` on
  proper nonempty clopen sets, and `f(∅) = 0`.
- **The constant is zero.** `{K ≠ ∅, K ⊆ [00]}` and `{K ≠ ∅, K ⊆ [01]}` are disjoint subsets of
  `{K ≠ ∅, K ⊆ [0]}`. So `2c ≤ c` and `c = 0`.
- **Second statement.** Take the finitely many `U = C \ [w]` with `|w| = n`. ∎

**Corollary 6.1 (no shallow rigid pieces).** For each `n`, `m`-almost every `x ∉ Fix V` has no cone of
length ≤ `n` contained in `O(x)`.

*Proof.* Apply Theorem 6 to `K(x) = C \ O(x)`. If `[w] ⊆ O(x)` with `|w| ≤ n`, then `K(x)` is empty,
which is null off `Fix V` by Theorem 4, or `K(x)` is a nonempty subset of `C \ [w]`. Finitely many `w`
are involved. ∎

**Corollary 6.2 (the invariant clopen algebra).** Let `B(x)` be the algebra of clopen sets `E` with
`hE = E` for all `h ∈ Stab(x)`. The set `Ω_B = {x : B(x) is finite with at least two atoms}` is null.

*Proof.*
- `B(gx) = gB(x)`. Let `π(x)` be the partition into atoms of `B(x)`. It is an equivariant map from
  `Ω_B` to the `V`-set `Y` of finite clopen partitions of `C` with at least two pieces.
- If `m(Ω_B) > 0`, then `E ↦ m(Ω_B ∩ π^-1 E) / m(Ω_B)` is an invariant mean on `Y`.
- Every stabilizer in `Y` is proper, since `V` moves every such partition, and contains the rigid
  stabilizers of the pieces. So it is in `𝓒`.
- Theorem 4 then makes `Y` null, a contradiction. There is no bound on the number of atoms. ∎

## 7. What survives

**Shape of a witness.** Let `m` be an invariant mean on a `V`-set with `m(Fix V) = 0`, as in item 1 of
Theorem 1. By the results above, `m`-almost every stabilizer `H = Stab(x)`:
- contains no element of any prescribed finite subset of `V \ {e}` (Corollary 2.1);
- fixes no Borel probability measure on `C` (Corollary 3.1); in particular it is non-amenable, has no
  finite orbit on `C`, and fixes no point of `C`;
- is not contained in a proper subgroup containing a rigid cover (Theorem 4 and push-forward). In
  particular it permutes the pieces of no finite clopen partition with at least two pieces. The
  push-forward: let `Ω_1` be the set of `x` with `Stab(x) ≤ K` for some `K ∈ 𝓒`, and choose one such
  `K_x` per orbit, at a representative `x_0`, transported by `K_(g x_0) = g K_(x_0) g^-1`. The map
  `g x_0 ↦ g K_(x_0)` from `V·x_0` to `V/K_(x_0)` is well defined because `Stab(x_0) ≤ K_(x_0)`, and it is
  equivariant. Pushing `m` restricted to `Ω_1` forward along these maps gives an invariant mean of mass
  `m(Ω_1)` on `⊔ V/K_(x_0)`, where every stabilizer is a conjugate of some `K_(x_0)`, so lies in `𝓒`.
  Theorem 4 makes that set null, so `m(Ω_1) = 0`;
- has an invariant clopen algebra that is trivial or infinite (Corollary 6.2);
- for each `n`, contains no `V_U` with `U` containing a cone of length ≤ `n` (Corollary 6.1);
- is wq*-normal in `V`. This is Tucker-Drob arXiv:1407.7474v3, Theorem 1, verbatim: "Let G be a
  finitely generated nonamenable group. Assume that G acts amenably on X and fix a G-invariant mean m on
  X. Then G_x is wq∗-normal in G for m-almost every x ∈ X." It is an imported statement and is not
  reproved here.

For a single orbit, co-amenability of `H` passes to every overgroup. So the co-amenable candidates are
the proper subgroups outside the downward closures of `𝓜`, `𝓒` and the confined subgroups.

**Where each approach dies.**
1. *Point, configuration and measure stabilizers.* These are dead by Corollary 3.1.
2. *Clopen and partition stabilizers, and subgroups with a rigid cover.* Dead by Theorem 4.
3. *Confined subgroups.* Dead by Corollary 2.1, with a uniform constant for each confining set.
   - The union over all confining sets is not controlled, because means are only finitely additive.
   - No classification of confined subgroups of `V` was imported. Le Boudec–Matte Bon arXiv:2012.03997v2
     was read on 2026-09-16 only for its `V_d` section (Proposition 5.2, Remark 5.3, Lemma 5.6,
     Theorem 5.5), which concerns highly transitive actions, not co-amenability. The numbering was taken
     from the arXiv source; the published numbering is unverified.
4. *Subgroups containing some rigid stabilizer.* Let `H` contain `V_U` for a proper nonempty clopen `U`,
   and put `O(H) = ⋃{U : V_U ≤ H}`.
   - If `O(H)` is clopen, then `H ≤ Stab_V(O(H))`, which lies in `𝓒` or equals `V`.
   - So a survivor has `O(H)` open and not closed, and the closed `H`-invariant set `K(H) = C \ O(H)`
     carries no `H`-invariant probability.
   - Theorem 6 forces the translates `gK(H)` to be dense at every fixed scale for typical `g`. This is no
     contradiction for a finitely additive mean.
5. *Thompson's T.* `T` is the subgroup of `V` preserving the cyclic order induced by
   `C → R/Z`. It is the natural test case, and it is undecided here.
   - **Not in 𝓜.** A `T`-invariant Borel probability on `C` pushes forward to one on the circle. Every
     `F`-invariant probability on `[0,1]` is carried by `{0,1}`, and `T` contains the dyadic rotations,
     so none exists.
   - **Contains no rigid stabilizer.** The swap of `[w00]` and `[w01]` reverses the order of two adjacent
     arcs, so it is not in `T`. `V_[w]` contains that swap, so `T` contains no `V_U`.
   - **Preserves no nontrivial finite clopen partition.** `T` is simple and acts minimally on the circle,
     so it would have to fix each piece.
   - **Lies below no member of `𝓜` or `𝓒`** (referee addition, 2026-09-16). `𝓜` is closed under
     subgroups, so this part is the "Not in 𝓜" item. For `𝓒`, suppose `T ≤ K` with `K` containing
     `V_(U_1)`. Then `U_1` contains a cone `[w]`, so `V_[w] ≤ K`.
     - `T` is transitive on proper arcs with dyadic endpoints, using rotations and the order-transitivity
       of `F` on dyadic rationals. Every cone and the complement of every cone is such an arc. So `K`
       contains `V_A` for every proper dyadic arc `A`.
     - Every proper clopen `U` misses some cone `[z]`, so `U ⊆ C \ [z]`, which is a proper dyadic arc, and
       `V_U ≤ K`.
     - The subgroup generated by all `V_U` with `U` proper clopen is normal, since `g V_U g^-1 = V_(gU)`,
       and nontrivial. By simplicity it is `V`. So `K = V`, and `K ∉ 𝓒`.

     So none of Corollary 3.1, Theorem 4 or item 4 above applies to `T`. Confinement is the one
     exclusion not decided for `T`.
   - **Open.** Whether `T` is confined, and whether `φ_S(V/T) = 0`, remain open.

**Barrier (from Theorem 1).**
- Refuting item 1 of Theorem 1 would prove `N_V = V`: every invariant mean on every `V`-set lives on
  global fixed points. That says nothing about non-soficity, because `N_V = V` is compatible with `V`
  being sofic.
- Proving item 1 proves `thompson-v-is-sofic`.
- So the reduction is one-directional. It is not an equivalence with soficity.

## 8. Literature gate (2026-09-16)

Queries went to the arXiv API (`export.arxiv.org/api/query`) on 2026-09-16. They covered titles and
abstracts combining Thompson / Higman–Thompson with sofic, hyperlinear, amenable action, invariant mean,
co-amenable, and confined subgroups.

- No source found proves or refutes soficity of `V`.
- No source found gives a proper co-amenable subgroup of `V`, or an essentially free amenable action of
  `V`.
- Since the web search budget was exhausted, this gate is limited to arXiv.

Read:
- **Elek–Szabó, arXiv:math/0408400.** As pinned in `elek-szabo-essentially-free-amenable-actions`.
- **Tucker-Drob, arXiv:1407.7474v3.** Abstract, introduction, Theorem 1, §0.B and Theorem 3, read from the
  arXiv PDF on 2026-09-16.
- **Le Boudec–Matte Bon, arXiv:2012.03997v2.** Abstract, introduction and §5.1–5.2, read from the arXiv
  PDF on 2026-09-16.
- **Glasner–Monod, arXiv:math/0505197v1.** Only page 1 was extracted: Definition 1.1 (invariant mean,
  amenable action) and the motivation for faithful transitive actions. Later statements, including the
  exact name of their class of groups, are unverified here.
- **Abstracts only.** Azuelos–Gaboriau arXiv:2308.05954, Kahl–Schneider arXiv:2504.10988v3 and
  Bartholdi arXiv:1705.04091. They were checked for relevance and do not bear on the statements above.
