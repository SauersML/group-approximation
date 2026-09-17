# Derived-read double counts: arbitrary (including linear) reads and approximate laws still force soficity

Lane swarm-0917-w5-gs-rokhlin-kazhdan, 2026-09-17. Target: `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`.

## 0. Purpose

The established node `reading-model-entropy-certificates-are-soficity` (artifact
`research/artifacts/reading-model-certificates-force-soficity-2026-09-17.md`, cited below as RM) shows that the
Gromov--Weiss double count run on any finite reading model certifies `Phi >= log q` for all configurations exactly
on sofic groups. Its Section 5 lists what the class does not contain:
- linear or rank models (dimension counts over a field);
- non-product label measures.

This artifact widens the class to **derived-read models**. These have an arbitrary probability space, and codes
read arbitrary finite-valued random variables: coordinates, linear functionals, nonlinear functions, or functions
using extra randomness. Laws at good sites only need to be close in total variation. The result is the same
dichotomy, with the same death step. The unit incidences `g^-1 g = 1` pin every read of a tight model to one site
variable, and the pinned model is a reading model to which RM Lemma B applies verbatim.

What remains outside is stated precisely in Section 6.

## 1. Setting

- `K` is a nontrivial finitely generated group, with finite symmetric generating set `S`, `1 ∈ S`, ball `B_r`, and
  `b = |B_r|`. So `b >= 2` for `r >= 1`.
- A configuration is `c = (k, E, F, psi)` as in `bernoulli-rokhlin-deficit-has-a-finitary-witness`.
  - `psi : (A^k)^E -> R` with `R` finite, and `|A| = q >= 2`.
  - The pattern is `P = FE ∪ {1}`, and `Y = psi(x|_E)` for `x` iid uniform on `A^k` over `K`.
  - `k Phi(c) = H(Y) + H(x(1) | Y_F)`, where `Y_f = psi((x(fe))_{e in E})`.
- TV distance is `d(P,Q) = sup_B |P(B) - Q(B)|`.
- Continuity of entropy (classical Fannes--Audenaert bound). If `d(P,Q) <= t <= 1/2` on a finite set `X`, then
  `|H(P) - H(Q)| <= t log |X| + h(t)`, where `h` is the binary entropy.

## 2. Derived-read models and the certificate

**Definition.** A derived-read model of `(E,F)` with tolerance `epsilon` consists of the following finite data.
- A probability space `Omega`.
- A finite index set `I` of sites and random variables `Z_i : Omega -> A^k` for `i` in `I`.
- A finite set `U` of codes, with random variables `v_{u,e} : Omega -> A^k` for `u` in `U` and `e` in `E` (the
  reads), and code variables `C_u = psi((v_{u,e})_{e in E})`.
- Maps `sigma_f : I -> U` for `f` in `F`.
- A nonempty set `V ⊆ I` of good sites such that:
  - (independence) `(Z_i)_{i in V}` is iid uniform on `A^k`;
  - (local law) for each `i` in `V`, the law of `(Z_i, (v_{sigma_f(i), e})_{f in F, e in E})` is within TV
    `epsilon` of the law of `(x(1), (x(fe))_{f in F, e in E})` for `x` iid uniform over `K`.

Put `N' = sigma_F(V)` and `mu = |N'| / |V|`.

Nothing else is constrained. Reads may be coordinates, linear functionals of a vector, arbitrary functions of the
sites, or functions of extra randomness. Sites outside `V` need not be independent, and `sigma_f` need not be
injective or related to anything.

Examples:
- A reading model (RM Section 1) gives one with `epsilon = 0`. Take `Omega` iid over `M`, `Z_i = x_i`,
  `v_{u,e} = x_{tau_e(u)}` and `V = M_g`. Injectivity of charts gives the exact local law.
- A linear double count gives one. Let `A = F_q`, `k = 1` and `Omega = F_q^n`, uniform. Sites are linear functionals
  that are linearly independent on `V`, so they are iid uniform there, and reads are arbitrary linear functionals.
  The local law is exact iff the functionals `(Z_i, v_{sigma_f(i),e})` satisfy exactly the linear relations
  `x(fe) = x(f'e')` of the pattern. A tuple of linear functionals is uniform on its image, so its law is either
  exactly right or at TV distance at least `1/2` from the right one.

**Lemma A'.** Let `X_F = A^k × R^F`, and put `delta(epsilon) = 2 (epsilon log |X_F| + h(epsilon))` for
`epsilon <= 1/2`. For every derived-read model,

    k Phi(c) >= k log q - (mu - 1) H(Y) - (mu + 1) delta(epsilon).

*Proof.*
1. **Code laws.** Take `u = sigma_f(i)` with `i` in `V`. The law of `(v_{u,e})_{e in E}` is a marginal of the local
   law at `i`, so it is within TV `epsilon` of the law of `(x(fe))_{e in E}`. That is iid uniform because `e -> fe`
   is injective. Pushing forward by `psi` does not increase TV, and `R` has at most `|X_F|` elements, so
   `H(C_u) <= H(Y) + delta/2`.
2. **Site laws.** For `i` in `V`, the pair `(Z_i, C_{sigma_F(i)})` is a function of the local tuple. Its law is
   within TV `epsilon` of that of `(x(1), Y_F)` on `X_F`, and so is the law of the second coordinate. Writing
   `H(Z | C) = H(Z, C) - H(C)` gives `H(Z_i | C_{sigma_F(i)}) <= H(x(1) | Y_F) + delta`.
3. **Count.** By independence on `V`, the chain rule and subadditivity,

       |V| k log q = H(Z_V) <= H(C_{N'}) + H(Z_V | C_{N'})
                   <= sum_{u in N'} H(C_u) + sum_{i in V} H(Z_i | C_{sigma_F(i)})
                   <= |N'| (H(Y) + delta) + |V| (H(x(1)|Y_F) + delta).

   Divide by `|V|`, and use `H(x(1)|Y_F) = k Phi - H(Y)`. ∎

For `epsilon = 0` this is RM Lemma A. The reads enter only through laws, so the count sees nothing linear or
nonlinear about them.

## 3. Pinning: tight derived-read models are reading models

**Lemma P (pinning and reduction).** Let `B_r ⊆ E ∩ F` with `r >= 1`, and take a derived-read model with
`epsilon < 1/6` and ratio `mu`. Then:
1. `sigma_g` is injective on `V` for every `g` in `B_r`, so `mu >= 1`;
2. if `b^2 (mu - 1) < 1`, there is a reading model `R` of `(B_r, B_r)` (RM Section 1) whose good sites are a set
   `V_R ⊆ V` with `|V_R| >= (1 - b^2 (mu - 1)) |V|`, and whose ratio is

       mu_R <= mu / (1 - b^2 (mu - 1)).

*Proof.* Restricting reads to `e` in `B_r` and maps to `f` in `B_r` gives a derived-read model of `(B_r, B_r)`. It
has the same `V` and tolerance, and its ratio `mu_0` is at most `mu`, since its codes are `sigma_{B_r}(V) ⊆ N'`.
Build `R` from this restricted model. All bounds below are increasing in the ratio, so they hold with `mu` in place
of `mu_0`. From now on `E = F = B_r` and `N' = sigma_{B_r}(V)`.

Two facts about independent uniform variables are used throughout:
- for distinct `i, i'` in `V`, `P(Z_i = Z_{i'}) = q^-k <= 1/2`;
- for `fe ≠ f'e'` in `P`, `P(x(fe) = x(f'e')) = q^-k <= 1/2`.

1. **Pinning.** Let `i` be in `V` and `g` in `B_r`. The pair `(f, e) = (g^-1, g)` has `fe = 1`, so the local law
   gives

       P( v_{sigma_{g^-1}(i), g} = Z_i ) >= 1 - epsilon.                                   (pin)

   If `sigma_{g^-1}(i) = sigma_{g^-1}(i') = u` with `i ≠ i'` in `V`, then `P(Z_i = Z_{i'}) >= 1 - 2 epsilon > 1/2`,
   a contradiction. As `g` runs over `B_r`, so does `g^-1`, and part 1 follows. Taking `g = 1` gives `|N'| >= |V|`.
2. **Read-back maps.** For `u` in `U` and `e` in `B_r`, if `u ∈ sigma_{e^-1}(V)`, let `tau_e(u)` be the unique
   `j` in `V` with `sigma_{e^-1}(j) = u`. By (pin) at `j`,

       P( v_{u,e} = Z_{tau_e(u)} ) >= 1 - epsilon.                                         (read)

3. **Full codes.** Let `N'' = N' ∩ ⋂_{g in B_r} sigma_{g^-1}(V)`. By part 1, `|sigma_{g^-1}(V)| = |V|`, so
   `|N' \ sigma_{g^-1}(V)| = (mu_0 - 1)|V|` and `|N' \ N''| <= b (mu_0 - 1) |V|`.
   Let `V_R = { i in V : sigma_f(i) ∈ N'' for all f in B_r }`. Each `sigma_f` is injective on `V`, so
   `|V \ V_R| <= b · b (mu_0 - 1)|V|`.
4. **The reading model `R`.**
   - Sites: `M = I ∪ {∞}`. Codes: `N = U ∪ {⊥}`.
   - `sigma_f` is the given map on `I`, and `sigma_f(∞) = ⊥`.
   - `tau_e(u)` is as in part 2 for `u` in `N''`, and `tau_e(u) = ∞` otherwise (including `u = ⊥`).
5. **Sites of `V_R` are good in `R`.** Let `i` be in `V_R` and put `c_i(fe) = tau_e(sigma_f(i))` for `f, e` in `B_r`.
   All these codes lie in `N''`, so `c_i` takes values in `V`. For `f, e` in `B_r` write `j(f,e) = tau_e(sigma_f(i))`.
   By (read), `P(v_{sigma_f(i),e} = Z_{j(f,e)}) >= 1 - epsilon`.
   - *Unit.* If `fe = 1` then `f = e^-1`, and `j(e^-1, e) = i` by uniqueness in part 2. So `c_i(1) = i`.
   - *Well-defined.* Let `fe = f'e'`. The local law at `i` gives
     `P(v_{sigma_f(i),e} = v_{sigma_{f'}(i),e'}) >= 1 - epsilon`. Combining this with (read) twice gives
     `P(Z_{j(f,e)} = Z_{j(f',e')}) >= 1 - 3 epsilon > 1/2`. Both indices lie in `V`, so `j(f,e) = j(f',e')`.
   - *Injective.* Let `fe ≠ f'e'`. The local law gives `P(v_{sigma_f(i),e} = v_{sigma_{f'}(i),e'}) <= 1/2 + epsilon`.
     If `j(f,e) = j(f',e')`, then (read) twice gives `P(v_{sigma_f(i),e} = v_{sigma_{f'}(i),e'}) >= 1 - 2 epsilon`.
     That exceeds `1/2 + epsilon` because `epsilon < 1/6`, so `j(f,e) ≠ j(f',e')`.

   So `c_i` is a well-defined injective map on `B_r B_r = P` with `c_i(1) = i` and `c_i(fe) = tau_e(sigma_f(i))`.
   That is, `i` is good in `R`.
6. **No other site is good in `R`.**
   - `∞` is not good. Since `sigma_1(∞) = ⊥` and `tau_e(⊥) = ∞`, its chart would send the distinct points `e ≠ e'` of
     `B_r` (`b >= 2`) to the same point.
   - A site `i` with some `sigma_f(i) ∉ N''` is not good for the same reason, since `tau_e(sigma_f(i)) = ∞` for every `e`.
   - Take `i` not in `V` with all `sigma_f(i)` in `N''`. Then `tau_1(sigma_1(i))` is the unique `j` in `V` with
     `sigma_1(j) = sigma_1(i)`, so `j ≠ i`. But goodness needs `tau_1(sigma_1(i)) = c_i(1) = i`.

   Hence the good set of `R` is exactly `V_R`. Its codes are `sigma_{B_r}(V_R) ⊆ N'`, so
   `mu_R <= |N'| / |V_R| <= mu_0 / (1 - b^2 (mu_0 - 1))`. ∎

**Corollary P.** Let `B_r ⊆ E ∩ F`, and take a derived-read model with `epsilon < 1/6` and `b^2(mu - 1) < 1`. Then
`K` has an `(r, (1 + b) b^2 (mu_R - 1))`-sofic approximation, with `mu_R <= mu / (1 - b^2 (mu - 1))`.

*Proof.* Apply RM Lemma B, part of the established `reading-model-entropy-certificates-are-soficity`, to the reading
model `R` of `(B_r, B_r)`. Its good set is `V_R ≠ ∅`. ∎

## 4. Theorem and obstruction

**Theorem D.** For a nontrivial finitely generated group `K` the following are equivalent:
1. `K` is sofic;
2. for every `r` and `eta > 0`, some derived-read model of `(B_r, B_r)` has `epsilon <= eta` and `mu <= 1 + eta`;
3. Lemma A' certifies `Phi(c) >= log q` for every configuration `c` of `K`, in the sense of RM Theorem. Some
   extension `c' = (k, E', F', psi ∘ restriction)` with `E' ⊇ E` and `F' ⊇ F` (so `Phi(c') <= Phi(c)`) has supremum `k log q` for the right-hand side of
   Lemma A' over derived-read models of its pattern.

Models with `epsilon > 1/2` are excluded, since Lemma A' is stated for `epsilon <= 1/2`.

*Proof.*
- `1 => 3`. Reading models are derived-read models with `epsilon = 0` and `delta(0) = 0`, as in Section 2, and for
  them Lemma A' is RM Lemma A. RM Theorem (`1 => 3`) says reading models certify every configuration of a sofic
  group.
- `3 => 2`. Take `c = (1, B_r, B_r, x -> x(1))`, so `H(Y) = log q > 0`, and let `c'` be the extension from `3`. Its
  `Y` is the same, since `psi` factors through restriction. A right-hand side close to `k log q` for a model of `c'`
  needs `(mu - 1) H(Y) + (mu + 1) delta(epsilon)` close to `0`. The restriction remark then passes to
  `(B_r, B_r)`, with ratio at most `mu` and at least `1` by Lemma P.
  - If `epsilon >= 1/6`, then `delta >= 2 h(1/6) > 0`, so it is not close to `0`.
  - If `epsilon < 1/6`, then `mu >= 1` by Lemma P, so both terms are nonnegative. Both must be small, so `mu -> 1`,
    and `epsilon -> 0` because `delta(epsilon) >= 2 h(epsilon)`.
- `2 => 1`. By Corollary P, as `mu -> 1` with `epsilon < 1/6`. ∎

**Restriction remark.** A derived-read model of `(E', F') ⊇ (E, F)` with good set `V` and tolerance `epsilon` gives
one of `(E, F)` with the same `V`, tolerance at most `epsilon`, and ratio at most as large. Drop the unused reads and
maps. The local law restricts to a marginal, and TV does not increase under marginals.

This is used below for a host `G ⊇ K`. A configuration on `G` with `B^K_{r_0} ⊆ E ∩ F` restricts to the pattern
`(B^K_{r_0}, B^K_{r_0})`, whose law is computed inside `K`.

**Obstruction.** Let `K` be nonsofic, for example `EL_D(R) <= L_(F_2)(1,2)^x` of `openai-leavitt-unit-nonsofic`,
contained in every host of the target that contains `U`. Fix `r_0 >= 1` and `delta_* > 0` such that `K` has no
`(r_0, delta_*)`-sofic approximation, and put `b = |B_{r_0}|`, `eta_0 = delta_* / ((1 + b) b^2)` and
`eta_1 = eta_0 / (1 + b^2 (1 + eta_0))`.

Let `c` be any configuration with `B_{r_0} ⊆ E ∩ F`, and take any derived-read model of its pattern.
- If `epsilon < 1/6`, then `mu >= 1 + eta_1`.
  - Otherwise, restrict to `(B_{r_0}, B_{r_0})`, keeping `epsilon` and a ratio `mu_0 <= mu < 1 + eta_1`, so
    `b^2(mu_0 - 1) < 1`.
  - Corollary P gives an `(r_0, (1 + b) b^2 (mu_R - 1))`-sofic approximation, so `mu_R >= 1 + eta_0`.
  - With `t = mu_0 - 1`, `(1 + t)/(1 - b^2 t) >= 1 + eta_0` rearranges to `t >= eta_1`, which is a contradiction.
- Hence the certified bound is at most

      k log q - eta_1 H(Y)          (epsilon < 1/6).

- If `1/6 <= epsilon <= 1/2`, the Fannes term already gives
  `delta(epsilon) >= (1/3) log |X_F| >= (1/3)(k log q + |F| H(Y))`, since `H(Y) <= log |R|`.
  - If `mu >= 1`, the right-hand side of Lemma A' is at most `k log q - delta <= (2/3) k log q`.
  - If `mu < 1`, it is at most `k log q + H(Y) - (1/3)(k log q + |F| H(Y)) <= (2/3) k log q`, because
    `|F| >= b >= 3`. A nonsofic group is infinite, so it is not generated by one involution, and `|S| >= 3`.

So on every host `G` containing a nonsofic `K`, for all configurations with `B^K_{r_0} ⊆ E ∩ F` (these extend every
configuration supported in `B^K_{r_0}`), the whole derived-read class proves at most

    Phi(c) >= log q - min( eta_1 H(Y)/k , (1/3) log q ).

These configurations are exactly the ones maximality must control. Extension only lowers `Phi`.

## 5. Where every member dies

The invariant is the ratio `mu` of codes to good sites, together with the pinning event (pin).

- **Step of death: Lemma P, part 1.** The unit incidence `g^-1 g = 1` puts `x(1)` among the reads of the code
  `sigma_{g^-1}(i)`, so at a good site the read `v_{sigma_{g^-1}(i), g}` equals the site variable `Z_i` with
  probability `1 - epsilon`. Nothing about how reads are computed can change this. The local law fixes the joint
  distribution, and independence of sites turns agreement in distribution into identity of indices.
- Tightness (`mu ~ 1`) then makes almost every code full (part 3). Pinned read-backs define `tau`, which gives a
  genuine reading model (parts 4 to 6). RM Lemma B turns that model into a sofic approximation.

So a derived-read count can be tight only by containing a reading model, and RM already showed that a reading model
can be tight only by being sofic.

**What the class contains, beyond RM.**
- Linear double counts over a finite field: dimension bounds `n <= sum rank + sum (conditional rank)` run site by
  site over a linearly independent family of functionals. This covers linear codes, linear sofic reads and matrix
  models, whenever the conditional term is a sum over individual site functionals.
- Nonlinear, hashed or randomized reads, and reads that use extra randomness in `Omega`.
- Non-product ambient measures, provided good sites are jointly independent and uniform.
- Approximate local laws (TV up to `1/6`, and up to `1/2` with the `(1/3) log q` loss).
- Everything in RM Section 5.

## 6. What remains outside (the new gate)

1. **Subspace-good counts.** These are counts whose conditional term is not a sum over individual site variables,
   for instance `H(Z | C_{N'})` bounded by the codimension of a large "good subspace" in a rank-metric
   approximation.
   - A count that runs the chain rule over a basis of that subspace is a derived-read model, and Theorem D applies to
     it. So such a count must bound the conditional entropy globally, without a per-coordinate chain rule.
   - This is exactly the gap flagged by `site-pullbacks-are-discontinuous-in-the-rank-metric`, and it is where
     linear soficity (`linear-sofic-groups-are-surjunctive`) would have to enter.
   - A candidate must produce the term `H(x(1) | Y_F)` of `Phi` without isolating one site. The functional `Phi` is
     itself per-site, so this is the precise remaining freedom.
2. **Approximately independent good sites.** `H(Z_V) >= |V|(k log q - beta)` with `beta > 0` instead of exact
   independence. Pinning still gives near-injectivity, but the index identifications in parts 1 and 5 degrade along
   chains. Not treated.
3. **Volume counts** (Hilbert--Schmidt, log-determinant) and multi-count limit functionals, as in RM.

## 7. Consequence for the target

On `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`, the nonsofic `EL_D(R)` sits inside every host that
contains `U`, as RM Section 5 notes. On those hosts no derived-read certificate reaches `Phi >= log q` on the
configurations with `B^K_{r_0} ⊆ E ∩ F`. This holds for any field (product or not), any reads (coordinates, linear
or nonlinear) and any tolerance. This is a statement about the proof class, not about `Phi`. A proof of maximality on
such hosts must leave the per-site chain-rule accounting of Section 2, for instance through item 1 of Section 6.
