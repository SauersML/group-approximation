---
rg: 2
id: fpbs-rotation-support-rigidity-kills-type-iii-classes-proof
kind: route
title: The Fubini step of the rotation-class rigidity needs only that the measure be nonatomic, since the bad pair relation has countable sections; transporting product measures along a Borel isomorphism with E_0 gives every Krieger type on the rotation rays; a pigeonhole on fellow-travelling orbit points replaces the limit-set intersection property
target: fpbs-rotation-support-rigidity-kills-type-iii-classes
requires:
  - fpbs-rotation-boundary-class-refutes-shadow-summability
---

Full written proof. Notation and numbering of cited results (Lemma 1.1, Lemma 1.2, Lemma 4.1, Lemma 5.1,
Proposition 5.2, Theorem 3) are those of `research/fpbs-rotation-boundary-class-refutes-shadow-summability-proof.md`.
In particular:
- `Omega_0` is the conull `sigma`-invariant set of `(theta, j)` with `theta + n alpha` not in `{0, 1/2}` for all `n`;
- `zeta^+ : Omega_0 -> dF` is the injective Borel itinerary map, and `B = zeta^+(Omega_0)`;
- `gamma_k(omega)` are the elements with `gamma_k(omega) zeta^+(omega) = zeta^+(sigma^k omega)`;
- `Bad = {(omega, omega') in Omega_0^2 : theta' in (theta + Z alpha) ∪ (-theta + Z alpha)}`.

## Imported inputs

- **(R) The previous rotation claim.** Lemmas 1.1, 4.1, 5.1 and Proposition 5.2 are combinatorial statements about
  words and rotations. They do not mention any measure. They are used verbatim.
- **(DJK)** Dougherty, Jackson, Kechris, *The structure of hyperfinite Borel equivalence relations*, Trans. AMS 341
  (1994), Theorem 9.1. Two aperiodic, nonsmooth, hyperfinite Borel equivalence relations are Borel isomorphic if and
  only if they have the same number of invariant ergodic probability measures.
- **(AW)** Araki--Woods and Krieger. The product measure `m_p = ⊗ (p, 1-p)` on `{0,1}^N`, with `0 < p < 1/2`, is
  quasi-invariant and ergodic for the tail relation `E_0`, of Krieger type `III_lambda` with `lambda = p/(1-p)`.
  Suitable inhomogeneous product measures give types `III_1` and `III_0`. Ergodicity for product measures is the
  Hewitt--Savage/Kolmogorov 0-1 law.
- **(Kr)** Krieger type is an invariant of the measure class of an ergodic nonsingular countable Borel equivalence
  relation. Types `III_lambda` are unchanged by passing to the restriction to a complete section (Krieger's ratio set
  is computed on any complete section).
- **(Ad)** Adams, *Boundary amenability for word hyperbolic groups*, Topology 33 (1994). The action of a hyperbolic
  group on its boundary is amenable for every quasi-invariant measure, and so is every action with a measurable
  equivariant map to it, in particular Maharam extensions.
- **(Mo)** Standard hyperbolic geometry: the Morse lemma for quasi-geodesic rays, and the fact that two geodesic rays
  with the same endpoint are eventually within `8 delta` of each other after a shift of parameter.
- **(K)** Used only for the last sentence of Theorem C: every torsion-free nonelementary hyperbolic group contains a
  malnormal quasiconvex free subgroup of rank 2 (I. Kapovich, Math. Proc. Cambridge Philos. Soc. 127 (1999)). Not
  reproved.

## 1. Theorem A: the Fubini step needs only a nonatomic measure

**Lemma 1.1 (countable sections).** For every `omega in Omega_0`, the section `Bad_omega = {omega' : (omega, omega') in
Bad}` is countable. Hence `(rho_1 x rho_2)(Bad) = 0` for every finite Borel `rho_1` and every finite nonatomic Borel
`rho_2` on `Omega_0`.

*Proof.* `Bad_omega` is contained in `((theta + Z alpha) ∪ (-theta + Z alpha)) x Z/2`, a countable set. `Bad` is
Borel. By Fubini, `(rho_1 x rho_2)(Bad) = int rho_2(Bad_omega) d rho_1(omega) = 0`, since a nonatomic measure gives
countable sets measure zero. ∎

Put `N_0 = ⋃_{h, h' in F} (h x h')(zeta^+ x zeta^+)(Bad)`, a subset of `F B x F B`. It is Borel, because `zeta^+` is
an injective Borel map on the standard Borel space `Omega_0` (Lusin--Souslin).

**Lemma 1.2 (translates stay inside the bad set).** For all `g, g', h, h' in F`,

`(g^{-1} h x g'^{-1} h')(zeta^+ x zeta^+)(Bad) ∩ (B x B) ⊆ (zeta^+ x zeta^+)(Bad)`.

*Proof.* Let `(omega, omega') in Bad`, and suppose `g^{-1} h zeta^+(omega) = zeta^+(omega_1)` and
`g'^{-1} h' zeta^+(omega') = zeta^+(omega_2)`. By Lemma 4.1 of (R), `omega_1 = sigma^k omega` and
`omega_2 = sigma^{k'} omega'` for some `k, k'`. Now `sigma^k` changes `theta` by `k alpha`. The relation
`theta' in ±theta + Z alpha` is invariant under `theta -> theta + k alpha` and `theta' -> theta' + k' alpha`. So
`(omega_1, omega_2) in Bad`. ∎

**Lemma 1.3 (the bad set is null).** Let `lambda_1, lambda_2` be finite Borel measures on `dF`, carried by `F B`, with
`lambda_2` nonatomic. Then `(lambda_1 x lambda_2)(N_0) = 0`.

*Proof.* Enumerate `F = {g_1, g_2, ...}` and put `P_i = g_i B minus ⋃_{l < i} g_l B`. These are disjoint Borel sets
covering `F B`. It suffices to show that `(lambda_1|_{P_i} x lambda_2|_{P_l})((h x h')(zeta^+ x zeta^+)(Bad)) = 0` for
all `i, l, h, h'`.
- Put `rho_1 = (zeta^+)^{-1}_* (g_i^{-1})_* (lambda_1|_{P_i})` and `rho_2 = (zeta^+)^{-1}_* (g_l^{-1})_* (lambda_2|_{P_l})`.
  These are finite Borel measures on `Omega_0`, and `rho_2` is nonatomic, since `zeta^+` is injective and `lambda_2`
  is nonatomic.
- Applying `g_i^{-1} x g_l^{-1}` and Lemma 1.2 (with `g = g_i`, `g' = g_l`), the measure in question is at most
  `(rho_1 x rho_2)(Bad)`.
- Lemma 1.1 finishes the proof. ∎

**Theorem A.** Let `(Z, mu_Z)` be an imp `F`-space and `xi : Z -> dF` measurable and equivariant. Suppose that for
every `E` of finite measure, `lambda_E = xi_*(mu_Z|_E)` is nonatomic and carried by `F B`. Then `F` acts totally
dissipatively on `(Z x Z, mu_Z x mu_Z)`.

*Proof.*
- *Joint returns are finite off `N`.* Put `N = (dF x dF minus F B x F B) ∪ N_0`. By Theorem 3(1) of (R), for every
  `(eta, eta')` not in `N` and every finite `H ⊂ F`, only finitely many `g` satisfy `g eta, g eta' in H B`. The proof
  of Theorem 3(1) uses only Lemma 4.1 and Proposition 5.2, which do not involve any measure.
- *A cover.* Choose `E_n` of finite measure increasing to `Z`, and finite `H_n` increasing to `F`. Since `lambda_{E_n}`
  is carried by `F B`, the sets `E'_n = E_n ∩ xi^{-1}(H_n B)` increase to a conull set.
- *Pairs avoid `N`.* `(xi x xi)_*(mu_Z|_{E'_n} x mu_Z|_{E'_n}) = lambda_{E'_n} x lambda_{E'_n}`. This gives
  `F B x F B` full measure, and by Lemma 1.3 it gives `N_0` measure zero. So a.e. pair in `E'_n x E'_n` has image
  outside `N`.
- *Finite returns.* If `g(z, z') in E'_n x E'_n`, then `g xi(z), g xi(z') in H_n B`. So a.e. pair in `E'_n x E'_n` has
  finitely many such `g`.
- *Dissipativity.* By the recurrence theorem for nonsingular actions of countable groups (Aaronson, *An introduction
  to infinite ergodic theory*, §1.6), a.e. point of the conservative part `C` that lies in `E'_n x E'_n` returns to it
  under infinitely many `g`. So `C ∩ (E'_n x E'_n)` is null for each `n`, and `C` is null. ∎

**Remarks.**
1. The non-crossing pairs (`xi z = xi z'`) are included: the diagonal of `dF` lies in `N`, because
   `(omega, omega) in Bad`, and it is null for `lambda x lambda` with `lambda` nonatomic.
2. If `xi_*(mu_Z|_E) << nu_rho` with `rho` nonatomic, the hypothesis holds. Indeed `nu_rho` is carried by `F B` and
   nonatomic, and absolute continuity preserves both properties.
3. Nothing about the Radon--Nikodym cocycle of `nu_rho` enters. This is why type III classes pose no new difficulty.
   The previous lane's concern, that returns can "use the Radon--Nikodym direction", is empty here. A joint return in
   the Maharam extension is in particular a joint return of the boundary pair to `H B x H B`, and those are already
   finite.

## 2. Theorem B: every Krieger type lives on the rotation rays

Let `R_sigma` be the orbit equivalence relation of `sigma` on `Omega_0`.

**Lemma 2.1.** `R_sigma` is aperiodic, nonsmooth and hyperfinite, and `P` is its only invariant probability measure.

*Proof.*
- *Aperiodic.* `sigma^p(theta, j) = (theta, j)` with `p != 0` forces `p alpha in Z`.
- *Hyperfinite.* It is generated by one Borel automorphism.
- *Unique invariant measure.* An `R_sigma`-invariant probability measure is `sigma`-invariant. Extended by zero to the
  compact group `T x Z/2`, it is invariant under translation by `(alpha, 1)`. Its Fourier coefficient at a character
  `chi` satisfies `mu^(chi) (chi(alpha, 1) - 1) = 0`. The powers of `(alpha, 1)` are dense (this is the ergodicity
  proof of Section 1 of (R)), so `chi(alpha, 1) != 1` for `chi != 1`. Hence `mu` is Haar measure, which is `P`.
- *Nonsmooth.* `P` is invariant, ergodic and nonatomic. A smooth countable relation has none. ∎

**Lemma 2.2.** The tail relation `E_0` on `{0,1}^N` is aperiodic, nonsmooth and hyperfinite, and its only invariant
probability measure is the uniform product measure.

*Proof.* The first three properties are standard. For the last, flipping the `i`-th coordinate is a Borel automorphism
whose graph lies in `E_0`. So an invariant measure gives equal mass to all `2^n` cylinders of length `n`. ∎

**Proposition 2.3 (type III measures on `Omega_0`).** For every `lambda in [0,1]` there is a nonatomic Borel
probability `rho_lambda` on `Omega_0`, quasi-invariant and ergodic for `R_sigma` (so for `sigma`), such that
`(R_sigma, rho_lambda)` has Krieger type `III_lambda`.

*Proof.* By Lemmas 2.1, 2.2 and (DJK), there is a Borel isomorphism `Psi : Omega_0 -> {0,1}^N` with
`(Psi x Psi)(R_sigma) = E_0`. Let `m_lambda` be an `E_0`-quasi-invariant, ergodic, nonatomic measure of type
`III_lambda` from (AW), and put `rho_lambda = (Psi^{-1})_* m_lambda`. Quasi-invariance, ergodicity, nonatomicity and
Krieger type are all invariant under isomorphisms of Borel relations. ∎

**Lemma 2.4 (the class `nu_rho`).** Let `rho` be nonatomic, `sigma`-quasi-invariant and ergodic on `Omega_0`. Then:
1. `nu_rho` is `F`-quasi-invariant, ergodic and nonatomic, and carried by `F B`;
2. `B` is a complete section of the `F`-orbit relation `R_F` on `F B`, and `R_F|_B = (zeta^+ x zeta^+)(R_sigma)`;
3. `nu_rho|_B` is equivalent to `zeta^+_* rho`.

Consequently, by (Kr), `(dF, nu_rho)` has the same type `III_lambda` as `(R_sigma, rho)`.

*Proof.*
1. *Quasi-invariance.* `h_* nu_rho = sum_g c_g (hg)_* zeta^+_* rho` has the same null sets as `nu_rho`.
   *Nonatomic.* `zeta^+` is injective.
   *Ergodicity.* For `F`-invariant `E`, `nu_rho(E) = sum_g c_g rho((zeta^+)^{-1}(g^{-1} E)) = rho((zeta^+)^{-1} E)`.
   Since `zeta^+(sigma omega) = zeta_1(omega)^{-1} zeta^+(omega)`, the set `(zeta^+)^{-1} E` is `sigma`-invariant, so
   its measure is `0` or `1`.
2. This is Lemma 4.1 of (R).
3. For `E ⊆ B`, `nu_rho(E) >= c_e rho((zeta^+)^{-1} E)`. Conversely, `g zeta^+(omega) in E ⊆ B` forces
   `g = gamma_k(omega)` and `g zeta^+(omega) = zeta^+(sigma^k omega)`. So
   `(zeta^+)^{-1}(g^{-1} E) ⊆ ⋃_k sigma^{-k} (zeta^+)^{-1}(E)`. If `rho((zeta^+)^{-1} E) = 0`, quasi-invariance makes
   every term null, and `nu_rho(E) = 0`. ∎

**Proof of Theorem B.** Take `rho = rho_lambda` from Proposition 2.3. By Lemma 2.4, `nu_{rho_lambda}` is an ergodic,
nonatomic, quasi-invariant class of type `III_lambda`, carried by `F B`.
- Let `Z` be its Maharam extension `dF x R`, with measure `d nu x e^t dt` and the Radon--Nikodym skew action. With `xi`
  the projection, `xi_*(mu_Z|_E) << nu_{rho_lambda}` for every `E` of finite measure. Theorem A applies (Remark 2 of
  Section 1), so the diagonal is totally dissipative.
- The same holds for every imp action, ergodic or not, whose boundary map pushes finite-measure restrictions into
  this class. That includes the ergodic components of the Maharam extension, which is not ergodic for
  `lambda < 1`.
- Amenability is (Ad). An ergodic imp action with totally dissipative diagonal is not PDR, since `Con(Z^2)` is null.

*Skew weights.* The complement of `Omega_0` in `T x Z/2` is countable. So every nonatomic Borel measure on
`T x Z/2` lives on `Omega_0`, including every measure defined by Anzai- or Denjoy-type cocycle weights on cylinders.
Theorem A applies to all of them, with no condition on the cocycle. ∎

## 3. Theorem C: hyperbolic groups without the limit-set intersection property

Let `Gamma` be nonelementary hyperbolic, with a `delta`-hyperbolic Cayley graph, base point `o = e`, and word length
`|.|`. Let `F = <a,b> ≤ Gamma` be free of rank 2 and quasiconvex. Then the orbit map `f -> f o` is a
`(L, c)`-quasi-isometric embedding of the Cayley tree of `F`. Let `iota : dF -> Lambda_F` be the induced
`F`-equivariant homeomorphism. By (Mo) there is `H` such that for each `zeta in dF`, the points `f_n o`, where
`f_n = zeta_1 ... zeta_n` are the prefixes of `zeta`, lie within `H` of a geodesic ray from `o` to `iota(zeta)`.
Assume:

**(M')** For every `beta in Gamma \ F`, the subgroup `F ∩ beta F beta^{-1}` is cyclic.

For a subgroup `K ≤ F`, let `dK ⊆ dF` be its set of accumulation points in the tree compactification. If `K = <c>` is
cyclic, then `dK ⊆ {c^+, c^-}`. A left translate `p c^{±}` (`p in F`) is eventually periodic.

**Lemma 3.1 (pigeonhole replacing (LI)).** Assume (M'). Let `zeta in dF` be such that no `F`-translate of `zeta` is
eventually periodic (equivalently, `zeta` is not eventually periodic). If `gamma in Gamma` and
`gamma iota(zeta) in Lambda_F`, then `gamma in F`.

*Proof.* Write `gamma iota(zeta) = iota(zeta')`. Let `f_n` and `f'_m` be the prefixes of `zeta` and `zeta'`.
- The points `f_n o` lie within `H` of a geodesic ray `r` from `o` to `iota(zeta)`.
- The points `gamma^{-1} f'_m o` lie within `H` of a geodesic ray `r'` from `gamma^{-1} o` to
  `gamma^{-1} iota(zeta') = iota(zeta)`.
- By (Mo), `r` and `r'` are eventually within `8 delta` of each other. Put `D = 2H + 8 delta + 1`.

So for all large `n` there is `m(n)` with `d(f_n o, gamma^{-1} f'_{m(n)} o) <= D`. Then
`beta_n = f_n^{-1} gamma^{-1} f'_{m(n)}` has `|beta_n| <= D`. The ball of radius `D` is finite, so some `beta` equals
`beta_n` for infinitely many `n_1 < n_2 < ...`. Write `m_i = m(n_i)`. From `f_{n_i} beta = gamma^{-1} f'_{m_i}`,

`f_{n_1}^{-1} f_{n_i} = beta (f'^{-1}_{m_1} f'_{m_i}) beta^{-1}`, for all `i >= 2`.

The left side is in `F`, the right side in `beta F beta^{-1}`. So `k_i = f_{n_1}^{-1} f_{n_i}` lies in
`K = F ∩ beta F beta^{-1}`. The `k_i` are distinct, since the `n_i` are, and `k_i -> f_{n_1}^{-1} zeta` in the tree
compactification. Hence `f_{n_1}^{-1} zeta in dK`.
- If `beta ∉ F`, then `K` is cyclic by (M'), so `f_{n_1}^{-1} zeta` is eventually periodic. This contradicts the
  hypothesis.
- So `beta in F`, and `gamma^{-1} = f_{n_1} beta f'^{-1}_{m_1} in F`. ∎

For malnormal `F` (the hypothesis (M) of (R)), `K` is trivial when `beta ∉ F`, and the lemma holds for every `zeta`.
This is Lemma 6.1 of (R), proved now without (LI).

**Lemma 3.2 (forcing `x, y in F`).** Assume (M'). Let `omega, omega' in Omega_0` and `x, y in Gamma`. If the equation
`gamma_k(omega) = x gamma_{k'}(omega') y` has infinitely many solutions `(k, k')`, then `x, y in F`.

*Proof.*
- For fixed `k'` the left side is determined, and distinct `k` give distinct `gamma_k(omega)`. So infinitely many
  `k'` occur. Pass to solutions `(k_i, k'_i)` with `|k'_i|` strictly increasing and `k'_i` of constant sign.
- Put `c_i = gamma_{k'_1}(omega')^{-1} gamma_{k'_i}(omega')`. Then `y^{-1} c_i y = gamma_{k_1}(omega)^{-1}
  gamma_{k_i}(omega) in F`. So `c_i` and `c_i^{-1}` lie in `K' = F ∩ y F y^{-1}`.
- *Case `k' > 0`.* `gamma_{k'}(omega')^{-1} = zeta_1 ... zeta_{k'}(omega')` is a prefix of `zeta^+(omega')`. So
  `c_i^{-1} = (zeta_1 ... zeta_{k'_i}) gamma_{k'_1}(omega')`. Its reduced form shares a prefix of length at least
  `k'_i - |k'_1|` with `zeta^+(omega')`. Hence `c_i^{-1} -> zeta^+(omega')`, so `zeta^+(omega') in dK'`. By
  Lemma 1.1(3) of (R), `zeta^+(omega')` is not eventually periodic.
- *Case `k' < 0`.* `gamma_{k'}(omega')^{-1} = zeta_0^{-1} zeta_{-1}^{-1} ... zeta_{k'+1}^{-1}` is a prefix of the ray
  `zeta^-(omega') = zeta_0^{-1} zeta_{-1}^{-1} ...`. As before, `zeta^-(omega') in dK'`. The `n`-th letter of
  `zeta^-(omega')` has exponent `-s(theta' + (1-n) alpha)`. If this ray were eventually periodic with period `p`, then
  `s(X - t alpha) = s(X - p alpha - t alpha)` for all `t >= 0`, with `X = theta' + (1-N) alpha` for large `N`. Lemma
  5.1 of (R) would give `p alpha in Z`. So it is not eventually periodic.
- In both cases `dK'` contains a point that is not eventually periodic. So `K'` is not cyclic, and (M') gives
  `y in F`. Then `x = gamma_{k_1}(omega) y^{-1} gamma_{k'_1}(omega')^{-1} in F`. ∎

With `x, y in F`, Proposition 5.2 of (R) applies. So:

**Corollary 3.3.** Assume (M'). If `(omega, omega') ∉ Bad`, then for all `x, y in Gamma` the equation
`gamma_k(omega) = x gamma_{k'}(omega') y` has finitely many solutions.

**Lemma 3.4 (returns reduce to `F`).** Assume (M'). Let `omega in Omega_0` and `h, u, g in Gamma`. Then
`g h iota zeta^+(omega) in u iota(B)` if and only if `u^{-1} g h = gamma_k(omega)` for some `k`. That `k` is unique.

*Proof.* If `u^{-1} g h iota zeta^+(omega) in iota(B) ⊆ Lambda_F`, Lemma 3.1 gives `u^{-1} g h in F`. The rotation ray
`zeta^+(omega)` is not eventually periodic by Lemma 1.1(3) of (R). Then `iota` is injective and `F`-equivariant, so
`u^{-1} g h zeta^+(omega) in B`. Lemma 4.1 of (R) gives the unique `k`. The converse is clear. ∎

Put `N_Gamma = (dGamma x dGamma minus Gamma iota(B) x Gamma iota(B)) ∪ ⋃_{h, h' in Gamma} (h iota zeta^+ x h' iota zeta^+)(Bad)`.

**Lemma 3.5.** Assume (M'). Let `lambda_1, lambda_2` be finite Borel measures on `dGamma` carried by `Gamma iota(B)`,
with `lambda_2` nonatomic. Then `(lambda_1 x lambda_2)(N_Gamma) = 0`.

*Proof.* This is the proof of Lemma 1.3, with `Gamma` in place of `F` and `iota zeta^+` in place of `zeta^+`. The only
new point is the analogue of Lemma 1.2. Suppose `g^{-1} h iota zeta^+(omega) = iota zeta^+(omega_1)` with
`g, h in Gamma`. By Lemma 3.4 (with `u = e`), `g^{-1} h = gamma_k(omega)`, so `omega_1 = sigma^k omega`. The rest is
unchanged. ∎

**Theorem C.** Assume (M'). Let `(Z, mu_Z)` be an imp `Gamma`-space and `xi : Z -> dGamma` measurable and equivariant.
Suppose that for every `E` of finite measure, `xi_*(mu_Z|_E)` is nonatomic and carried by `Gamma iota(B)`. Then
`Gamma` acts totally dissipatively on `(Z x Z, mu_Z x mu_Z)`.

*Proof.*
- *Finite joint returns off `N_Gamma`.* Let `(eta, eta') ∉ N_Gamma`. Write `eta = h iota zeta^+(omega)` and
  `eta' = h' iota zeta^+(omega')` with `h, h' in Gamma`. Then `(omega, omega') ∉ Bad`. Fix `u, u'` in a finite set
  `H ⊂ Gamma`.
  - By Lemma 3.4, `g eta in u iota(B)` and `g eta' in u' iota(B)` hold iff `g = u gamma_k(omega) h^{-1} =
    u' gamma_{k'}(omega') h'^{-1}` for some `k, k'`.
  - Such a `g` determines `k` and `k'`. The pair satisfies `gamma_k(omega) = x gamma_{k'}(omega') y` with
    `x = u^{-1} u'` and `y = h'^{-1} h`.
  - By Corollary 3.3 there are finitely many such pairs, hence finitely many `g`. Summing over `(u, u') in H^2`:
    only finitely many `g` satisfy `g eta, g eta' in H iota(B)`.
- *Cover, null set and dissipativity.* These are as in Theorem A, with `H_n` increasing to `Gamma` and Lemma 3.5 in
  place of Lemma 1.3. ∎

**The last sentence of Theorem C (torsion-free groups).** A malnormal `F` satisfies (M'), with trivial intersections.
By (K) every torsion-free nonelementary hyperbolic group has a malnormal quasiconvex free subgroup of rank 2. So for
these groups Theorem C holds, and with Section 2 (which is about `F` alone) every Krieger type `III_lambda` occurs
among the killed classes `nu_rho = sum_{g in Gamma} c_g g_* iota_* zeta^+_* rho`. For type, note that
`iota(B)` is a complete section of the `Gamma`-orbit relation on `Gamma iota(B)`, and by Lemma 3.4 the restricted
relation is `(iota zeta^+)(R_sigma)`. The equivalence `nu_rho|_{iota(B)} ~ iota_* zeta^+_* rho` is proved as in
Lemma 2.4(3), using Lemma 3.4.

**What changed relative to Section 6 of (R).**
- (LI) was used to prove Lemma 6.1 there. Lemma 3.1 proves it by a pigeonhole on orbit points that fellow-travel two
  asymptotic rays. That argument uses only the Morse lemma and finiteness of balls.
- (M) was used twice: in Lemma 6.1, and to force `y in F`. Both uses need only (M'), because the elements that
  malnormality kills accumulate at a rotation ray, and rotation rays are not limit points of cyclic subgroups.
- (K) remains the only import that is not elementary. Replacing it requires proving (M') for some explicit Schottky
  subgroup, such as `<a^N, b^N>` with `N` large. That is a small-cancellation statement: a long common fellow-travelling
  of two branching `F`-hulls forces the translating element to be close to `F`. It is left open here.

## 4. The general statement: the exact step where the support method stops

**Proposition 4.1.** Let `Gamma` be a cocompact Fuchsian group, `dGamma = S^1`, and let `Leb` be the Lebesgue class.
For every Borel `S` with `Leb(Gamma S) = 1`, some finite `H ⊂ Gamma` has the following property. The set of pairs
`(eta, eta') in HS x HS` with infinitely many `g` such that `g eta, g eta' in HS` has positive `Leb x Leb` measure. In
particular its sections are not all countable.

*Proof.* The diagonal action on `(S^1 x S^1, Leb x Leb)` is conservative (Hopf; the geodesic flow of a closed
hyperbolic surface is recurrent, and the Liouville class is `Leb x Leb` off the diagonal). Choose `H` with
`Leb(HS) > 0`. Then `W = HS x HS` has positive measure, and by conservativity a.e. point of `W` returns to `W` under
infinitely many `g`. ∎

So the conclusion of Theorem A cannot come from the support alone for every class. For Lebesgue it holds for the
Maharam extension only because of the Radon--Nikodym fibre (Theorem B of `fpbs-dini-boundary-class-diagonal-dissipative`).
A proof of the general pointwise match rigidity statement for Dini-singular classes must therefore combine a support
relation, as here, with a fibre count, as in the Dini claim. Neither alone suffices: Theorem 1 of (R) defeats the
fibre count, and Proposition 4.1 defeats the support relation.
