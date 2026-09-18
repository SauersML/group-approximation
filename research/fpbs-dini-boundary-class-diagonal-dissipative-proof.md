---
rg: 2
id: fpbs-dini-boundary-class-diagonal-dissipative-proof
kind: route
title: North--South dynamics bounds each diagonal return mass by a product of thin-shadow masses at g and g^{-1}, and Borel--Cantelli turns a convergent shadow-product sum into dissipation off the diagonal
target: fpbs-dini-boundary-class-diagonal-dissipative
requires:
  - fpbs-hyperbolic-bb-criterion-obstruction
---

Full written proof. All sets and maps are Borel. Notation is as in the target claim.

## Imported inputs

- **(I1) Gromov products.** Use `(x|y)_o` for `x, y` in `Gamma ∪ dGamma`, defined for boundary points by the usual
  inf-liminf over sequences.
  - It is invariant under isometries: `(gx|gy)_{go} = (x|y)_o`.
  - It is `delta`-hyperbolic: `(x|z)_o >= min((x|y)_o, (y|z)_o) - 2 delta`.
  - For a vertex `x` and a boundary point `zeta`, `(x|zeta)_o + (o|zeta)_x >= |x| - 2 delta`. For interior points this
    is an exact identity; the boundary version loses `2 delta`.
  - Changing the base point from `o` to `p` changes the Gromov product by at most `|p|`.
- **(I2) Visual metric.** For small `eps > 0` there is a metric `d_eps` on `dGamma` and `C_0 >= 1` with
  `C_0^{-1} e^{-eps (zeta|zeta')_o} <= d_eps(zeta, zeta') <= C_0 e^{-eps (zeta|zeta')_o}`.
  - Disjoint closed sets `U, V` satisfy `sup_{U x V} (zeta|zeta')_o = M_{UV} < infinity`, by compactness.
  - Every boundary point is the endpoint of a geodesic ray from `o`.
- **(I3) Bevilacqua--Bowen, Theorem A.1 and Definitions 37--40**, as recorded in
  `research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md`, §6.1.
  - `Con(Y)` is `Gamma`-invariant.
  - Every positive-measure subset of `Con(Y)` has infinitely many return times at almost every point.
  - PDR is defined for ergodic actions: a.e. `x, y` are joined by a finite chain of pairs in `Con(X^2)`.
- **(I4) No finite orbits.** A nonelementary hyperbolic group fixes no point of `dGamma`.
- **(I5) Item 4 of `fpbs-hyperbolic-bb-criterion-obstruction`** (Zimmer map is Dirac under PDR). Used only in the
  Corollary.

## Step 1: North--South bounds with thin shadows

For a vertex `x` and `s >= 0`, put:
- `N_s(x) = {zeta : (x|zeta)_o >= s}`;
- `O_s(x) = {zeta : (x|zeta)_o >= |x| - s - 2 delta}`.

**Lemma 1.** If `zeta` is not in `N_s(g^{-1})`, then `g zeta` is in `O_s(g)`. Hence `g(dGamma \ N_s(g^{-1}))` is
contained in `O_s(g)`. If `|g| >= 2s + 2 delta`, then `O_s(g)` is contained in `N_s(g)`.

*Proof.*
- Put `x = g^{-1} o`. By (I1), `(o|zeta)_x >= |g| - (x|zeta)_o - 2 delta > |g| - s - 2 delta`.
- Apply the isometry `g`, which sends `x` to `o` and `o` to `g o`. This gives `(go|g zeta)_o > |g| - s - 2 delta`.
- The inclusion holds because `|g| - s - 2 delta >= s`.

**Lemma 2.** Let `U, V` be closed and disjoint, and let `s > M_{UV} + 2 delta`. Then no set `N_s(x)` meets both `U`
and `V`.

*Proof.* If `zeta` is in `U ∩ N_s(x)` and `zeta'` is in `V ∩ N_s(x)`, then
`(zeta|zeta')_o >= s - 2 delta > M_{UV}` by (I1). This is a contradiction.

## Step 2: the return mass of a product set

Fix `U, V` as in Lemma 2 with the chosen `s`, and fix `B` of finite measure. Put `B_W = B ∩ xi^{-1}(W)` and
`A = B_U x B_V`. For `W = U, V`, put `a_W(g) = mu(B_W ∩ g^{-1} B_W)`. It also equals `mu(g B_W ∩ B_W)`, by invariance.
Then `(mu x mu)(A ∩ g^{-1} A) = a_U(g) a_V(g)`.

By equivariance, `z in g^{-1} B_W` implies `xi(z) in g^{-1} W`. Therefore:
- **(i)** `a_W(g) <= nu_B(W ∩ g^{-1} W)`;
- **(ii)** `a_W(g) <= nu_B(gW ∩ W)`.

**Lemma 3.** If `|g| >= 2s + 2 delta`, then `a_U(g) a_V(g) <= nu_B(O_s(g)) nu_B(O_s(g^{-1}))`.

*Proof.* Put `N^+ = N_s(g)` and `N^- = N_s(g^{-1})`. By Lemma 2, each of them meets at most one of `U`, `V`.
- **If `W ∩ N^- = ∅`:** by Lemma 1, `gW ⊂ O_s(g)`. So `a_W(g) <= nu_B(O_s(g))` by (ii).
- **If `W ∩ N^+ = ∅`:** Lemma 1 applied to `g^{-1}` gives `g^{-1}W ⊂ O_s(g^{-1})`. So `a_W(g) <= nu_B(O_s(g^{-1}))`
  by (i).
- **If `W` meets neither:** `gW ⊂ O_s(g) ⊂ N^+`, which is disjoint from `W`. So `gW ∩ W = ∅` and `a_W(g) = 0`.

It remains to treat the case where `U` and `V` each meet `N^+` or `N^-`. Since neither of `N^+`, `N^-` meets both,
one of them meets exactly `U` and the other meets exactly `V`.
- If `N^-` meets `U` and `N^+` meets `V`, then `U ∩ N^+ = ∅` and `V ∩ N^- = ∅`. So
  `a_U a_V <= nu_B(O_s(g^{-1})) nu_B(O_s(g))`.
- The other assignment is symmetric.

## Step 3: Borel--Cantelli (Theorem A)

Summing Lemma 3 gives

`sum_g (mu x mu)(A ∩ g^{-1}A) <= #{g : |g| < 2s + 2 delta} mu(B)^2 + S_s(nu_B)`,

which is finite by hypothesis. The left side equals `int_A #{g : gz in A} d(mu x mu)(z)`. So a.e. `z` in `A` returns to
`A` only finitely often.

If `E = A ∩ Con(Z x Z)` had positive measure, then a.e. point of `E` would return to `E`, and so to `A`, infinitely
often (I3). So `A ∩ Con(Z x Z)` is null.

Now choose:
- `U, V` from the countable family of pairs of closed `d_eps`-balls with rational radii, centred in a countable dense
  set, and with disjoint closures;
- `B` from the given countable directed family.

Every crossing pair `(z, z')` lies in some such `A`. So the crossing part of `Con(Z x Z)` is null, which is total
dissipativity of the crossing part.

**PDR fails when `Z` is ergodic.** `Con(Z x Z)` is contained in `{xi(z) = xi(z')}` up to a null set. So every chain of
Con-pairs stays inside one fibre of `xi`. PDR would then make `xi(z) = xi(z')` for `mu x mu`-a.e. pair, so `xi` is a.e.
constant. Its value is a `Gamma`-fixed point, which contradicts (I4). No hypothesis on `Con(Z)` is needed.

## Step 4: Dini implies shadow-summable (Theorem B)

**Lemma 4.**
1. `O_s(x)` has `d_eps`-diameter at most `C_0 e^{4 eps delta} e^{-eps(|x| - s)}`.
2. Each `zeta` lies in `O_s(x)` for at most `K_s = |ball of radius 2s + 10 delta|` vertices `x` with `|x| = n`.

*Proof.*
1. For `zeta, zeta'` in `O_s(x)`, (I1) gives `(zeta|zeta')_o >= |x| - s - 4 delta`. Then apply (I2).
2. Let `r` be a geodesic ray from `o` to `zeta`. The inequality `(x|zeta)_o >= n - s - 2 delta` with `|x| = n` puts
   `x` within `2s + 10 delta` of `r(n)`, by the standard tree approximation of the tripod `o, x, zeta`.

Let `lambda` be Dini with modulus `omega`.
- By Lemma 4.1, `lambda(O_s(g)) <= omega(c_s e^{-eps |g|})`, where `c_s = C_0 e^{4 eps delta} e^{eps s}`.
- By Lemma 4.2, `sum_{|g| = n} lambda(O_s(g^{-1})) <= K_s lambda(dGamma)`.

Hence

`S_s(lambda) <= sum_n omega(c_s e^{-eps n}) K_s lambda(dGamma) < infinity`,

because `omega` is nondecreasing and `sum_n omega(c e^{-eps n})` is comparable to `(1/eps) int_0 omega(r) dr/r`.

**Domination.** Suppose `nu_B << lambda` for every `B` of finite measure, with `lambda` a finite Dini measure. Fix an
exhaustion `B'_1 ⊂ B'_2 ⊂ ...` by sets of finite measure, and let `h_j = d nu_{B'_j} / d lambda`. Put
`B_{j,k} = B'_j ∩ xi^{-1}{h_j <= k}`. Then `nu_{B_{j,k}} <= k lambda`, and these sets cover `Z` up to a null set.

The family of finite unions of the sets `B_{j,k}` is countable and directed. Each member has `nu <= (sum of k's)
lambda`, so it is Dini, and therefore shadow-summable. So Theorem A applies.

## Step 5: the ergodic dichotomy (Theorem C)

Fix `nu` in `C`.

**The Dini part.** Let `E_D` be the essential union of the Borel sets `E` such that `nu|_E << lambda_E` for some
finite Dini measure `lambda_E`.
- **Countable unions.** If `lambda_k` are Dini with moduli `omega_k`, put
  `lambda = sum_k 2^{-k} lambda_k / (1 + lambda_k(dGamma) + int_0^1 omega_k dr/r)`. Then `omega_lambda <=
  sum_k c_k omega_k`, so `lambda` is Dini and dominates every `lambda_k`. Hence `E_D` is attained by a countable
  union, and `nu|_{E_D}` is dominated by one Dini measure.
- **Invariance.** By (I1) and (I2), `g` is bi-Lipschitz on `(dGamma, d_eps)` with constant `C_0^2 e^{eps |g|}`. So
  `g_* lambda_E` is Dini. Quasi-invariance gives `nu|_{gE} ~ g_*(nu|_E) << g_* lambda_E`. So `g E_D ⊂ E_D` modulo
  null sets.

By ergodicity, `E_D` is null or conull.
- **Conull:** the first alternative holds.
- **Null:** let `lambda` be any Dini measure, and let `E` carry the part of `nu` absolutely continuous to `lambda`.
  Then `E ⊂ E_D` is null, so `nu` is singular to `lambda`.

**Positive dimension forces the Dini case.** Suppose `d_nu(zeta) = liminf_{r -> 0} log nu(B(zeta,r)) / log r > 0` on a
set `P` of positive measure.
- Put `E_k = {zeta in P : nu(B(zeta,r)) <= r^{1/k} for all r <= 1/k}`. This is Borel, since it suffices to take
  rational `r` by left continuity of `r ↦ nu(B(zeta,r))` for open balls. The `E_k` increase to `P`.
- Put `F_k = E_k \ E_{k-1}`. A ball `B(zeta,r)` meeting `F_k` at `zeta'` lies in `B(zeta', 2r)`. So
  `nu(B(zeta,r) ∩ F_k) <= min(nu(F_k), (2r)^{1/k})` when `2r <= 1/k`, and `<= nu(F_k)` otherwise.
- With `phi(r) = 1 / log(e D/r)^2` (`D` the diameter), `phi` is Dini, and the ratio of that bound to `phi` is bounded
  by some `D_k`.
- `lambda = sum_k 2^{-k} D_k^{-1} nu|_{F_k}` is equivalent to `nu|_P` and has `omega_lambda <= phi`.

So `P ⊂ E_D` up to a null set, and `E_D` is not null.

## Step 6: the Corollary and the named classes

Let `Z` be an amenable ergodic PDR imp action with `Con(Z)` conull. By (I5), its Zimmer map is `delta_{xi}` for an
equivariant `xi`. By Theorems B and A, the class of `xi_* mu` is not dominated by a Dini measure. By Theorem C it is
singular to all of them, and by Step 5 every measure in it has lower local dimension `0` a.e.

Positive-dimension inputs, imported and not reproved here:
- **Patterson--Sullivan and quasi-conformal densities.** These are for a proper cocompact `Gamma`-action on a
  hyperbolic space quasi-isometric to the Cayley graph, including the word metric and the Riemannian symmetric
  metric. The shadow lemma (Coornaert 1993) gives `nu(O_s(g)) <= C e^{-c|g|}`. Since `B(zeta, e^{-eps n}) ⊂
  O_s(r(n))` for fixed `s`, the measure is Frostman, hence Dini. The same shadow lemma holds for quasi-conformal
  (Gibbs) measures of Hölder cocycles.
- **Harmonic measures.** For a nondegenerate random walk with finite first moment, harmonic measure is exact
  dimensional of dimension `h/(eps l) > 0` (Tanaka, *Dimension of harmonic measures in hyperbolic spaces*, ETDS
  2019). Entropy `h > 0` holds by non-amenability, and the drift `l` is positive and finite.
- **Lebesgue class of a cocompact rank-one lattice.** This is a special case, since Lebesgue measure is
  Patterson--Sullivan for the Riemannian metric. It recovers, for cocompact lattices, the conclusion of
  `fpbs-rank-one-lebesgue-boundary-diagonal-dissipative` by an unrelated argument. The diagonal set
  `{xi(z) = xi(z')}` is null for a nonatomic class, so the whole diagonal is dissipative there.

For Maharam extensions `dGamma x R` of `nu`, the sets `B_R = dGamma x [-R,R]` give `nu_{B_R} = (e^R - e^{-R}) nu`. An
equivalent measure `f nu` gives an isomorphic extension. So the Maharam extension is covered as soon as the class of
`nu` contains a Dini measure.

## Step 7: atomic classes

Let `Z` be ergodic and let the class of `xi_* mu` be atomic. By ergodicity it is carried by one orbit `Gamma eta`. Put
`H = Stab(eta)`. In a hyperbolic group, `H` is finite or virtually cyclic, and in the latter case it has a second
fixed point `eta*`. The map `a eta ↦ a eta*` is well defined and equivariant on `Gamma eta`.

- **Structure of the pair space.** Over the orbit of a pair `(a eta, b eta)`, the space `Z x Z` is induced from the
  pair stabilizer `S = aHa^{-1} ∩ bHb^{-1}`.
- **Finite pair stabilizers.** If `S` is finite, the fibre `W` over `(a eta, b eta)` meets `gW` only for `g` in `S`.
  So `W` has no positive-measure part in `Con`, and neither do its translates.
- **Infinite pair stabilizers.** If `S` is infinite and `a eta != b eta`, then `S` contains a loxodromic element
  fixing both points. So `b eta = a eta*`.

Hence `Con(Z x Z)` is contained in `{xi(z') in {xi(z), xi(z)*}}`. The map `P(z) = {xi(z), xi(z)*}` is an equivariant
pair map, or a point map when `H` is finite, and it is constant along Con-chains. Under PDR it would be a.e. constant,
which gives an invariant point or pair and contradicts (I4) together with (H6) of the obstruction proof. So an
ergodic PDR action never has an atomic boundary class.

**Consequence.** A Bevilacqua--Bowen certificate for a nonelementary hyperbolic group needs a **nonatomic** ergodic
quasi-invariant class on `dGamma` that is singular to every Dini measure.

## Remarks

1. **No cocycle geometry is used.** Property (P) of `fpbs-hyperbolic-bb-criterion-obstruction-proof`, Step 7 asks the
   cocycle difference to grow along geodesics. Here the cocycle never appears. Classes whose cocycle fails (P) but
   which have positive dimension are killed.
2. **`Gamma = Z` calibrates the geometry.** For `g = n`, `O_s(n)` and `O_s(-n)` are the two ends. The sum is
   `sum_n nu{+}nu{-} = infinity` when both carry mass, and Lemma 3 gives nothing, as it must.
3. **The sharp sum.** The proof actually shows that
   `sum_g a_U(g) a_V(g) < infinity` for all `U`, `V`, `B` suffices. For a Maharam extension with `B = dGamma x [-R,R]`,
   `a_W(g)` is comparable, within factors `e^{±2R}`, to `nu{eta in W ∩ g^{-1}W : |log D_g(eta)| <= 2R}`, where
   `D_g = d(nu∘g)/d nu`. A Maharam certificate must make this sum diverge. That needs Radon--Nikodym derivatives
   staying bounded on sets of `nu`-mass much larger than the thin shadows, which is exactly what positive dimension
   forbids.
4. **Atomic classes.** For an atomic class on the orbit of a loxodromic fixed point, the shadow sum diverges.
   Step 7 still kills PDR. So the criterion is sufficient, not necessary.

## Where the argument stops

Classes singular to every Dini measure are untouched. For such a class, thin shadows at `g` and `g^{-1}` carry masses
whose products are not summable, for every measure in the class. Whether a cocompact `Sp(n,1)` lattice has a
nonatomic ergodic quasi-invariant class of this kind is open. If a nonelementary hyperbolic group `Gamma` has none,
then by Step 7 and the Corollary it has no Bevilacqua--Bowen certificate.
