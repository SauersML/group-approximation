# Mod-p homology growth of Kazhdan groups vanishes along the profinite topology

Lane `sw-007` (inverter on `fpbs-fixed-price-counterexample-exists`), wave
`flagship-2026-09-17`.

## Why this matters for Fixed Price

`fpbs-kazhdan-rankgradient-counterexample-reduction` refutes Fixed Price from
an infinite Kazhdan group `Gamma` with a Farber chain of positive rank gradient.
Hutchcroft--Pete give `Gamma` an action of cost one. Abert--Nikolov give the
profinite boundary action cost `1 + RG`. Every proposed certificate for positive
rank gradient in the archive is homological: it bounds `d(Gamma_n)` below by
`d_p(Gamma_n) = dim_(F_p) H_1(Gamma_n;F_p)`, along the derived `p`-series, a
power-deficiency presentation, or a Golod--Shafarevich tower. This note proves
that no such mod-`p` certificate can work, for two broad classes of chains, and
names what survives.

Notation: `d_p(H) = dim_(F_p) H_1(H;F_p)`. A *Kazhdan pair* `(X,kappa)` for `G`
means that for every unitary representation `(pi,V)` of `G` without nonzero
invariant vectors and every `v` in `V`, some `s` in `X` has
`||pi(s)v - v|| >= kappa ||v||`.

## Theorem A (no rapid descent)

**Theorem A.** Let `Gamma` be a Kazhdan group and `p` a prime. Then `Gamma` has
no abelian `p`-series with rapid descent. In other words, there is no chain
`Gamma = Gamma_1 > Gamma_2 > ...` with `Gamma_(i+1)` normal in `Gamma_i`,
`Gamma_i/Gamma_(i+1)` elementary abelian, and
`inf_i d_p(Gamma_i/Gamma_(i+1))/[Gamma:Gamma_i] > 0`.
Consequently, `RG_p(L) = 0` for every finite index subgroup `L` of `Gamma`, where
`RG_p(L) = inf_H (d_p(H)-1)/[L:H]` over subnormal `H` of `p`-power index.

*Proof.*
1. By `fpbs-shalom-property-t-is-open`, there is a finitely presented Kazhdan
   group `G` with a surjection `pi: G -> Gamma`.
2. Put `P_i = pi^(-1)(Gamma_i)`. Then `P_(i+1)` is normal in `P_i`,
   `P_i/P_(i+1) = Gamma_i/Gamma_(i+1)` and `[G:P_i] = [Gamma:Gamma_i]`. So
   `{P_i}` is an abelian `p`-series of `G` with rapid descent.
3. By Lackenby's Theorem 1.15 (`fpbs-lackenby-rapid-descent-p-large`), `G` is
   `p`-large. So some finite index subgroup of `G` maps onto a nonabelian free
   group, and hence onto `Z`.
4. This contradicts (T): (T) passes to finite index subgroups and forces finite
   abelianization.

For the consequence, note that a finite index `L` is again Kazhdan. Suppose
`RG_p(L) = c > 0`. The derived `p`-series `D_i` of `L` has
`D_i/D_(i+1) = H_1(D_i;F_p)`, so
`d_p(D_i/D_(i+1)) = d_p(D_i) >= 1 + c[L:D_i]`. That is rapid descent, which
Theorem A excludes. QED.

**What Theorem A kills.**
- Any certificate `d_p(H) >= c[Gamma:H]` along a family of subnormal `p`-power
  index subgroups that is cofinal in the pro-`p` topology. Every `D_i` contains
  a member `H`. Lackenby's Lemma 3.3 gives
  `(d_p(D_i)-1)/[Gamma:D_i] >= (d_p(H)-1)/[Gamma:H]`, iterated along a subnormal chain from `D_i` down to `H` with `p`-power steps. So the derived `p`-series
  grows linearly.
- It reproves `fpbs-power-p-deficiency-excludes-property-t` without truncating
  presentations: positive power `p`-deficiency gives `RG_p > 0` by
  `fpbs-power-p-deficiency-schreier-bound`.
- The Attempt in `fpbs-kazhdan-positive-rank-gradient` that "moves the
  difficulty to `RG_p(Gamma) > 0`" is dead. That condition is never satisfied
  by a Kazhdan group, finitely presented or not.

## Theorem B (profinitely cofinal families)

**Theorem B.** Let `Gamma` be a Kazhdan group, `p` a prime and `c > 0`. There is
no family `F` of finite index normal subgroups of `Gamma` such that
- every finite index subgroup of `Gamma` contains a member of `F`, and
- `d_p(N) >= c[Gamma:N]` for every `N` in `F`.

Equivalently, `d_p(N)/[Gamma:N] -> 0` along the directed set of finite index
normal subgroups. For every `c > 0` there is a finite index `M` such that every
finite index normal `N` of `Gamma` contained in `M` has `d_p(N) < c[Gamma:N]`.
In particular, `d_p(Gamma_n)/[Gamma:Gamma_n] -> 0` along every nested normal
chain that is cofinal in the profinite topology. Such chains are exactly the
chains whose boundary action is the full profinite completion `Gamma-hat`.

The equivalence: suppose the vanishing fails for some `c`. Then the set of
normal `N` with `d_p(N) >= c[Gamma:N]` meets every finite index subgroup, since
each finite index subgroup contains a normal one. That set is such a family.

### Ingredients

- **(K) Kazhdan support bound.** Let `G` be finitely presented with presentation
  complex `K` on generators `X` and relators `R`, and let `(X,kappa)` be a
  Kazhdan pair. Let `U` be a subgroup of index `N`, with covering complex `K_U`
  (`N` vertices, `N|X|` edges). Then every cellular cocycle `c` representing a
  nonzero class `alpha` in `H^1(K_U;F_p)` satisfies
  `|supp c| >= kappa^2 N/4`. So `relsize(alpha) >= eps := kappa^2/(4|X|)`.
  - *Proof.* Let `K~` be the `p`-fold cover of `K_U` for `ker alpha`. Its vertex
    set is `V = G/ker alpha`, of size `pN`.
  - Lift `c` to `c`-values on `V` (Lackenby, *Detecting large groups*,
    Section 4). The deck group shifts `c`-values by `1`, so each fibre meets
    the zero level set `A` exactly once, and `|A| = N`.
  - Put `f = 1_A - 1/p`. It is orthogonal to the constants in `l^2(V)`, and
    `l^2_0(V)` has no invariant vectors because `G` acts transitively.
  - (T) gives an `s` in `X` with `2|A \ s^(-1)A| = ||pi(s)1_A - 1_A||^2 >=
    kappa^2||f||^2 = kappa^2 N(1-1/p) >= kappa^2 N/2`.
  - Take `v` in `A` with `sv` not in `A`. The `s`-edge `v -> sv` has nonzero
    `c`-difference, so it lies over an edge in `supp c`. Distinct such `v` lie
    over distinct edges, because each fibre has one vertex in `A`.
  - Hence `|supp c| >= |A \ s^(-1)A| >= kappa^2 N/4`. This is an explicit
    contrapositive of Lackenby's Theorem 4.2 and Lemma 4.3.
- **(L5.1)** Lackenby, Theorem 5.1. Let `K` be a finite 2-complex with `r`
  2-cells, and `U` a set of `u` cocycles representing independent classes in
  `H^1(K;F_p)`. Let `q: K~ -> K` be regular with elementary abelian deck group of
  rank `n`. Then there are at least `(n-u)u - r` cocycles on `K~` representing
  independent classes and supported in `q^(-1)(supp U)`.
- **(L6.1)** Lackenby, Theorem 6.1. Let `V` be a subspace of `F_p^E` of
  dimension `v`, and `w < v`. Then `V` has a `w`-dimensional subspace `W` with
  `|supp W| <= theta_w |supp V|`, where
  `theta_w = (p^(w+1)-p)/(p^(w+1)-1) < 1`.
- **(L3.3)** Lackenby, Lemma 3.3. If `H` is normal of `p`-power index in `L`,
  then `d_p(H) <= (d_p(L)-1)[L:H] + 1`.
- **(Tr)** If `[B:A]` is coprime to `p`, restriction
  `H^1(B;F_p) -> H^1(A;F_p)` is injective, since corestriction composed with
  restriction is multiplication by `[B:A]`. Pulling back a cellular cocycle
  along the finite cover `K_A -> K_B` replaces its support by the full
  preimage. So it preserves the support fraction (support over number of
  1-cells).

### Proof of Theorem B

**Setup.**
- Suppose `F` exists. Take a finitely presented Kazhdan cover `pi: G -> Gamma`
  (`fpbs-shalom-property-t-is-open`), with finite presentation `<X|R>`, Kazhdan
  pair `(X,kappa)` and presentation complex `K`.
- Every subgroup below is the preimage of a finite index subgroup of `Gamma`.
  Write `K_A` for the cover of `K` belonging to `A`. For such `A`,
  `d_p(A) >= d_p(pi A)`, since `A` maps onto `pi A`.
- Fix `u = ceil(2|R|/c)`, `theta = theta_u` and `eps = kappa^2/(4|X|)`.

**Step 1: good subgroups.** Call `A` *good* if:
- `d_p(pi A) >= c[G:A]`;
- `[G:A] > (u^2+u)/|R|`;
- `K_A` carries `u` cocycles representing independent classes in `H^1(K_A;F_p)`
  whose union of supports is a fraction `sigma` of the 1-cells.

The first good subgroup: pick `N` in `F` of index above `(u^2+u)/|R|` and above
`u/c`.
- Such `N` exists. For any member `N_0`, `d_p(N_0) >= c[Gamma:N_0] > 0`, so the
  Frattini subgroup `[N_0,N_0]N_0^p` is proper.
- By cofinality it contains a member, of index at least `p[Gamma:N_0]`. So
  member indices are unbounded.

Put `A = pi^(-1)(N)`. Take any `u` independent classes (`d_p(N) >= c[G:A] > u`),
with `sigma <= 1`.

**Step 2: from a good `A` with fraction `sigma` to a good `A'` with fraction at
most `theta sigma`.**
1. *Frattini cover.* Let `Phi = [pi A, pi A](pi A)^p` and `B = pi^(-1)(Phi)`.
   Then `B` is normal in `A` and `A/B = pi A/Phi` is elementary abelian of rank
   `n = d_p(pi A) >= c[G:A]`. So `K_B -> K_A` is regular with elementary abelian
   deck group of rank `n`. The complex `K_A` has `r = |R|[G:A]` 2-cells.
2. *Lift the classes (L5.1).* There are at least `(n-u)u - r` independent
   classes on `K_B`, supported in the preimage of the old support. Here
   `(n-u)u - r >= c[G:A]u - u^2 - |R|[G:A] >= 2|R|[G:A] - u^2 - |R|[G:A] > u`,
   using `cu >= 2|R|` and `[G:A] > (u^2+u)/|R|`.
3. *Shrink the support (L6.1).* Let `V` be their span. It is a subspace of
   cocycles in which every nonzero element represents a nonzero class. Its
   support is at most the preimage of the old support, so its support fraction
   is at most `sigma`. Theorem 6.1 with `w = u` gives a `u`-dimensional `W`
   inside `V` with support fraction at most `theta sigma`. A basis of `W`
   represents `u` independent classes on `K_B`.
4. *Coprime descent.* By cofinality, pick `N` in `F` with `N` contained in
   `Phi`. Let `P` be a Sylow `p`-subgroup of `Phi/N`, `A'_Gamma` its preimage in
   `Phi`, and `A' = pi^(-1)(A'_Gamma)`. Then `[B:A'] = [Phi:A'_Gamma]` is
   coprime to `p`. By (Tr), pulling `W` back to `K_(A')` gives `u` cocycles
   representing independent classes, with support fraction at most
   `theta sigma`.
5. *Growth is inherited (L3.3).* `N` is normal in `Gamma`, hence normal in
   `A'_Gamma`, with index `p^k = |P|`. So
   `d_p(A'_Gamma) >= 1 + (d_p(N)-1)/p^k >= 1 + (c[Gamma:N]-1)/p^k
   = c[Gamma:A'_Gamma] + 1 - p^(-k) >= c[G:A']`.
   Also `[G:A'] >= [G:A]`, so `A'` is good.

**Step 3: contradiction.** Iterate Step 2 `m` times, with `theta^m < eps`. This
gives a finite index subgroup `A_m` of `G` and a nonzero class on `K_(A_m)`
represented by a cocycle whose support is at most `theta^m` times the number of
1-cells. That contradicts (K). QED.

Only finitely many steps are used, about `log(1/eps)/log(1/theta)`, which is of
order `p^u log(4|X|/kappa^2)`.

### Calibration

- **Free group `F_2`.** The family of all finite index normal subgroups has
  `d_p(N) = [F_2:N] + 1`. Steps 1--2 go through; only (K) fails, since `F_2` is
  not Kazhdan. The argument then produces classes of vanishing relative size,
  consistent with `F_2` failing (tau) with respect to kernels.
- **Any finitely presented `G` without (T).** Replace (K) by Lackenby's
  Theorem 4.1. The same iteration says that a profinitely cofinal normal family
  with linear mod-`p` growth makes `G` large. This is consistent with Lackenby's
  Theorem 1.6: for virtually residually `p`-finite `G`, positive first
  `L^2`-Betti number implies large. Via Luck approximation, `beta^(2)_1 > 0`
  yields exactly such a family with `b_1` in place of `d_p`. No known
  non-large group is contradicted.
- **Lackenby's (tau) paper** (arXiv:math/0509036, Theorems 1.1, 1.3, 1.7). It
  builds, in groups whose pro-`p` completion has exponential subgroup growth,
  nested subnormal `p`-chains with linear mod-`p` growth and (tau). Such chains
  have index-`p` steps and are not closed under Frattini subgroups. Step 2.4
  needs a member inside `Phi(pi A)`, so those chains are outside Theorem B's
  hypothesis, and outside Theorem A's too, since they are not abelian series
  with rapid descent. No contradiction.

## Corollary B' (all primes at once: the abelianization rank)

**Corollary B'.** Let `Gamma` be a Kazhdan group and `c > 0`. There is a finite
index `M` such that every finite index normal `N` of `Gamma` contained in `M`
satisfies `d(N^ab) < c[Gamma:N]`. Here `N^ab` is finite, and `d(N^ab)` is its
minimal number of generators.

*Proof.* Take the finitely presented Kazhdan cover `pi: G -> Gamma` with
presentation `<X|R>`, and put `L = max(2, max relator length)`.

1. **Hadamard torsion bound.** Let `Q = pi^(-1)(N)`, of index `m = [Gamma:N]`.
   The group `H_1(Q;Z)` is `ker d_1 / im d_2` in the covering complex `K_Q`.
   - `C_1/ker d_1` embeds in the free group `C_0`, so `tors H_1(Q)` embeds in
     `tors coker d_2`.
   - The order of `tors coker d_2` is the product of the nonzero invariant
     factors of `d_2`. That product divides every nonzero maximal-rank minor, so
     by Hadamard it is at most the product of the column norms.
   - `d_2` has `|R|m` columns, each of Euclidean norm at most its `l^1` norm,
     which is at most `L`.
   - Hence `|tors H_1(Q)| <= L^(|R|m)`.
2. **The bound on `d_p`.** `Q` is Kazhdan, so `b_1(Q) = 0`, and `d_p(Q)` is the
   `p`-rank of `tors H_1(Q)`. So `p^(d_p(Q)) <= L^(|R|m)`, and
   `d_p(N) <= d_p(Q) <= |R| m log L / log p`.
3. **Large primes.** If `p > P_0 := L^(|R|/c)`, then `d_p(N) < c[Gamma:N]` for
   every finite index normal `N`, with no restriction on `N`.
4. **Small primes.** For each of the finitely many primes `p <= P_0`, Theorem B
   gives an `M_p`. Put `M` equal to the intersection of the `M_p`.
5. `N^ab` is finite, so `d(N^ab) = max_p d_p(N)`. QED.

The same torsion bound shows that along *any* family of finite index subgroups
of a Kazhdan group, linear growth of `d_p` can occur only for primes
`p <= L^(|R|/c)`.

## What survives, sharply

A homological certificate for `fpbs-kazhdan-positive-rank-gradient` must avoid
Theorems A, B and Corollary B'. What remains is one of the following.

1. **A non-cofinal Farber chain with linear growth at a fixed prime.** The
   chain is neither profinitely cofinal (Theorem B) nor an abelian `p`-series
   with rapid descent (Theorem A). An example would be a Farber chain inside a
   pro-`p`-like quotient with index-`p` subnormal steps, as in Lackenby's (tau)
   chains. For `Gamma` Kazhdan such chains may exist, for example when the
   pro-`p` completion has exponential subgroup growth, as for Ershov's
   Golod--Shafarevich Kazhdan groups.
2. **A non-abelian certificate on a cofinal chain.** Take
   `d(Gamma_n) >= c[Gamma:Gamma_n]` along a cofinal chain. By Corollary B', the
   abelianization contributes `o([Gamma:Gamma_n])` generators, at every prime
   simultaneously. Prime-varying abelian certificates are dead, by the
   Hadamard torsion bound. So the generators must be forced by one of the
   following. (By Dalla Volta--Lucchini, `d` of a finite group is governed by
   crown-based powers of its chief factors.)
   - Non-central abelian chief factors, which means large twisted
     `H^1(Gamma_n;M)` for nontrivial irreducible `F_p[Gamma_n/K]`-modules `M`.
     Inflation-restriction bounds this by `d_p(K)`. But `[Gamma:K]` can be far
     larger than `[Gamma:Gamma_n]`, so Theorem B does not control it.
   - Non-abelian crowns `S^k` with `k` exponential in the index, which means
     `log|Epi(Gamma_n,S)| >= c'[Gamma:Gamma_n]`.
   - The gap `d(Gamma_n) > d(Gamma_n-hat)`, which no finite quotient detects.

Rank gradient along the full profinite completion is `Cost(Gamma-hat) - 1`.
Theorem B and Corollary B' therefore say that, for a Kazhdan group, the profinite completion
action can have cost above one only through survivor 2.
