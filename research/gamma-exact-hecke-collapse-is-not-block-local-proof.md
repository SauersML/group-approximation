---
rg: 2
id: gamma-exact-hecke-collapse-is-not-block-local-proof
kind: route
target: gamma-exact-hecke-collapse-is-not-block-local
title: Proof that at Gamma-exact lifts (MUI-O) reduces to admissible finite block rigidity, with the subfield model and the antiflag counterexample
requires:
  - mui-pair-measures-orbital-reduction
  - kun-thom-nonsofic-wreath
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
  - research/artifacts/dual-number-antiflag-block-2026-09-18.g
---

Notation is that of `gamma-exact-hecke-collapse-is-not-block-local`.
Fix `t in T`. Write `phi = phi_t`, `Lambda = Lambda_t`, `s = s_n`,
`Y = Y_n`, and `u = u_n`, and suppress `n` where harmless. "Along `U`" is
understood in every limit. `(S, kappa)` is a Kazhdan pair for `Gamma`: for
every unitary representation `pi` and every vector `v`,
`||v - P v|| <= kappa^-1 max_{s in S} ||pi(s) v - v||`, where `P` is the
projection onto invariant vectors.

Theorem C and Theorem 4.1 are used exactly as transcribed in
`research/artifacts/kun-thom-2608-06222-verified.md`:

- **(C)** if `G` acts sofically on `(X, mu)`, then `L^infty(X)^Gamma` is
  `G`-invariant;
- **(4.1)** if `sigma : G -> S_U` is a sofic representation, then
  `C_{S_U}(sigma(Gamma))` is normalized by `sigma(G)`.

## Step 0. The twisted diagonal action

Since the lift is Gamma-exact and `phi(Gamma) = Lambda subset Gamma`,

```text
gamma . (y, z) = (s(gamma) y, s(phi(gamma)) z)
```

is an honest action of `Gamma` on `Y x Y`. Its orbits are the Gamma-orbits
of the Gamma-set `Y x phi^* Y`. Let `Y = X_1 ⊔ ... ⊔ X_m` be the
`s(Gamma)`-orbits. An orbit `O subset X_i x Y` of the twisted action
projects onto `X_i` with fibres of constant size `m_O = |O| / |X_i|`. When
`m_O = 1`, `O` is the graph of a map `g_O : X_i -> Y` with
`g_O(s(gamma) x) = s(phi(gamma)) g_O(x)`. Its image is one
`s(Lambda)`-orbit.

The **defect** of `t` at level `n` is

```text
eps_n = max_{gamma in S} u({y : s(t) s(gamma) y != s(phi(gamma)) s(t) y}).
```

Since `t gamma = phi(gamma) t` in `G` and `sigma` is sofic, `eps_n -> 0`.

## Step 1. Rectification (part (1))

**Lemma R.** Let `f : Y -> Y` be a bijection with
`max_{gamma in S} u(f s(gamma) != s(phi(gamma)) f) <= eps`. Then there are
a Gamma-invariant `Y' subset Y` and an injective twisted-equivariant
`tau : Y' -> Y` with `u({y in Y' : tau y = f y}) >= 1 - 4 eps / kappa^2`.
Moreover, on each orbit `X_i subset Y'`, `tau` agrees with `f` on more than
half of `X_i`.

*Proof.* Let `F = {(y, f y)}` be the graph of `f` and let
`v = 1_F in l^2(Y x Y)` under the twisted action. Then `||v||^2 = |Y|`. For
`gamma in S`, the point `(s(gamma) y, s(phi(gamma)) f y)` lies in `F` for
every `y` outside the defect set. So `|gamma F \ F| <= eps |Y|` and
`||gamma v - v||^2 <= 2 eps |Y|`. By (T),
`||v - P v||^2 <= (2 eps / kappa^2) |Y|`. Now `P v` is the orbit average:
`P v = sum_O p_O 1_O` with `p_O = |F ∩ O| / |O|`. Hence

```text
||v - P v||^2 = sum_O |F ∩ O| (1 - p_O)  <=  (2 eps / kappa^2) |Y|.
```

Since `F` is a graph, `|F ∩ O| <= |X_i|` for `O` over `X_i`, so
`p_O <= 1/m_O`. Every orbit with `p_O > 1/2` therefore has `m_O = 1`, and
the orbits with `p_O <= 1/2` contain at most `(4 eps / kappa^2)|Y|` points
of `F`. Over a fixed `X_i` the sets `F ∩ O` are disjoint and have total
size `|X_i|`, so at most one orbit `O_i` over `X_i` has `p_O > 1/2`. Call
`X_i` good if it exists, let `Y'` be the union of the good `X_i`, and put
`tau = g_{O_i}` on `X_i`. Then `tau = f` on `F ∩ O_i`, a set of more than
`|X_i|/2` points, and the total mass where `tau = f` is at least
`1 - 4 eps / kappa^2`.

*Injectivity on `X_i`.* `tau : X_i -> tau(X_i)` is a twisted-equivariant
surjection between transitive sets, so its fibres have a constant size
`k`. The set where `tau = f` meets each fibre at most once, since `f` is
injective, and has more than `|X_i|/2` points. So `|X_i|/k > |X_i|/2` and
`k = 1`.

*Injectivity across orbits.* If `tau(X_i)` meets `tau(X_j)` with `i != j`,
the two images are the same `Lambda`-orbit `L`, and
`|X_i| = |L| = |X_j|`. Then `f` maps more than `|L|/2` points of `X_i` and
more than `|L|/2` points of `X_j` injectively into `L`, which is
impossible. ∎

Apply Lemma R to `f = s(t)` with `eps = eps_n`. This gives `Y'_n`, `tau_n`,
and the agreement bound of (1). `tau_n` intertwines `s(gamma)` with
`s(phi(gamma))`, so `Y''_n = tau(Y'_n)` is `s(Lambda)`-invariant, each
Gamma-orbit `A` of `Y'` maps bijectively onto one Lambda-orbit `tau A`, and
`tau : A -> phi^*(tau A)` is a Gamma-isomorphism.

*TV statement.* Let `B_n = (Y \ Y') ∪ {y in Y' : tau y != s(t) y}`, with
`u(B_n) -> 0`. Extend `tau` to any bijection of `Y`. Then
`(tau x tau)_* nu_n` and `psi(t)_* nu_n` agree off the image of
`(B_n x Y) ∪ (Y x B_n)`, whose `nu_n`-mass tends to `0` because the
marginals of an MUI measure are uniformly absolutely continuous with
respect to `u_n`. ∎(1)

**Corollary R1 (one orbit).** Let `C` be one `s(Gamma)`-orbit and
`beta : C -> C` a bijection with
`max_{gamma in S} |{y in C : beta s(gamma) y != s(gamma) beta y}| <=
eps |C|`, where `4 eps / kappa^2 < 1/2`. Then `beta` agrees with a
Gamma-automorphism of `C` on at least `(1 - 4 eps / kappa^2)|C|` points.
(Apply Lemma R to the Gamma-set `C` with `phi = id`. The only
Gamma-invariant subsets are `C` and the empty set, and the agreement bound
rules out the empty set. An injective equivariant map `C -> C` is an
automorphism.)

## Step 2. Theorem C kills the leak (part (2))

For a Gamma-orbit `C` of `Y` contained in `Y'` (note that `Y'` is
Gamma-invariant), let `w_1(C) >= w_2(C) >= ...` be the sizes of the
Lambda-orbits `tau A` contained in `C`. Put
`m'(C) = sum_{i >= 2} w_i(C)`. Then
`leak(C) = |C \ Y''| + m'(C)`.

**Sign lemma.** Let `w_1 >= w_2 >= ...` be nonnegative, `W = sum w_i`,
`m' = W - w_1`, and let `eps_i` be independent fair signs. Put
`P_± = sum_{eps_i = ±1} w_i`. Then `E min(P_+, P_-) >= 0.14 m'`.

*Proof.* `min(P_+, P_-) = (W - |S|)/2` with `S = sum eps_i w_i`, and
`E|S| <= (sum w_i^2)^(1/2)`. If `m' <= w_1`, then
`sum w_i^2 <= w_1^2 + w_1 m'`, so `(sum w_i^2)^(1/2) <= w_1 + m'/2` and
`E min >= m'/4`. If `m' > w_1`, then `w_1 < W/2` and
`sum w_i^2 <= w_1 W < W^2/2`, so
`E min >= W (1 - 2^(-1/2))/2 > 0.146 W >= 0.14 m'`. ∎

*Proof of (2).* For each `n` choose signs `eps_A in {±1}`, one for each
Gamma-orbit `A` of `Y'_n`, such that

```text
sum_{C subset Y'} min(P_+(C), P_-(C))  >=  0.14 sum_{C subset Y'} m'(C),      (*)
```

where `P_±(C)` is the total size of the `tau A subset C` with
`eps_A = ±1`. By the sign lemma, the expectation of the left side over
independent fair signs satisfies this, so some choice does. Put
`f_n = sum_A eps_A 1_A`: this is `±1` on `Y'`, `0` off `Y'`, and exactly
`s(Gamma)`-invariant.

Work on the Loeb space `X` of `(Y_n, u_n)`, with the tautological sofic
embedding, exactly as in the proof of `mui-pair-measures-orbital-reduction`
(1). Then `F = st(f) in L^infty(X)^Gamma`. By (C), `t . F` is again
Gamma-invariant. At the internal level, `g_n = f_n o s(t)^-1` satisfies
`max_{gamma in S} ||g_n o s(gamma)^-1 - g_n||_{L^1(u_n)} -> 0`. Since
`|g_n| <= 1`, the same holds in `L^2(u_n)` squared.

The invariant vectors of `l^2(Y)` under `s(Gamma)` are the functions that
are constant on each orbit, and `P` averages over orbits. By (T),

```text
sum_C min_c sum_{z in C} (g_n(z) - c)^2  =  ||g_n - P g_n||^2  =  o(|Y|).
```

Off the set `s(t)(B_n) ∪ (Y \ Y'')`, of mass `o(1)`, we have
`g_n = eps_A` on `tau A`: for `y in A` with `tau y = s(t) y`,
`g_n(tau y) = f_n(y) = eps_A`. On an orbit `C subset Y'` the function
`g_n` is therefore `+1` on `P_+(C)` points and `-1` on `P_-(C)` points,
apart from exceptional points. For every constant `c`,
`P_+(1-c)^2 + P_-(1+c)^2 >= min(P_+, P_-)`. Hence
`sum_C min(P_+(C), P_-(C)) = o(|Y|)`, and by (*),
`sum_{C subset Y'} m'(C) = o(|Y|)`. Finally,
`sum_C |C \ Y''| = |Y \ Y''| = |Y \ Y'| = o(|Y|)`, because `tau` is
injective, and the orbits `C` not contained in `Y'` have total mass
`u(Y \ Y') = o(1)`. So `sum_C leak(C) = o(|Y|)`.

The Gamma-orbits `A` of `Y'` that are not of the form `A_C` have
`tau A` among the non-maximal Lambda-orbits of some `C`, so their total
size is at most `sum_C m'(C) = o(|Y|)`. ∎(2)

(The theorem is used only through `t . F in L^infty(X)^Gamma`: it gives
Gamma-invariance of the push, not `t`-invariance. That is exactly the form
needed.)

## Step 3. Theorem 4.1 makes the good blocks admissible (part (3))

Fix `delta, delta' > 0`. By (2) and Markov's inequality, the Gamma-orbits
`A` of `Y'` that are not of the form `A_C`, or have
`leak(C) > min(delta, delta'/2)|C|`, carry mass `o(1)`. Let `A_n` be the
set of remaining orbits `A = A_C` for which some Gamma-automorphism `alpha_A`
of `A` has `tau alpha_A tau^-1` agreeing with no Gamma-automorphism of `C`
on `(1 - delta')|C|` points. We show `u(union A_n) -> 0`.

Let `pi_n` be `alpha_A` on each `A in A_n` and the identity elsewhere.
Then `pi_n` commutes with `s(Gamma)` exactly, so
`[pi] in C_{S_U}(sigma(Gamma))`. By (4.1), `sigma(t)[pi]sigma(t)^-1` also
centralizes `sigma(Gamma)`. That is, `pi'_n = s(t) pi_n s(t)^-1` satisfies
`max_{gamma in S} u(pi' s(gamma) != s(gamma) pi') -> 0`.

For `A = A_C in A_n`, let `beta_C` be the bijection of `C` equal to
`tau alpha_A tau^-1` on `tau A` and to the identity on `C \ tau A`. Let
`E_n = s(t)(B_n ∪ pi^-1 B_n) ∪ (Y \ Y'')`, a set of mass `o(1)`. Then
`pi' = beta_C` on `C \ E_n`. On `tau A`, if `y, alpha y notin B_n`, then
`pi'(tau y) = s(t) alpha y = tau alpha y`. On `C \ tau A`, the points of
`Y''` lie in `tau A'` for Gamma-orbits `A'` with `tau A' subset C` and
`A' != A_C`; these are not in `A_n`, because `A_{C'} = A'` would force
`C' = C`, and there `pi' = id` off `E_n`. So

```text
sum_C max_{gamma in S} |{z in C : beta_C s(gamma) z != s(gamma) beta_C z}|
    <= |S| (u(pi' s(gamma) != s(gamma) pi') + 2 u(E_n)) |Y|  =  o(|Y|).
```

Choose `eps_0 > 0` with `4 eps_0 / kappa^2 <= delta'/2` and
`4 eps_0 / kappa^2 < 1/2`. By Markov's inequality, the blocks with
relative defect `> eps_0` carry mass `o(1)`. On every other block,
Corollary R1 gives a Gamma-automorphism of `C` agreeing with `beta_C` on
at least `(1 - delta'/2)|C|` points. So it agrees with
`tau alpha_A tau^-1` on at least `(1 - delta'/2)|C| - leak(C) >=
(1 - delta')|C|` points of `tau A`, contradicting `A in A_n`. So the whole
of `A_n` lies in the `o(1)` mass of high-defect blocks. ∎(3)

The Lambda-automorphisms of `tau A` are exactly the maps
`tau alpha tau^-1` with `alpha` a Gamma-automorphism of `A`, since
`tau : A -> phi^*(tau A)` is a Gamma-isomorphism. So a
`(delta, delta')`-good orbit gives a configuration
`(C, a = tau A_C)` satisfying the hypotheses of (LHR-adm).

## Step 4. The reduction (part (4))

By `mui-pair-measures-orbital-reduction` (2') and (3), at a Gamma-exact
lift, (MUI-J) follows once, for every MUI orbital `nu` and every
`t in T`, the push `psi(t)_* nu` is internally Gamma-invariant. (TV
approximation by orbital measures commutes with the push.) Let `nu_n =
sum_O w_O unif(O)` over the (untwisted) `psi(Gamma)`-orbits `O` of
`W_n`, with `w_O >= 0` and `sum_O w_O = 1`.

Fix `c > 0` and take `delta, delta'` from (LHR-adm). Let `G_n` be the union
of the `(delta, delta')`-good orbits. By (3), `u(Y \ G_n) -> 0`, and by
MUI, `nu_n(W_n \ (G_n x G_n)) -> 0`. Since `G_n x G_n` is
`psi(Gamma)`-invariant, the orbits `O` not contained in it carry weight
`o(1)`. Discard them. Each remaining `O` lies in `A x B` for good `A`, `B`.
Its image `O' = (tau x tau)(O)` is one Lambda-orbit in `a x b`, where
`a = tau A subset C` and `b = tau B subset D`, and the configuration
`(C, D, a, b)` satisfies the hypotheses of (LHR-adm). So
`|O'| >= (1 - c)|Gamma O'|`, whence
`||unif(O') - unif(Gamma O')||_TV = 1 - |O'|/|Gamma O'| <= c`. Since
`tau x tau` is a bijection on `O`, `(tau x tau)_* unif(O) = unif(O')`. By
(1),

```text
psi(t)_* nu_n  ≈_{o(1)}  sum_O w_O unif(O')  ≈_{c}  sum_O w_O unif(Gamma O'),
```

and the last measure is exactly `psi(Gamma)`-invariant. Hence
`limsup ||psi(gamma)_* psi(t)_* nu_n - psi(t)_* nu_n||_TV <= 2c` for every
`gamma`. Since `c` is arbitrary, `psi(t)_* nu` is internally
Gamma-invariant. Then (MUI-J) holds, and by
`mui-commutant-reduces-to-internal-joining-invariance` (1), so does
(MUI-C). ∎(4)

## Step 5. The subfield model (part (5))

Let `Q = q^k`, and let `rho_k`, `Z_k = P^2(F_{Q^2})`, `a` be as in (5).

*The images.* `rho_k(R_+) = F_q[alpha, beta] = F_{Q^2}`, since
`F_q(alpha) = F_{Q^2}` already. `t R_+ = F_q[x_1, x_1 x_2, x_3, ...,
x_d]`, and `rho_k` sends its generators to `0, 0, beta, 0, ..., 0`, so
`rho_k(t R_+) = F_q[beta] = F_Q`. Over a field, `EL_3 = SL_3`, and
`rho_k(EL_3(S)) = EL_3(rho_k S)` for a subring `S`. So `Gamma` acts on
`Z_k` through `SL_3(F_{Q^2})` and `Lambda_t = EL_3(t R_+)` acts through
`SL_3(F_Q)`. The compressor is legitimate: `t = I + E_12 in SL_d(Z)` and
`t R_+ subset R_+`.

*Counting.* `|Z_k| = Q^4 + Q^2 + 1`, and the rational points number
`Q^2 + Q + 1`, so `|a| = Q^4 - Q`. For `z in a`, `z^Q != z` (entrywise
Frobenius), and the line `L(z) = <z, z^Q>` is Frobenius-stable, hence
`F_Q`-rational. `z` lies on no second rational line, since two rational
lines meet in a rational point. Each rational line is a `P^1(F_{Q^2})`
containing `Q^2 - Q` non-rational points, and
`(Q^2 + Q + 1)(Q^2 - Q) = Q^4 - Q`, which checks the count.

*Transitivity of `SL_3(F_Q)` on `a`.* `SL_3(F_Q)` is transitive on
rational lines. The stabilizer of `<e_1, e_2>` contains
`diag(g, det g^-1)` for `g in GL_2(F_Q)`, which induces all of
`PGL_2(F_Q)` on the line. `PGL_2(F_Q)` has order `Q^3 - Q`. It is
transitive on `P^1(F_{Q^2}) - P^1(F_Q)`: an element fixing a non-rational
`z` also fixes `z^Q`, so it lies in a non-split torus of order `Q + 1`, and
`(Q^3 - Q)/(Q + 1) = Q^2 - Q`. So `a` is one `Lambda_t`-orbit, and
`leak = (Q^2+Q+1)/(Q^4+Q^2+1) = O(Q^-2)`.

*The Frobenius graph.* `F(z) = z^Q` commutes with `SL_3(F_Q)`, because
`(g z)^Q = g^{(Q)} z^Q = g z^Q` for `F_Q`-rational `g`. So `F` is a
Lambda_t-automorphism of `a`, and its graph `O = {(z, Fz)}` is the image
of the Lambda_t-orbit `a` under `z -> (z, Fz)`, hence one Lambda_t-orbit,
of size `Q^4 - Q`, inside `a x a`. `SL_3(F_{Q^2})` is 2-transitive on
`P^2(F_{Q^2})`, and `Fz != z`, so `Gamma O` is the whole off-diagonal
orbit, of size `N(N-1)` with `N = Q^4 + Q^2 + 1`. So
`|O|/|Gamma O| < 1/N = O(Q^-4)`.

*No admissibility.* A Gamma-automorphism `theta` of a 2-transitive set
`Z` with `|Z| >= 3` is trivial: `theta(x)` is fixed by `Stab(x)`, which is
transitive on `Z - {x}`, so `theta(x) = x`. Thus `F` agrees with a
Gamma-automorphism of `C = Z_k` at no point of `a`. So the configuration
`(C = D = Z_k, a = b)` satisfies every hypothesis of (LHR-adm) except the
admissibility clause, with `delta = O(Q^-2)`. Its orbit `O` violates the
conclusion for every `c < 1 - O(Q^-4)`. Letting `k -> infinity` defeats
every `(c, delta)` with `c < 1`, so the admissibility-free statement is
false.

*Where the model is excluded.* In a Gamma-exact lift, a block
`(C, tau A_C)` of this type is not `(delta, delta')`-good for any
`delta' < 1 - O(Q^-2)`, because `tau^-1 F tau` is a Gamma-automorphism of
`A_C`. By (3) such blocks carry mass `o(1)`. The input that excludes them
is Theorem 4.1, through the permutation `pi` of Step 3. Theorem C alone
does not: the model satisfies the conclusion of Step 2 (a single large
Lambda-orbit per block). So no argument that uses Theorem C together with
finite information about individual Gamma-sets can prove (MUI-O). It must
use Theorem 4.1 (or more global structure of `G`), exactly as (4) does.
∎(5)


## Step 6. The antiflag block (part (6))

*The images.* `rho : R_+ -> Rbar = F_2[e]/(e^2)` sends `x_2 -> e` and
every other `x_i -> 0`. `Rbar` is local, so `EL_3(Rbar) = SL_3(Rbar)`, and
`rho(Gamma) = EL_3(Rbar) = SL_3(Rbar) =: Gammabar`, of order
`|SL_3(F_2)| * |sl_3(F_2)| = 168 * 2^8 = 43008`. Since `t` acts on `R` by a
ring automorphism, `Lambda_t = EL_3(t R_+)`. The generators
`x_1, x_1 x_2, x_3, ..., x_d` of `t R_+` all map to `0`, so
`rho(t R_+) = F_2` and `rho(Lambda_t) = SL_3(F_2) =: Lambdabar`, the
constant matrices. `Aut(Rbar / F_2)` is trivial (`e -> c e` needs
`c in F_2^*`), so this is a block with no Galois twist, which is the
case Step 5 left open.

*The search.* Let `pi : Gammabar -> Lambdabar` be reduction mod `e`, with
kernel `K = I + e sl_3(F_2)`, an elementary abelian group of order `2^8`
on which `Lambdabar` acts by conjugation. `Lambdabar` is a complement to
`K`. For a subgroup `H` put `M = pi(H)` and `V = H ∩ K`. Then `V` is an
`M`-submodule of `K`, and `H / V` is a complement to `K / V` in
`K M / V`. Conversely, every such complement lifts to a subgroup `H`. The
script enumerates:

- `M` of order 24 in `Lambdabar`, up to conjugacy (the two classes of
  `S_4`, point and line stabilizers);
- `V` of codimension 2 in `K` and `M`-invariant, found as the common
  kernels of 2-dimensional `M`-invariant subspaces of the dual `F_2^8`;
- complements to `K/V` in `KM/V` (`ComplementClassesRepresentatives`).

For each resulting `H` of index 28, `Lambdabar` is transitive on
`Gammabar / H` iff `Gammabar = H Lambdabar`, iff
`|H ∩ Lambdabar| * |Gammabar| = |H| * |Lambdabar|`, iff
`|H ∩ Lambdabar| = 6`. Blocks passing this test are acted on by
`FactorCosetAction`, and the orbits on ordered pairs and the centralizers
in `Sym(28)` are computed. The script is
`research/artifacts/dual-number-antiflag-block-2026-09-18.g`. Run with
`nice -n 10 timeout 1200 gap -q -o 2g ... < /dev/null`, it prints

```text
|Gamma-bar|=43008 |K|=256 |Lambda-bar|=168
BLOCK: |H|=1536 |H cap K|=64 |H cap Lambda|=6  faithful=true
  Gamma-bar pair orbits:  [ 28, 84, 672 ]
  Lambda-bar pair orbits: [ 28, 84, 84, 84, 168, 168, 168 ]
  |Aut_Gamma|=1  |Aut_Lambda|=1
done
```

*Hand checks.* Everything the argument uses can be cross-checked without
the computer, except the Gamma-orbit count on pairs.

- `Lambdabar` acts on `C` transitively with point stabilizer
  `H ∩ Lambdabar` of order 6. `SL_3(F_2) = PSL_2(7)` has one class of
  subgroups of order 6, namely `S_3 = N(C_3)`, the stabilizer of an
  antiflag (a point `p` and a line `l` with `p` not on `l`; there are
  `7 * 4 = 28` of them). So `C` is the Lambdabar-set of antiflags.
- `|H K| = |H| |K| / |V| = 6144`, of index 7. So `C` fibres
  Gamma-equivariantly over the 7-point set `Gammabar / HK`, with fibres of
  size 4. On antiflags this is `(p, l) -> p` or `(p, l) -> l`, according
  to the class of `M`. The Gamma-orbits on pairs are then the diagonal
  (28), same fibre off the diagonal (`28 * 3 = 84`), and different fibres
  (`28 * 24 = 672`). The computation says Gammabar is transitive on the
  last set, so its rank is 3.
- `Lambdabar` keeps the diagonal and the same-fibre set (the point
  stabilizer `S_4` acts on the 4 lines missing `p` as `S_4`, which is
  2-transitive). It splits the 672 different-fibre pairs according to
  the incidence pattern of `(p, l, p', l')`, into orbits of sizes
  `84 + 84 + 168 + 168 + 168 = 672`.
- `Aut_Lambda(C) = N_Lambdabar(S_3) / S_3 = 1`, because `S_3 = N(C_3)` is
  self-normalizing. `Aut_Gamma(C) = N_Gammabar(H) / H`, and a nontrivial
  element would give a second pair orbit of size 28. There is only the
  diagonal, so `Aut_Gamma(C) = 1`.

*Conclusion.* Take `Z = C = D` and `a = b = C`, so `leak = 0`. Every
Lambda_t-automorphism of `a` is the identity, which is the restriction of
the identity Gamma-automorphism, so the admissibility clause holds with
`delta' = 0`. The Lambda_t-orbit `O` of size 84 inside the Gamma-orbit of
size 672 has `|O| = |Gamma O| / 8`. So `|O| >= (1 - c)|Gamma O|` fails
for every `c < 7/8`, and (LHR-adm) fails at `c = 1/2` for all
`delta, delta'`. ∎(6)

A wider scratch search, not part of the artifact, lets `M` range over all
subgroup classes of `Lambdabar` and `V` over all `M`-invariant subgroups
of codimension at most `log_2 |M|`. It finds further Lambda-transitive
blocks with `|Aut_Lambda| = |Aut_Gamma|`, of sizes 42, 56 and 84. These
are admissible, because `Aut_Gamma(C) subset Aut_Lambda(C)` always holds,
so equal orders force equality. Their smallest ratio
`|O| / |Gamma O|` is `1/16` (at `n = 56`). They are not needed for (6).

## What this leaves

Steps 1--4 show that at Gamma-exact lifts the sofic data enter (MUI-O)
only through leak-freeness and admissibility of single blocks. Step 6
exhibits a finite block that has both and still splits a Hecke double
coset. So no proof of (MUI-O) can run block by block from Theorems C and
4.1. Nor is the antiflag block excluded by the finite theory: in a finite
`G`-set, Theorem C applied to `Y x Y` would make Gamma-orbits of pairs
`G`-invariant, and the block fails that. But in the sofic setting this
pair-level form of Theorem C is exactly what is in question
(`mui-pair-measures-orbital-reduction`).

The problem is now (REAL) of the claim. Is there a Gamma-exact sofic lift
of `G` in which a fixed fraction of the mass sits in Gamma-orbits
`A ≅ phi_t^*(C)` that `s_n(t)` sends onto antiflag blocks `C`? A positive answer is expected to refute (MUI-O) at that lift: by (1),
the uniform measure on an 84-element Gamma-orbit of `A x A` pushes forward
to the uniform measure on a Lambda_t-orbit that fills only `1/8` of its
Gamma-orbit of pairs, so it is far from Gamma-invariant. The remaining
point, not proved here, is that such orbital measures occur inside an MUI
Hecke mixture. Through part (4) run backwards, that would also refute
(MUI-J) and (MUI-C). A negative answer has
to use constraints that tie different compressors together: `s_n(t)`,
`s_n(t^-1)`, `s_n(t')` for `t' in T` and the relations of `G` all act on
the same `Y_n`, and each must again produce leak-free, admissible blocks.
