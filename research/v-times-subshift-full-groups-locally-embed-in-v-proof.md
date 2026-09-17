---
rg: 2
id: v-times-subshift-full-groups-locally-embed-in-v-proof
kind: route
title: Periodic approximation of V-times-subshift full groups by Higman–Thompson groups
target: v-times-subshift-full-groups-locally-embed-in-v
requires:
  - thompson-v-has-haagerup-property
  - km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4
---

The notation is that of the target claim.
- `X = C x Y`, and `sigma` is the left shift.
- For `x` in `A^Z` and `R ≥ 0`, `x[i;R]` is the word `x_{i-R} ... x_{i+R}`.
- For a word `v` in `{0,1}^*`, `[v] ⊆ C` is its cylinder.

## Step 0. Non-periodic points are dense, and the cocycle is well defined

**Lemma 0.** If `Y` is infinite and irreducible, then the non-periodic points are
dense in `Y`.

*Proof.*
1. Suppose some nonempty clopen `U ⊆ Y` consists of periodic points.
2. Each set `Per_k(Y) = {y : sigma^k y = y}` is finite. So `U` is countable and
   compact, and by Baire it has an isolated point `q`.
3. Then `q` is periodic and isolated in `Y`: `{q} = {y in Y : y[0;R0] = q[0;R0]}`
   for some `R0`. Put `u = q[0;R0]`.
4. Let `w` be in `L(Y)`. Irreducibility gives `v` with `uvw` in `L(Y)`.
5. So some `y` in `Y` has `y[0;R0] = u` and contains `w` further to the right.
   This `y` equals `q`, so `w` occurs in `q`.
6. Hence `L(Y) ⊆ L(q)` and `Y ⊆` the orbit closure of `q`, which is finite.
   This is a contradiction. ∎

An element `g` of `[[G]]` is a homeomorphism of `X`. Locally,
`g(vc', y) = (w c', sigma^n y)`, with a prefix replacement `v -> w` and an
integer `n`, both locally constant.
- On non-periodic `y`, the integer `n` is determined by `g`. By Lemma 0 and
  continuity, it extends uniquely to a continuous cocycle `n_g : X -> Z`.
- The cocycle identity `n_{gh}(x) = n_g(hx) + n_h(x)` holds on a dense set, and
  so everywhere.
- If `g = id`, then `n_g = 0`.

(If `Y` is finite, `[[G]]`, as a group of homeomorphisms of the finite union of
Cantor sets `X`, lies in `V_{2,|Y|} ≅ V`, and there is nothing to prove. From now
on `Y` is infinite.)

## Step 1. Finite rules

Let `S` be a finite symmetric generating set of `Gamma`. By compactness there
are `L, R, D ≥ 0` with the following property.
- For each `s` in `S` there is a function
  `Phi_s : {0,1}^L x L_{2R+1}(Y) -> {0,1}^* x [-D, D]`, `(v, u) ↦ (w, n)`.
- For all `c = vc'` in `C` and all `y` in `Y` with `y[0;R] = u`:
  `g_s(c, y) = (w c', sigma^n y)` and `n_{g_s}(c, y) = n`.

**Formal action.** Take any `xi` in `A^Z` and any position `i` in `Z` such that
`xi[i;R]` is in `L(Y)`. Define
`T_s(c, xi, i) = (w c', xi, i + n)`, where `(w, n) = Phi_s(c_{[1,L]}, xi[i;R])`.

For a word `s_1 ... s_k` over `S`, set `T_{s_1...s_k} = T_{s_1} ∘ ... ∘ T_{s_k}`.
Put `R_k = R + (k-1)D`.

**Lemma 1 (locality).**
- `T_{s_1...s_k}(c, xi, i)` is defined when every `(2R+1)`-window of `xi` inside
  `[i - R_k, i + R_k]` is in `L(Y)`.
- Its `C`-output and its total displacement depend only on `c` and `xi[i;R_k]`.

*Proof.* By induction on `k`. The `j`-th step reads a radius-`R` window centred
within distance `(j-1)D` of `i`. ∎

**Lemma 2 (agreement with `Y`).** Let `y` be in `Y`, and let `W = s_1...s_k`
represent `g_W` in `Gamma`. Then `T_W(c, y, 0) = (c'', y, m)` with
`g_W(c, y) = (c'', sigma^m y)` and `m = n_{g_W}(c, y)`.

*Proof.* We have `g_s(c, sigma^i y) = (w c', sigma^{i+n} y)`, which matches
`T_s(c, y, i)` under `(c, y, i) <-> (c, sigma^i y)`. Iterate, and use the
cocycle identity. ∎

## Step 2. Periodic approximations

**Lemma 3.** Let `Y` be irreducible, let `m ≥ 1`, let `u_1, ..., u_k` be in
`L(Y)`, and let `M ≥ 1`. Then there are a word `P` and an integer `N` that is a
multiple of `|P|` with `N ≥ M`, such that `p = P^∞` (bi-infinite, period `|P|`)
has two properties:
- every `m`-window of `p` is in `L(Y)`;
- every `u_j` occurs in `p`.

*Proof.*
1. Pad each `u_j` inside `L(Y)` to length at least `m`. Irreducible languages are
   extendable (apply irreducibility to `u, u`).
2. Inductively choose `v_1, ..., v_k` with
   `u_1 v_1 u_2 ... u_k v_k u_1` in `L(Y)`, using irreducibility once per step.
3. Put `P = u_1 v_1 ... u_k v_k`.
4. Any `m`-window of `P^∞` has the form `P^∞_{[j, j+m)}` with `0 ≤ j < |P|`.
   Since `m ≤ |u_1|`, it lies inside `P u_1`, which is in `L(Y)`, and `L(Y)` is
   factorial.
5. Take `N = |P| * ceil(M / |P|)`. ∎

## Step 3. The approximating action

Let `p` and `N` be as in Lemma 3 with `m ≥ 2R_2 + 1`. On `X_N = C x Z/N`, define
`rho_p(s)(c, i) = (w c', i + n mod N)`, where `(w, n) = Phi_s(c_{[1,L]}, p[i;R])`.
- This is well defined because `p` has period dividing `N` and every window is in
  `L(Y)`.
- By Lemma 1, the product `rho_p(s_1) ... rho_p(s_k)` is computed by `T_{s_1...s_k}`
  on `(c, p, i)`, reduced mod `N`, whenever `m ≥ 2R_k + 1`.

**Lemma 4 (relators).** Let `W` be a word of length `k` with `g_W = 1` in `Gamma`,
and let `m ≥ 2R_k + 1`. Then `rho_p(W) = id` on `X_N`.

*Proof.*
1. Fix `(c, i)`, and put `u = p[i;R_k]`. It is in `L(Y)`, so some `y` in `Y` has
   `y[0;R_k] = u`.
2. By Lemmas 1 and 2, `T_W(c, p, i)` has the same `C`-output `c''` and the same
   displacement `m'` as `T_W(c, y, 0)`.
3. There `g_W(c, y) = (c, y)` and `n_{g_W} = 0`, so `c'' = c` and `m' = 0`.
4. Hence `rho_p(W)(c, i) = (c, i)`. ∎

**Consequences.**
- Applying Lemma 4 to `W = s s^{-1}` and `W = s^{-1} s` (length 2) shows that
  `rho_p(s)` is a bijection with inverse `rho_p(s^{-1})`.
- Each `rho_p(s)` is a homeomorphism of `⊔_N C` given piecewise, on finitely many
  cylinders, by prefix replacements. So `rho_p(s)` lies in the Higman–Thompson
  group `V_{2,N}`.
- Higman's theorem gives `V_{2,N} ≅ V_{2,1} = V` for all `N`.
- So `rho_p` extends to a homomorphism `F(S) -> V_{2,N}`, and Lemma 4 holds for
  reduced and unreduced words alike.

**Lemma 5 (witnesses).** Let `W` be a word of length `k` with `g_W ≠ 1`. Then
there is a word `u_W` in `L_{2R_k+1}(Y)` with the following property. If `u_W`
occurs in `p`, `m ≥ 2R_k + 1` and `N > kD`, then `rho_p(W) ≠ id`.

*Proof.*
1. The set `{x : g_W x ≠ x}` is nonempty and open. By Lemma 0 it contains some
   `(c, y)` with `y` non-periodic.
2. Write `g_W(c, y) = (c'', sigma^{m'} y)`. Either `c'' ≠ c`, or `m' ≠ 0`.
3. Put `u_W = y[0;R_k]`, and let `i` be an occurrence centre of `u_W` in `p`.
4. By Lemmas 1 and 2, `rho_p(W)(c, i) = (c'', i + m' mod N)`.
5. Since `|m'| ≤ kD < N`, this differs from `(c, i)`. ∎

## Step 4. Proof of the theorem

**Item 1.**
1. Given a finite `F ⊆ Gamma`, choose for each `a` in `F` a word `W_a` over `S`
   of length at most `r`. Assume `1` is in `F`, with `W_1` empty.
2. Put `m = 2R_{3r} + 1` and `M = 2rD + 1`.
3. Apply Lemma 3 to the witness words `u_{W_a W_b^{-1}}` for `a ≠ b` in `F`
   (each of length `2R_{2r}+1 ≤ m`), producing `p` and `N`.
4. Define `phi(a) = rho_p(W_a)`.
5. Partial homomorphism: suppose `a, b, ab` are in `F`. The word
   `W_a W_b W_{ab}^{-1}` has length at most `3r` and represents `1`. By Lemma 4,
   `phi(a) phi(b) = phi(ab)`.
6. Injectivity: for `a ≠ b`, the word `W_a W_b^{-1}` has length at most `2r` and
   represents `g ≠ 1`. By Lemma 5, `phi(a) ≠ phi(b)`.
7. Hence `phi : F -> V_{2,N} ≅ V` is an injective partial homomorphism, and
   `Gamma` is locally embeddable into `V`.
   - Here `rho_p` is a homomorphism from `F(S)` that kills every relator of
     length at most `3r`. Any bound can be arranged by enlarging `r`.

**Item 2.**
1. Let `Gamma = <S | Q>` with `Q` finite, and choose `r` at least every relator
   length.
2. Then `rho_p` kills `Q`, so it factors through a homomorphism
   `Gamma -> V_{2,N} ≅ V`.
3. That homomorphism agrees with `phi` on `F`, so it is injective on `F`.

**Item 3.**
1. Apply item 2 with `F = {1, g}` for some `g ≠ 1`. This gives
   `psi : Gamma -> V` with `psi(g) ≠ 1`.
2. `ker psi` is normal and proper, and `Gamma` is simple, so `ker psi = 1`.

**Item 4.**
1. Every homomorphic image of a Kazhdan group is Kazhdan.
2. Every subgroup of `V` has the Haagerup property
   (`thompson-v-has-haagerup-property`), and Kazhdan groups with the Haagerup
   property are finite.
3. So each map from item 2 has finite image and is injective on `F`, and `Gamma`
   is residually finite.
4. If `Gamma` is also simple, item 3 embeds it in `V`, so it is finite. ∎

## Step 5. Corollary

1. By `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`, there is an
   infinite finitely presented simple Kazhdan group `Lambda`.
2. If `Lambda ≤ [[G_V x (Z ⋉ Y)]]` for some infinite irreducible `Y`, item 4
   makes `Lambda` finite. This is a contradiction.
3. The finite-`Y` case is excluded directly. Then `X` is a finite disjoint union
   of Cantor sets, `[[G]]` (as a group of homeomorphisms) lies in
   `V_{2,|Y|} ≅ V`, and the Haagerup argument applies.
4. The alternating groups `A(G|_{C x Y})` are subgroups, so the conclusion
   passes to them.

## Calibration checks

- `V ≤ [[G]]` (maps with trivial shift), and `V` is LE-V. So `V` is the smallest
  approximating class the theorem could use.
- If the factor `G_V` is removed, `C` becomes a point and `V_{2,N}` becomes
  `Sym(N)`. The same argument then gives that `[[Z ⋉ Y]]` is LEF for irreducible
  `Y`. For minimal `Y` this is Grigorchuk–Medynets' theorem, and it agrees with
  `periodic-approximable-subshifts-host-no-fp-simple-group`.
- The theorem makes no false claims about `V` or its known f.p. simple relatives:
  - `V` itself embeds in `V`.
  - Every f.p. subgroup of `[[G]]` inherits a solvable word problem from `V`,
    because it is residually V in the "injective on finite sets" sense. This
    matches the computability of the action.

## Remark: where a host must differ

The proof uses exactly two inputs.
1. Finite approximations of the shift factor that realise arbitrary finite sets
   of patterns of the language with large stabilizers.
2. On the finite side, a group acting on `C x (finite set)` by prefix
   replacements. Every such group lies in some `V_{2,N}`, which is Haagerup.

Step 6 isolates input 1 as (PA*) for an arbitrary acting group.

## Step 6. Extension to subshifts over other acting groups (Theorem′)

This writes out the remark above. `Delta` is a finitely generated group acting
on `A^Delta` by `(mu . x)(nu) = x(mu^{-1} nu)`. For finite `K ⊆ Delta`,
`L_K(Y) = {y|_K : y in Y}`.

**Definition (PA*).** A subshift `Y ⊆ A^Delta` has (PA*) if
- (TF) the points of `Y` with trivial stabilizer are dense in `Y`; and
- for every finite `K ∋ e`, every finite `U ⊆ L_K(Y)` and every finite
  `B ⊆ Delta \ {e}`, there are a finite `Delta`-set `S` and a
  `Delta`-equivariant map `pi : S -> A^Delta` such that
  1. `pi(t)|_K` is in `L_K(Y)` for every `t` in `S`;
  2. for every `u` in `U` some `t` in `S` has `pi(t)|_K = u` and
     `Stab_Delta(t) ∩ B = ∅`.

**Theorem′.** If `Y` has (PA*), items 1-4 of the theorem hold for every finitely
generated `Gamma ≤ [[G_V x (Delta ⋉ Y)]]`, with `V_{2,|S|} ≅ V` as target.

*Proof.* Steps 0-4 go through with the following changes.

1. *Cocycle.* Locally `g(vc', y) = (w c', n . y)` with `n` in `Delta` locally
   constant. By (TF), `n` is determined on a dense set, so it extends uniquely to
   a continuous `n_g : X -> Delta`. The identity
   `n_{gh}(x) = n_g(hx) n_h(x)` holds, and `n_g = e` when `g = id`.
2. *Finite rules.* By compactness there are `L`, a finite `K ∋ e` and a finite
   `D ⊆ Delta` with maps `Phi_s : {0,1}^L x L_K(Y) -> {0,1}^* x D`, such that
   `g_s(vc', y) = (w c', n . y)` and `n_{g_s}(vc', y) = n` whenever
   `(w, n) = Phi_s(v, y|_K)`.
3. *Formal action.* For `q` in `A^Delta` with `q|_K` in `L_K(Y)`, put
   `T_s(c, q) = (w c', n . q)` with `(w, n) = Phi_s(c_{[1,L]}, q|_K)`.
   - Let `D_j` be the set of products of at most `j` elements of `D`, and put
     `K_k = D_{k-1}^{-1} K`.
   - After `j` steps the point is `m_j . q` with `m_j` in `D_j`. The next step
     reads `(m_j . q)|_K`, which is the restriction of `q` to `m_j^{-1} K ⊆ K_k`,
     translated.
   - So if `q|_{K_k} = y|_{K_k}` for some `y` in `Y`, then `T_W(c, q)` is defined
     for every word `W` of length `k`. It equals `(c'', m . q)`, where
     `g_W(c, y) = (c'', m . y)` and `m = n_{g_W}(c, y)` (the cocycle identity).
4. *Approximation.* Fix `r`. Put `K' = K_{3r}` and `B = D_{2r} \ {e}`, and take
   `U` to be the witness patterns below. (PA*) gives `S` and `pi`. Define
   `rho(s)(c, t) = (w c', n . t)` with `(w, n) = Phi_s(c_{[1,L]}, pi(t)|_K)` on
   `C x S`.
   - Equivariance gives `pi(n . t) = n . pi(t)`. So the composite
     `rho(s_1) ... rho(s_k)` at `(c, t)` has `C`-output `c''` and moves `t` to
     `m . t`, where `(c'', m)` is computed by `T_W` at `(c, pi(t))`.
5. *Relators* (length `k ≤ 3r`, `g_W = 1`). By clause 1 for `K'`, `pi(t)|_{K_k}`
   is some `y|_{K_k}` with `y` in `Y`. Then `c'' = c` and `m = n_{g_W}(c, y) = e`,
   so `rho(W) = id`.
   - With `W = s s^{-1}`, each `rho(s)` is a bijection. It is a piecewise prefix
     replacement on `|S|` copies of `C`, so it lies in `V_{2,|S|} ≅ V`.
6. *Witnesses* (length `k ≤ 2r`, `g_W ≠ 1`).
   - By (TF) choose `(c, y)` with `y` free and `g_W(c, y) = (c'', m . y) ≠ (c, y)`.
     Then `c'' ≠ c` or `m ≠ e`.
   - Put `u_W = y|_{K'}`, and use clause 2 to pick `t` with `pi(t)|_{K'} = u_W` and
     `Stab(t) ∩ B = ∅`.
   - Then `rho(W)(c, t) = (c'', m . t)`. If `c'' = c`, then `m` is in
     `D_k \ {e} ⊆ B`, so `m . t ≠ t`.
7. Items 1-4 now follow word for word as in Step 4. ∎

**Examples of (PA*).**
- (E1) *Infinite irreducible `Z`-subshifts.* (TF) is Lemma 0. Take
  `S = Z/N` and `pi(i) = sigma^i p`, with `p` and `N` from Lemma 3 and
  `M > max |B|`. Equivariance holds because `N` is a multiple of the period
  `|P|`. The stabilizer is `NZ`, which misses `B`. So Theorem′ contains the
  theorem.
- (E2) *The full shift `A^Delta`, `|A| ≥ 2`, over an infinite residually finite
  `Delta`.*
  - (TF): for `lambda ≠ e` the set `Fix(lambda)` is closed with empty interior.
    Any cylinder on a finite `F` can be extended with
    `x(nu) ≠ x(lambda^{-1} nu)` for some `nu` outside `F ∪ lambda F`. Now apply
    Baire.
  - (PA*): choose `mu_1, ..., mu_k` so that the sets `mu_j^{-1} K` are pairwise
    disjoint, which is possible since `Delta` is infinite. Choose a finite-index
    normal `Delta_0` that misses `B` and every `a^{-1} b ≠ e` with
    `a, b` in `∪_j mu_j^{-1} K`.
  - Put `S = Delta / Delta_0`. Let `p` be the `Delta_0`-invariant point with
    `p(mu_j^{-1} kappa) = u_j(kappa)`, arbitrary elsewhere, and set
    `pi(mu Delta_0) = mu . p`. The stabilizers are all `Delta_0`.
- (E3) *Topologically free minimal `Delta`-subshifts with (PA) in the sense of
  `periodic-approximable-subshifts-host-no-fp-simple-group`.*
  - Say `u` occurs in `x` at `mu` when `(mu . x)|_K = u`, that is,
    `x(mu^{-1} kappa) = u(kappa)` for `kappa` in `K`.
  - Fix `x` in `Y`. By minimality every `u` in `U` occurs in `x`, say at `mu_u`.
    Apply (PA) with a window `W` that contains every `mu_u^{-1} K`, and with
    `B' = ∪_u mu_u^{-1} B mu_u`.
  - Take `S` to be the finite orbit of the resulting `y`, and `pi` the inclusion.
    Clause 1 is the last clause of (PA). Since `y|_W = x|_W`, the point
    `mu_u . y` carries `u` on `K`. Its stabilizer `mu_u Stab(y) mu_u^{-1}` misses
    `B`, because `Stab(y)` misses `B'`.

**Calibration.**
- (E2) with `Delta = SL_3(Z)` gives a host containing `SL_3(Z)`, which is
  finitely presented and Kazhdan. Theorem′ item 4 only says it is residually
  finite, which is true.
- An infinite simple group `Delta` has only trivial finite `Delta`-sets, so
  clause 2 fails for every `B ≠ ∅`. Hosts over the km-246 lattice escape
  Theorem′, as they must, since they contain the lattice.
