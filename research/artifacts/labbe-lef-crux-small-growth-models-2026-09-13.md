# Finite models of Labbé's derived full group with small Schreier growth are trivial (2026-09-13)

Lane `ex2-labbe-lef-crux`. Target: `labbe-relator-shifts-carry-patch-rich-periodic-points` (crux (C1) of
`labbe-shift-derived-full-group-is-lef`).

**Verdict: the crux is false, for every finite generating set, every extension and every radius.** Status:
ESTABLISHED, unreviewed. Proved here:
- **Theorem A** (Section 2): every action of `Gamma` on a set whose Schreier balls grow like `o(k^4)` splits
  into fixed points and standard orbits.
- **Corollary B** (Section 3): in a finite model that satisfies all short relators and has quadratic ball
  growth, every `r`-ball is trivial or orbital.
- **Theorem C** (Section 4): a finite `F(S)`-set whose balls are all trivial or orbital carries the trivial
  action.
- **Corollary D** (Section 5): for `n >= n_0(S, R)`, every periodic point of every relator shift `Z_n`
  carries the trivial action, so (H1) fails.

The engine is Matte Bon's classification of confined subgroups (arXiv:1801.10133, TeX source read on MSI).

## 0. Setup

- `Omega = Omega_U`, Labbé's 19-tile Wang shift: minimal, aperiodic, free, and a nearest-neighbour SFT
  (`minimal-aperiodic-wang-shift-exists`). `G = Z^2 ~ Omega` is its transformation groupoid, which is minimal
  and effective.
- `Gamma = D([[G]])` is finitely generated, infinite and simple, and equals Nekrashevych's `A(G)`
  (`minimal-z2-subshift-derived-full-groups-are-fg-simple`). Fix a finite symmetric generating set `S`, and
  `R` with `|c_s| <= R` for `s ∈ S`.
- An `F(S)`-set is a set with a permutation for each `s ∈ S`, the one for `s^{-1}` being inverse to the one
  for `s`. Its Schreier graph has an `s`-edge `v -> s v`, and `B_k(v)` is the ball of radius `k`.
- `v` is *`n`-exact* if every word of length `<= 2n` that is trivial in `Gamma` fixes every vertex of
  `B_n(v)`. An `F(S)`-set is *`n`-exact* if all its vertices are.
- **Standard orbit.** For `x ∈ Omega`, `Gamma x` is the `Z^2`-orbit of `x`: 3-cycles realise every germ. Here
  `g` acts on `u ∈ Z^2`, identified with `sigma^u x`, by `u -> u + c_g(sigma^u x)`.
- **Orbital ball.** A rooted labelled `r`-ball is *orbital* if it is isomorphic to `B_r(x)` in `Gamma x` for
  some `x ∈ Omega`, and *trivial* if it is a single vertex with a loop for every `s`.

**Import (Matte Bon, arXiv:1801.10133, Theorem `t-confined`, TeX `hom_full_revised19.tex` line 1793, read
verbatim).**
- *Setting:* `G` is a minimal effective étale groupoid over a Cantor space, and `H ≤ F(G)`.
- *Equivalent conditions:*
  - (ii) `H` is confined by `A(G)`: some finite `P ⊆ F(G) \ {1}` meets every `A(G)`-conjugate of `H`;
  - (iii) there is a unique finite `Q ⊆ X`, possibly empty, with `St^0_{A(G)}(Q) ≤ H ≤ St_{F(G)}(Q)`.
- *Notation:* `St^0` fixes a neighbourhood of `Q` pointwise; `St` stabilises `Q` setwise.
- *Also:* `St^0_{A(G)}(∅) = A(G)`.

## 1. Two elementary lemmas

**Lemma 1.1 (germs are trivial).** For `x ∈ Omega`, `St_Gamma(x) = St^0_Gamma(x)`.
- *Proof.* If `g x = x` then `c_g(x) = 0`. The cocycle `c_g` is continuous and `Z^2`-valued, so it vanishes on
  a neighbourhood of `x`, and `g` fixes that neighbourhood pointwise. ∎

**Lemma 1.2 (two points give quartic growth).** Let `x_1 ≠ x_2` in `Omega`. In the orbit graph of the
ordered pair `(x_1, x_2)` under `Gamma`, `|B_k((x_1, x_2))| >= c k^4` for all `k >= 1`, with `c > 0`
depending on `x_1, x_2` and `S`.
- *Proof.*
  1. **Separation.** Choose disjoint clopen sets `U_i ∋ x_i`. Minimality and compactness give `r_U` such
     that every ball `B(p, r_U)` meets `Lambda_i = {u : sigma^u x_i ∈ U_i}`. Put `J = 2 r_U + 1`.
  2. **Short local moves inside `U_i`.**
     - For `y ∈ U_i`, and `w` with `|w| <= J` and `sigma^w y ∈ U_i`, pick `w'' ∉ {0, w}` with `|w''| <= 3J` and
       `sigma^{w''} y ∈ U_i`.
     - Pick a clopen `C ∋ y` such that `C`, `sigma^w C` and `sigma^{w''} C` are pairwise disjoint and lie in
       `U_i`. Freeness makes this possible.
     - The 3-cycle `C -> sigma^w C -> sigma^{w''} C -> C` lies in `Gamma`, as a commutator of transpositions
       (ChJN line 209). It is supported in `U_i` and sends `y` to `sigma^w y`.
     - The set of such `y` is compact, and `w` ranges over a finite set. So finitely many of these 3-cycles
       suffice, each of `S`-length `<= L`.
  3. **Paths.** Let `u ∈ Lambda_1`, `|u| <= k`.
     - Walk along lattice points `p_0 = 0, ..., p_m = u` with `m <= 2k`, and choose
       `lambda_j ∈ Lambda_1 ∩ B(p_j, r_U)` with `lambda_0 = 0` and `lambda_m = u`.
     - Consecutive `lambda_j` are within `J`. So a product `a_u` of `<= 2k` moves from step 2 maps `x_1` to
       `sigma^u x_1`, has length `<= 2Lk`, and is supported in `U_1`.
     - Likewise, `b_w` maps `x_2` to `sigma^w x_2` and is supported in `U_2`.
  4. **Counting.**
     - `a_u` fixes `U_2` pointwise and `b_w` fixes `U_1` pointwise. So `a_u b_w (x_1, x_2) = (sigma^u x_1, sigma^w x_2)`,
       and these pairs are distinct for distinct `(u, w)`.
     - Syndeticity gives `|Lambda_i ∩ B(k)| >= (k/J)^2` for large `k`. So `|B_{4Lk}| >= k^4/J^4`. ∎

## 2. Theorem A: small-growth actions are standard

**Theorem A.** Let `Y` be a `Gamma`-set (not necessarily transitive) with `sup_y |B_k(y)| <= f(k)` for all
`k`, where `f(k) = o(k^4)`. Then every `Gamma`-orbit in `Y` is a fixed point, or is isomorphic as a
`Gamma`-set to a standard orbit `Gamma x`. In the second case `St_Gamma(v) = St_Gamma(x)`.

*Proof.* Fix `v ∈ Y` and put `H = St_Gamma(v)`.
1. **`H` is confined.**
   - Suppose it is not. For `P = B_{2k}(Gamma) \ {1}` there is `g` with `P ∩ gHg^{-1} = ∅`, i.e.
     `St(gv) ∩ B_{2k} = {1}`. Then `h -> h g v` is injective on `B_k(Gamma)`, so `|B_k(gv)| = |B_k(Gamma)|`.
   - This holds for every `k`, so `|B_k(Gamma)| <= f(k) = o(k^4)`.
   - By Gromov's theorem `Gamma` would be virtually nilpotent, hence residually finite. But `Gamma` is
     infinite and simple, a contradiction.
   - So some finite `P` meets every `Gamma`-conjugate of `H`. Since `Gamma = A(G)`, `H` is confined by `A(G)`.
2. **Classification.** By the import there is a finite `Q ⊆ Omega` with `St^0_Gamma(Q) ≤ H ≤ St(Q)`.
   - If `Q = ∅`, then `H = Gamma` and `v` is fixed.
3. **`|Q| >= 2` is impossible.**
   - Let `Q ⊇ {x_1, x_2}` and `q = |Q|`. The inclusion `H ≤ St(Q)` gives an equivariant surjection
     `Gamma v -> Gamma Q` of orbit graphs, which maps balls onto balls.
   - The orbit of an ordered `q`-tuple listing `Q` maps onto `Gamma Q` with fibres of size `<= q!`, and it
     projects onto the orbit of `(x_1, x_2)`.
   - So `|B_k(v)| >= |B_k((x_1, x_2))| / q! >= c k^4 / q!` by Lemma 1.2. That contradicts `f(k) = o(k^4)`.
4. **`Q = {x}`.** Then `St^0_Gamma(x) ≤ H ≤ St_Gamma(x)`, and Lemma 1.1 gives `H = St_Gamma(x)`. So
   `gv -> gx` is a well-defined isomorphism `Gamma v -> Gamma x`. ∎

## 3. Corollary B: finite models look orbital

**Corollary B.** For all `C` and `r` there is `n_0 = n_0(S, C, r)` with the following property. Let `O` be an
`n`-exact `F(S)`-set with `n >= n_0` and `|B_k(v)| <= C k^2` for all `v` and all `k <= n`. Then every `r`-ball
of `O` is trivial or orbital.

*Proof.*
1. **A bad sequence.** Suppose not. There are `n_i -> ∞`, models `O_i` and vertices `v_i` whose `r`-balls are
   neither trivial nor orbital.
2. **A limit.** `Sub(F(S))` is compact, so after passing to a subsequence `St_{F(S)}(v_i) -> K`. Put `Y = F(S)/K`
   with root `v = K`.
   - Every ball of `Y` is a ball of some `O_i` with `i` large, because the rooted labelled `m`-ball is
     determined by `K ∩ B_{2m+1}`.
3. **`Y` is a `Gamma`-set.** Let `w` be trivial in `Gamma` with length `l`, and `g ∈ F(S)`.
   - For `n_i >= |g| + l`, the word `g^{-1} w g` fixes `v_i`, by `n_i`-exactness at `v_i`: `g v_i ∈ B_{n_i}(v_i)`.
   - So `K` contains the normal closure of `ker(F(S) -> Gamma)`, and `Gamma` acts on `Y`.
4. **Growth.** `|B_k(y)| <= C k^2` for all `y ∈ Y` and all `k`.
5. **Contradiction.** By Theorem A the orbit `Y` is a fixed point or standard, so `B_r(v)` is trivial or
   orbital. The `r`-ball type is locally constant in `Sub(F(S))`, so `B_r(v_i)` would be too. ∎

## 4. Theorem C: Schreier rigidity for balls that are trivial or orbital

This completes Proposition L5 of `research/artifacts/labbe-lef-2026-09-12.md`, which was only sketched there.

**Chart lemma.** For every `rho` there is `r_1(rho)` such that, if `B_{r_1}(x)` and `B_{r_1}(x')` are
isomorphic (rooted, labelled) for `x, x' ∈ Omega`, then `x|B(rho) = x'|B(rho)`.
- *Proof.*
  1. **Stabilisers separate points.** If `x ≠ x'`, pick `e ∈ {e_1, e_2}` with `x' ∉ {sigma^e x, sigma^{2e} x}`,
     and a clopen `D ∋ x` such that `D`, `sigma^e D`, `sigma^{2e} D` are disjoint and miss `x'`. The 3-cycle on
     them moves `x` and fixes `x'`. So `St(x) ≠ St(x')`.
  2. **What a ball sees.** `B_r(x)` determines `St(x) ∩ B_r`, since a word of length `<= r` fixes `x` iff its
     path returns to the root.
  3. **Compactness.** If the lemma failed, there would be `x_r, x'_r` with isomorphic `r`-balls and different
     `B(rho)`-patterns. Pass to limits `x ≠ x'`, with constant patterns.
     - For each word `w`, the set `{y : w y = y}` is clopen. So `w ∈ St(x) <=> w ∈ St(x_r) <=> w ∈ St(x'_r) <=> w ∈ St(x')`
       for large `r`.
     - Hence `St(x) = St(x')`, which contradicts step 1. ∎

**Moves.**
- Fix `R_2 >= R_1 + 2`, where `R_1` is ChJN's radius (no legal `B(R_1)`-pattern overlaps its translate by
  `0 < |u|_1 <= 3`).
- For legal `pi` on `B(R_2)` and `e ∈ {±e_1, ±e_2}`, let `s(pi, e) ∈ Gamma` be the generator of
  `zd-derived-full-group-fp-forces-finite-type-proof`. On each orbit it is the 3-cycle `w -> w+e -> w-e -> w`
  on the occurrences `w` of `pi`, which are disjoint by that route's Lemma 0. So it sends every `x` with
  `x|B(R_2) = pi` to `sigma^e x`.
- Let `L` bound the `S`-lengths of these finitely many elements.

**Theorem C.** Put `r_* = r_1(R_2) + 2L`. Every finite `F(S)`-set `O` in which all `r_*`-balls are trivial or
orbital carries the trivial action.

*Proof.*
1. **The moving set.** Let `O_mov` be the set of vertices whose `r_*`-ball is not trivial. Its complement is
   the set of common fixed points of `S`, so `O_mov` is invariant.
2. **Charts.** For `v ∈ O_mov`, `B_{r_*}(v) ≅ B_{r_*}(x)` for some `x`. By the chart lemma,
   `chi(v) := x|B(R_2)` depends only on `v`.
3. **Moves on `O_mov`.** Put `T_e(v) = s(chi(v), e) · v`. In `Gamma x` this word leads from `x` to
   `sigma^e x`.
   - The ball `B_{r_*-L}(T_e v)` lies inside `B_{r_*}(v)` and is isomorphic to `B_{r_*-L}(sigma^e x)`. With
     `r_* - L >= r_1(R_2)`, this gives `chi(T_e v) = (sigma^e x)|B(R_2)`.
   - `T_e v` is moved by `s(chi(T_e v), -e)`, so it lies in `O_mov`.
   - `T_{-e} T_e v = v`, since in `Gamma x` the two words lead back to `x`. So each `T_e` is a bijection of
     `O_mov`.
4. **The moves commute.** The words for `T_{e_1} T_{e_2} v` and `T_{e_2} T_{e_1} v` have length `<= 2L`, and
   in `Gamma x` both lead from `x` to `sigma^{e_1+e_2} x`. The ball isomorphism sends both to the same vertex
   of `O`.
   - So `Z^2` acts on the finite set `O_mov` by `T^u = T_{e_1}^{u_1} T_{e_2}^{u_2}`.
5. **A periodic tiling.**
   - Suppose `O_mov ≠ ∅`, pick `v_0` and put `y(u) = chi(T^u v_0)(0)`.
   - `chi(T^{u+e_i} v_0)(0) = chi(T^u v_0)(e_i)`, and `chi(T^u v_0)` is a legal pattern. So every horizontal and
     vertical neighbour pair of `y` matches, and `y ∈ Omega_U`, a nearest-neighbour SFT.
   - `y` is invariant under the stabiliser of `v_0` in `Z^2`, which has finite index. So `y` is periodic,
     contradicting aperiodicity.
   - Hence `O_mov = ∅`. ∎

## 5. Corollary D: the relator-shift crux is false

The notation is that of `zd-subshift-full-group-lef-via-periodic-relator-shifts`: an extension `ĉ` of radius
`R' >= R`, the relator shift `Z_n`, and hypotheses (H1) and (H2).

**Corollary D.** There is `n_0 = n_0(S, R)` such that for every `n >= n_0`, every extension of any radius `R'`
and every periodic `y ∈ Z_n`, all `ŝ` act trivially on the shift orbit `O` of `y`. So (H1) and (H2) never hold
together for `n >= n_0`, and `labbe-relator-shifts-carry-patch-rich-periodic-points` is false.

*Proof.*
1. **`O` is an `F(S)`-set.** The relator `s^{-1} s` has length 2, so `ŝ` permutes `O`, with inverse the extension
   of `s^{-1}`.
2. **`O` is `n`-exact.** A trivial word of length `<= 2n` has `ĉ_w = 0` on `O ⊆ Z_n`, so it fixes every point.
3. **Growth.** Identify `O` with the torus `Z^2 / L` via `u -> sigma^u y`. Each `ŝ` moves a point by a vector of
   norm `<= R`, so `|B_k(z)| <= (2kR + 1)^2 <= 9 R^2 k^2`.
4. **Triviality.** Apply Corollary B with `C = 9R^2` and `r = r_*`, then Theorem C. For `n >= n_0(S, 9R^2, r_*)`
   the action is trivial. Nothing here depends on `R'` or on the extension.
5. **(H1) and (H2) force a moved point.**
   - Take `x ∈ Omega` and `s ∈ S` with `c_s(x) ≠ 0`. By (H1), `x|B(2nR')` occurs at some `z ∈ O`, and then
     `ĉ_s(z) = c_s(x)`.
   - By (H2), `c_s(x) ∉ L`, since `0 < |c_s(x)| <= R <= 2nR`. So `ŝ z ≠ z`, contradicting step 4. ∎

## 6. Scope, and what survives

- **Dead.** Route `labbe-full-group-lef-via-periodic-relator-shifts`, for every generating set and every
  extension, gated or not. `aperiodic-sft-gated-models-break-refinement-relations` is the special case of
  gated extensions of ChJN's generators.
- **Beyond spatial models.** Corollary B and Theorem C concern arbitrary finite `n`-exact `F(S)`-sets, spatial
  or not. So any LEF witness for `Gamma` must use finite groups `G_n`, exact on `B_n(Gamma)`, whose `G_n`-sets
  of quadratic growth up to scale `n` are all trivial. Their regular actions have exponential growth, so this is
  the non-spatial crux (C2), now narrowed. It is **not** a refutation of LEF.
- **Relation to peers.**
  - `zd-derived-full-group-fp-forces-finite-type` works with colourings whose small windows are legal.
  - Theorem C needs no colouring at all: the charts are read off the Schreier balls.
  - The "effective tiling extraction" proposed in ex-fp-simple-relation-climbing's final report is Corollary B
    plus Theorem C, for finite models.
- **Infinite approximants untouched.** Non-isolation in the space of marked groups could still come from
  infinite marked groups. Corollary B then shows only that their small-growth Schreier graphs look orbital
  locally, and Theorem C needs finiteness.
- **Generality (remark, not claimed).**
  - Theorem A uses only minimality and freeness of `Z^2 ~ Omega`. For `Z^d` the same proof gives the bound
    `o(k^{2d})`.
  - Theorem C uses that `Omega` is an aperiodic nearest-neighbour SFT. For a general SFT the colouring would be
    `chi(v)|B(r_X)`.
- **Citation fidelity.**
  - Theorem `t-confined` was read verbatim, together with its proof, from `hom_full_revised19.tex` (arXiv
    e-print 1801.10133), lines 1793–1880.
  - The dichotomy in the proof of Theorem A is modelled on the proof of Matte Bon's Theorem `t-wobbling` (lines
    2461ff), which gets confinement from the absence of Cayley balls in the same way.
