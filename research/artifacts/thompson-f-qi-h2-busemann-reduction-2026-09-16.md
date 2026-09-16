# Thompson's F and spaces quasi-isometric to H^2: a Busemann reduction (2026-09-16)

Supports:
- route `thompson-f-quasimorphisms-vanish-on-f-prime-proof` (Part 1);
- route `thompson-f-no-cobounded-qi-h2-action-via-busemann` (Parts 2 and 3);
- the direct route `busemann-null-isometries-have-no-boundary-contraction-proof` (Part 4). The route file
  carries the complete version, in which the boundary estimates (I1)–(I3) are proved and (I4) is no
  longer needed.
- the proof sketch recorded under '## Attempts' of `two-boundary-fixed-points-block-cobounded-qi-h2-actions`
  (Part 5). That sketch was later superseded by the direct route
  `two-boundary-fixed-points-block-via-busemann-projection`, which needs neither the Morse lemma nor
  boundary topology.

Revision note (same day). (C2)(ii) and (C3) were restated after drafting:
- (C2)(ii) now concludes with Gromov products instead of topological convergence;
- the topological fact "`u_n → u` implies `(u_n|u)_o → ∞`" moved into (C3).
Parts 3 and 4 below reflect the revised statements.

It replaces Markovic's theorem, which the older route `thompson-f-no-cobounded-qi-h2-action-via-markovic`
needs, with three things:
- a swindle showing that the Busemann pseudocharacter vanishes on `F' = [F,F]`;
- Hölder's theorem on free actions on the line;
- elementary coarse geometry.

Conventions. `F` is the group of orientation-preserving piecewise-linear homeomorphisms of `[0,1]` with
finitely many breakpoints, all in `Z[1/2]`, and slopes in `2^Z`. This is `F_(2,1)` of Dudko–Medynets,
Definition 3.1. For a homeomorphism `f`, `supp f` is the closure of `{t : f(t) ≠ t}`. Commutators are
`[a,b] = a b a^{-1} b^{-1}`.

A **homogeneous quasimorphism** (a "pseudocharacter" in arXiv:2406.12982, Definition 1.5) is a map
`β: G → R` such that:
- `D(β) := sup_{g,h} |β(gh) − β(g) − β(h)| < ∞`;
- `β(g^n) = n β(g)` for all `n ∈ Z`.

## Imported facts, with provenance

- **(S) Simplicity and perfection of `F'`.** Dudko–Medynets, *Finite factor representations of
  Higman–Thompson groups*, arXiv:1212.1230v2, p. 10. The PDF was re-fetched and its text extracted on
  2026-09-16. Verbatim, up to extraction spacing: "Observe that the commutator subgroup of F_(n,r) is a
  simple group and the abelianization of F_(n,r) is isomorphic to Z^n [1, Section 4]. Consider the
  subgroup F'_(n,r) of F_(n,r) consisting of all elements f ∈ F_(n,r) with supp(f) being a subset of
  (0,r). Observe that (the commutator subgroup) F'_(n,r) = (F'_(n,r))' [1, Section 4]."
  - Their reference [1] is K. Brown, *Finiteness properties of groups*, J. Pure Appl. Algebra 44 (1987);
    [2] is Cannon–Floyd–Parry. The route `thompson-f-has-no-cobounded-action-on-hyperbolic-plane-proof`
    says [1] is Cannon–Floyd–Parry. That is a harmless misattribution; the quoted sentence itself
    matches.
  - Below, only "`F'` is perfect" is used. It is also derived from simplicity plus non-commutativity in
    Part 1, step 0, so either half of the quote suffices.
- **(NF) `thompson-f-has-no-free-subgroups`** (established by citation in the graph). `F` has no
  non-abelian free subgroup and is not elementary amenable.

## Part 1. Homogeneous quasimorphisms of F vanish on F'

**Step 0: `F'` is perfect and non-abelian.**
- Non-abelian: if `F'` were abelian, `F` would be metabelian, hence elementary amenable, contradicting
  (NF).
- Perfect: `[F',F']` is normal in `F'`, so by (S) it is `1` or `F'`. It is not `1`, since `F'` is
  non-abelian.

**Step 1: `F'` consists of compactly supported elements.**
- Each `f ∈ F` has finitely many breakpoints and fixes `0` and `1`. So there are `ε_f > 0` and
  `a_f, c_f ∈ Z` with `f(t) = 2^{a_f} t` on `[0, ε_f]` and `f(t) = 1 − 2^{c_f}(1 − t)` on `[1 − ε_f, 1]`.
- Composing germs gives `a_{fg} = a_f + a_g` and `c_{fg} = c_f + c_g`. So `f ↦ (a_f, c_f)` is a
  homomorphism `F → Z^2`, and it kills every commutator.
- Hence every `g ∈ F'` has `a_g = c_g = 0`, so `g` is the identity on `[0, ε_g] ∪ [1 − ε_g, 1]`. Thus
  `supp g ⊂ [ε_g, 1 − ε_g]`.

**Step 2: an element pushing everything right.** Define
`h(t) = 2t` on `[0,1/4]`, `h(t) = t + 1/4` on `[1/4,1/2]`, `h(t) = t/2 + 1/2` on `[1/2,1]`.
- The pieces agree at `1/4` (value `1/2`) and at `1/2` (value `3/4`), and `h(1) = 1`.
- The breakpoints are dyadic and the slopes are `2, 1, 1/2`, so `h ∈ F`.
- `h(t) − t` equals `t`, `1/4` and `(1 − t)/2` on the three pieces, so `h(t) > t` on `(0,1)`.
- For `s ∈ (0,1)`, the sequence `h^n(s)` increases and is bounded by `1`. Its limit `L` is a fixed point
  of `h` with `L ≥ s > 0`, so `L = 1`.

**Step 3: facts about homogeneous quasimorphisms.** Let `D = D(β)`.
- (Q1) Conjugation invariance, `β(f g f^{-1}) = β(g)`. We have
  `|β(f g f^{-1}) − β(f) − β(g) − β(f^{-1})| ≤ 2D` and `β(f^{-1}) = −β(f)`, so
  `|β(f g f^{-1}) − β(g)| ≤ 2D`. Applying this to `g^n` gives `n |β(f g f^{-1}) − β(g)| ≤ 2D` for all
  `n`.
- (Q2) If `ab = ba`, then `β(ab) = β(a) + β(b)`. Indeed `(ab)^n = a^n b^n`, so
  `n |β(ab) − β(a) − β(b)| ≤ D` for all `n`.
- (Q3) `|β([a,b])| ≤ D`. By (Q1), `β(a b a^{-1}) + β(b^{-1}) = β(b) − β(b) = 0`, and
  `|β((a b a^{-1}) b^{-1}) − β(a b a^{-1}) − β(b^{-1})| ≤ D`.
- (Q4) `|β(c_1 ⋯ c_m)| ≤ Σ_i |β(c_i)| + (m − 1) D`, by induction on `m`.

**Step 4: the swindle.** Let `β: F → R` be a homogeneous quasimorphism and `g ∈ F'`.
- By Step 0, write `g = Π_{i=1}^m [x_i, y_i]` with `x_i, y_i ∈ F'`. By Step 1 each `x_i, y_i` is
  compactly supported in `(0,1)`.
- Choose `U = [u_0, u_1] ⊂ (0,1)` containing all their supports. Then `Γ := {f ∈ F : supp f ⊆ U}` is a
  subgroup containing all `x_i`, `y_i` and `g`.
- By Step 2, choose `M ≥ 1` with `h^M(u_0) > u_1`, and put `U_k := h^{Mk}(U)` for `k ≥ 0`.
- **The `U_k` are pairwise disjoint.** Let `k < k'`. Since `h^M` is increasing with `h^M(t) > t`, we get
  `h^{M(k'−k)}(u_0) ≥ h^M(u_0) > u_1`. Applying the increasing map `h^{Mk}` gives
  `min U_{k'} > max U_k`.
- Put `τ_k(f) := h^{Mk} f h^{−Mk}`, so `supp τ_k(f) = h^{Mk}(supp f)`. For `f ∈ Γ` this lies in `U_k`.
- **Homeomorphisms with disjoint supports commute.** Suppose `supp f ∩ supp f' = ∅`.
  - If `t` lies in neither support, both maps fix `t`.
  - If `t ∈ supp f`, then `f(t) ∈ supp f`, since `f` preserves `{f ≠ id}` and hence its closure. So `f'`
    fixes both `t` and `f(t)`, and `f f'(t) = f(t) = f' f(t)`.
  - The case `t ∈ supp f'` is symmetric.
- Consequently, for each `n ≥ 1` the map
  `Φ_n: Γ^n → F, (f_0, …, f_{n−1}) ↦ τ_0(f_0) τ_1(f_1) ⋯ τ_{n−1}(f_{n−1})`
  is a homomorphism, because factors with different indices commute.
- In `Γ^n`, the diagonal element `(g, …, g)` equals `Π_i [(x_i, …, x_i), (y_i, …, y_i)]`. Applying
  `Φ_n` gives
  `P_n := τ_0(g) ⋯ τ_{n−1}(g) = Π_{i=1}^m [X_i, Y_i]`, where `X_i := Φ_n(x_i, …, x_i)` and
  `Y_i := Φ_n(y_i, …, y_i)`.
- The factors `τ_k(g)` pairwise commute and each has `β(τ_k(g)) = β(g)` by (Q1). By (Q2) and induction,
  `β(P_n) = n β(g)`.
- By (Q3) and (Q4), `|β(P_n)| ≤ m D + (m − 1) D = (2m − 1) D`.
- So `n |β(g)| ≤ (2m − 1) D` for every `n ≥ 1`, and therefore `β(g) = 0`. ∎

Remarks.
- Consequently every homogeneous quasimorphism of `F` factors through `F/F' ≅ Z^2`. It is then a
  homomorphism, because a homogeneous quasimorphism on an abelian group is additive by (Q2).
- This recovers, for `F`, the agreeability that arXiv:2406.12982v2 attributes to Calegari (Citation 3.7:
  "Every subgroup of F_n is agreeable", citing [Cal07] = D. Calegari, *Stable commutator length in
  subgroups of PL^+(I)*, Pacific J. Math. 232 (2007) 257–262, and [FFL23]). The citation was read in
  arXiv:2406.12982v2 on 2026-09-16; Calegari's paper was not read. The swindle above is self-contained
  and does not rely on it.

## Part 2. Hölder: a free action on the line by increasing homeomorphisms is abelian

**Lemma H.** Let `A` be a group of increasing homeomorphisms of `R` in which every non-identity element
has no fixed point. Then `A` is abelian.

*Proof.*
1. **A bi-invariant order.** For `f ≠ g` in `A`, the map `g^{-1} f` has no fixed point. So `f(y) − g(y)`
   never vanishes, and by the intermediate value theorem it has constant sign. Define `g < f` if
   `f(y) > g(y)` for all `y`.
   - This is a total order.
   - It is invariant under left multiplication, because each `u ∈ A` is increasing.
   - It is invariant under right multiplication, because `f(y) > g(y)` for all `y` implies
     `f(u(y)) > g(u(y))` for all `y`.
   - Positive elements are those with `f(y) > y` everywhere. If `x < y` and `u ≤ v`, then `xu < yv`.
2. **Archimedean.** Let `e < f`. The sequence `f^n(0)` increases. If it were bounded, its limit would be
   a fixed point of `f`. So `f^n(0) → +∞`, and likewise `f^{−n}(0) → −∞`.
   - Hence for every `a ∈ A` there is `m ∈ Z` with `f^m(0) ≤ a(0) < f^{m+1}(0)`.
   - Since comparisons can be tested at `0`, this gives `f^m ≤ a < f^{m+1}`.
3. **Case 1: there is a least positive element `f`.** Given `a`, choose `m` as in step 2. Then
   `e ≤ f^{−m} a < f`, so `f^{−m} a = e`. Thus `A = ⟨f⟩`, which is abelian.
4. **Case 2: there is no least positive element.**
   - First, every `g > e` has some `k > e` with `k^2 ≤ g`. Choose `e < f < g`. If `f^2 ≤ g`, take
     `k = f`. Otherwise `g < f^2`, and `k := f^{−1} g` satisfies `e < k < f`, so
     `k^2 < f k = g`.
   - Now suppose `ab ≠ ba`, say `ba < ab`. Put `g := (ab)(ba)^{−1} > e`, and choose `k > e` with
     `k^2 ≤ g`.
   - By step 2, pick `m, n` with `k^m ≤ a < k^{m+1}` and `k^n ≤ b < k^{n+1}`. Then `ab < k^{m+n+2}`
     and `k^{m+n} ≤ ba`, so `(ba)^{−1} ≤ k^{−(m+n)}`.
   - Therefore `g = (ab)(ba)^{−1} < k^{m+n+2} k^{−(m+n)} = k^2 ≤ g`, a contradiction. ∎

## Part 3. The route argument

Statements used, as in the claim files:

- **(C1)** `thompson-f-quasimorphisms-vanish-on-f-prime`: `F'` is perfect, and every homogeneous
  quasimorphism `F → R` vanishes on `F'`.
- **(C2)** `busemann-null-isometries-have-no-boundary-contraction`. Let `X` be a δ-hyperbolic geodesic
  space, `ξ ∈ ∂X`, `o ∈ X`, and `(z_i)` a sequence converging to `ξ`. For an isometry `k` fixing `ξ`,
  put `q(k) := limsup_i (d(o,z_i) − d(ko,z_i))` and `p(k) := lim_n q(k^n)/n`, as in arXiv:2406.12982,
  Definition 1.10.
  - (i) For every group `G` of isometries fixing `ξ`, the limit exists and `p: G → R` is a homogeneous
    quasimorphism.
  - (ii) If `k` fixes `ξ` and some `a ∈ ∂X \ {ξ}`, and `p(k) = 0`, then no `x ∈ ∂X \ {ξ, a}` satisfies
    `(k^n x | a)_o → ∞` as `n → +∞`.
- **(C3)** `cobounded-qi-h2-actions-without-free-groups-are-focal`. Let `X` be a geodesic space
  quasi-isometric to `H^2`, and let `G` have no non-abelian free subgroup and act isometrically on `X`
  with a coarsely dense orbit. Then:
  - `X` is Gromov hyperbolic, `∂X` is homeomorphic to `S^1`, and isometries act on `∂X` by
    homeomorphisms, giving `∂: G → Homeo(∂X)`;
  - if `u_n → u` in `∂X`, then `(u_n|u)_o → ∞`;
  - `G` fixes some `ξ ∈ ∂X`;
  - some `g ∈ G` is loxodromic, and `Fix(∂g) = {ξ, η}` with `η ≠ ξ`.
- **(C4)** `two-boundary-fixed-points-block-cobounded-qi-h2-actions`. If `G` acts isometrically on a
  geodesic space `X` quasi-isometric to `H^2`, and `∂G` fixes two distinct points of `∂X`, then no orbit
  is coarsely dense.

**Argument.** Suppose `F` acts isometrically on such an `X` with a coarsely dense orbit.

1. **Focal structure.** By (NF) and (C3), `∂X ≅ S^1`, `F` fixes `ξ`, and some loxodromic `g` has
   `Fix(∂g) = {ξ, η}` with `η ≠ ξ`.
2. **The Busemann pseudocharacter vanishes on `F'`.** Let `p: F → R` be the Busemann pseudocharacter at
   `ξ`, with fixed choices `o` and `(z_i)`. By (C2)(i) it is a homogeneous quasimorphism, so by (C1),
   `p(k) = 0` for all `k ∈ F'`. Its restriction to `⟨k⟩` is the pseudocharacter of `⟨k⟩` with the same
   choices, so (C2)(ii) applies to each `k ∈ F'`.
3. **Orientation.** Fix a homeomorphism `ι: ∂X \ {ξ} → R`, and write `R_ξ := ∂X \ {ξ}`. Every `∂k` with
   `k ∈ F` preserves `R_ξ`, so it induces a homeomorphism `k_ι` of `R`, which is increasing or
   decreasing. Recording which gives a homomorphism `F' → Z/2`. It is trivial because `F'` is perfect
   (C1). So `k_ι` is increasing for every `k ∈ F'`.
4. **Elements of `F'` with a fixed point in `R_ξ` act trivially on `∂X`.** Let `k ∈ F'` with
   `Fix := Fix(k_ι) ≠ ∅`, and suppose `k_ι ≠ id`.
   - Take a component `J = (s, s')` of `R \ Fix`, with `−∞ ≤ s < s' ≤ +∞`. Since `Fix ≠ ∅`, at least
     one endpoint is finite. Say `s` is finite; the other case is symmetric. So `s ∈ Fix`.
   - `k_ι` is an increasing homeomorphism with `k_ι(Fix) = Fix`, so it permutes the components of
     `R \ Fix`. Also `k_ι(J) = (s, k_ι(s'))`, with `k_ι(±∞) := ±∞`. The only component with left
     endpoint `s` is `J`, so `k_ι(J) = J`.
   - On `J`, `k_ι(t) − t` never vanishes, so it has constant sign. If it is negative, then for
     `x ∈ J` the sequence `k_ι^n(x)` decreases and is bounded below by `s`. Its limit is a fixed point
     in `[s, x)`, hence equals `s`. If it is positive, the same holds for `k^{−1}`.
   - So for `k' ∈ {k, k^{−1}} ⊂ F'` we have `k'^n x → s` in `R`. Transporting by `ι^{−1}`,
     `∂k'^n(x̂) → â` in `R_ξ`, and hence in `∂X`, where `â := ι^{−1}(s)` and `x̂ := ι^{−1}(x)`. Here
     `x̂ ∉ {ξ, â}` and `∂k'` fixes `ξ` and `â`.
   - By (C3), `(∂k'^n x̂ | â)_o → ∞`. This contradicts (C2)(ii), since `p(k') = 0` by step 2. Hence
     `k_ι = id`, so `∂k` is the identity on `R_ξ` and also fixes `ξ`: `∂k = id`.
5. **`∂(F')` is trivial.** The group `A := {k_ι : k ∈ F'}` consists of increasing homeomorphisms of `R`
   (step 3), and its non-identity elements have no fixed points (step 4). By Lemma H, `A` is abelian.
   Since `∂k` fixes `ξ`, the map `∂k ↦ k_ι` is an isomorphism `∂(F') → A`. So `∂(F')` is an abelian
   quotient of the perfect group `F'`, hence trivial.
6. **A second global fixed point.** By step 5, `∂` factors through `F/F'`, so `∂(F)` is abelian. For
   `h ∈ F`, `∂h` commutes with `∂g`, so it maps `Fix(∂g) = {ξ, η}` onto itself. It fixes `ξ` (step 1),
   so it fixes `η`. Thus `∂(F)` fixes `ξ ≠ η`, and (C4) contradicts the coarsely dense orbit. ∎

Sanity check against a known example. `BS(1,2) = Z[1/2] ⋊ Z` acts coboundedly on `H^2` (see
`abelian-isometry-groups-of-h2-are-not-cobounded-proof`). It is amenable, so it has no free subgroup
and every pseudocharacter is a homomorphism. The argument fails exactly at perfection: its commutator
subgroup `Z[1/2]` is abelian, not perfect, and it does act freely by translations on `∂H^2 \ {∞}`. The
same proof shows more generally: if a group `G` has no non-abelian free subgroup, `[G,G]` is perfect,
and every homogeneous quasimorphism of `G` vanishes on `[G,G]`, then `G` has no cobounded isometric
action on a space quasi-isometric to `H^2`. That generalisation is recorded here, not as a node.

## Part 4. Proof of (C2), modulo basic facts about the Gromov boundary

Conventions.
- `(x|y)_w = (d(x,w) + d(y,w) − d(x,y))/2`.
- δ-hyperbolic means `(x|z)_w ≥ min{(x|y)_w, (y|z)_w} − δ` for all points.
- A sequence `(y_i)` converges at infinity if `(y_i|y_j)_o → ∞`. Two such sequences are equivalent if
  `(y_i|w_j)_o → ∞`, and `∂X` is the set of equivalence classes.
- For `u, v ∈ X ∪ ∂X`, `(u|v)_o := sup liminf_{i,j} (y_i|w_j)_o` over sequences representing `u, v`
  (constant sequences for points of `X`).

Basic boundary facts. In the first draft these were imported from Bridson–Haefliger III.H §3, not
re-read. They are now proved from the four-point inequality in the route file
`busemann-null-isometries-have-no-boundary-contraction-proof`, Step 1, as (B1)–(B3). That version has
`3δ` in (I3).
- (I1) For any sequences `y_i → u` and `w_j → v`: `liminf_{i,j} (y_i|w_j)_o ≥ (u|v)_o − 2δ`.
- (I2) `(u|v)_o < ∞` for distinct `u, v ∈ ∂X`.
- (I3) `(u|v)_o ≥ min{(u|t)_o, (t|v)_o} − 3δ` for `u, v, t ∈ ∂X`.
- (I4) If `u_n → u` in `∂X`, then `(u_n|u)_o → ∞`. This is no longer used in Part 4; it is part of
  (C3).

Isometries map sequences converging at infinity to such sequences and preserve equivalence.

(a) **Spread of limit points.** Let `z_i, z'_j → ξ` and `y ∈ X`. Then
`limsup_i (y|z_i)_o ≤ liminf_j (y|z'_j)_o + δ`.
- Choose `i_l, j_l → ∞` realising the limsup and the liminf.
- Then `(y|z'_{j_l})_o ≥ min{(y|z_{i_l})_o, (z_{i_l}|z'_{j_l})_o} − δ`, and the second entry tends to
  `∞`.
- Put `λ_y := liminf_i (y|z_i)_o ∈ [0, d(y,o)]`. All limit points of `(y|z'_j)_o`, for any `z'_j → ξ`,
  lie in `[λ_y − δ, λ_y + δ]`.

(b) **Busemann cocycle.**
- Put `b(y) := limsup_i (d(y,z_i) − d(o,z_i))`. Since `d(y,z) − d(o,z) = d(y,o) − 2(y|z)_o`, we get
  `b(y) = d(y,o) − 2λ_y` and `b(o) = 0`.
- Let `k` fix `ξ` and put `z'_i := k^{−1} z_i → ξ`. Then
  `b(ky) = limsup_i (d(y,z'_i) − d(k^{−1}o, z'_i)) = limsup_i [d(y,o) − 2(y|z'_i)_o − d(k^{−1}o,o) + 2(k^{−1}o|z'_i)_o]`.
- By (a) this lies within `4δ` of `b(y) − b(k^{−1}o)`. With `c(k) := −b(k^{−1}o)`:
  `(**) |b(ky) − b(y) − c(k)| ≤ 4δ` for all `y`.

(c) **(C2)(i).**
- Writing `b(klo) − b(o) = [b(k(lo)) − b(lo)] + [b(lo) − b(o)]` and using (**) three times gives
  `|c(kl) − c(k) − c(l)| ≤ 12δ`.
- For a quasimorphism `φ` of defect `D`:
  - `φ(g^{m+n}) ≤ φ(g^m) + φ(g^n) + D`, and `|φ(g^n) − nφ(g)| ≤ (n − 1)D`;
  - so by Fekete's lemma `φ̄(g) := lim φ(g^n)/n` exists and satisfies `|φ̄ − φ| ≤ D`;
  - hence `φ̄` has defect at most `4D`;
  - `φ̄(g^n) = nφ̄(g)` for `n ≥ 0`, and `φ̄(g^{−1}) = −φ̄(g)` because
    `|φ(g^m) + φ(g^{−m}) − φ(e)| ≤ D`.
- Next compare with `q`. We have `q(k) = −d(ko,o) + 2 limsup_i (ko|z_i)_o`, so by (a)
  `|q(k) + b(ko)| ≤ 2δ`. By (**) at `y = o`, `|b(ko) − c(k)| ≤ 4δ`. So `|q + c| ≤ 6δ`.
- Hence `q` is a quasimorphism and `p = q̄ = −c̄` is a homogeneous quasimorphism.

(d) **Bounded horofunction shift.** If `p(k) = 0`, then `c̄(k^n) = 0` for all `n ∈ Z`, so
`|c(k^n)| ≤ 12δ`. By (**), `|b(k^n y) − b(y)| ≤ 16δ` for all `n ∈ Z` and `y ∈ X`.

(e) **Horospherical product.** Put `P(y,w) := (b(y) + b(w) − d(y,w))/2 = (y|w)_o − λ_y − λ_w`. By (d),
`|P(k^n y, k^n w) − P(y,w)| ≤ 16δ`.

(f) **Claim A.** If `y_i → u ∈ ∂X \ {ξ}`, then `limsup_i λ_{y_i} ≤ (u|ξ)_o + δ`.
- Let `T := limsup_i λ_{y_i}`, and fix `R > 0` and `ε > 0`.
- Choose `N` with `(y_i|y_{i'})_o ≥ R` for all `i, i' ≥ N`. Then choose `i ≥ N` with
  `λ_{y_i} ≥ min{T, R} − ε`.
- For `i' ≥ N` and all large `m`,
  `(y_{i'}|z_m)_o ≥ min{R, (y_i|z_m)_o} − δ ≥ min{R, λ_{y_i} − ε} − δ`.
- So `(u|ξ)_o ≥ liminf_{i',m} (y_{i'}|z_m)_o ≥ min{R, T − 2ε} − δ`. Let `R → ∞` and `ε → 0`, and use
  (I2).

(g) **(C2)(ii).** Suppose `k` fixes `ξ` and `a ≠ ξ`, `p(k) = 0`, `x ∈ ∂X \ {ξ, a}`, and
`(x_n|a)_o → ∞`, where `x_n := k^n x`.
1. Pick `y_i → x` and `w_j → a` in `X`. Since `liminf_{i,j} (y_i|w_j)_o ≤ (x|a)_o < ∞` (I2), we can pass
   to index pairs `(i_l, j_l) → ∞`. Relabelling, we may assume `(y_i|w_i)_o ≤ Q := (x|a)_o + 1` for all
   `i`. Hence `P(y_i, w_i) ≤ Q`, since `λ ≥ 0`.
2. By (e), `P(k^n y_i, k^n w_i) ≤ Q + 16δ` for all `n, i`.
3. Fix `n`. Then `k^n y_i → x_n` and `k^n w_i → a`, with `x_n ≠ ξ` and `x_n ≠ a`, because `k^n` is a
   bijection of `∂X` fixing `ξ` and `a`.
4. Bound the three terms of `P(k^n y_i, k^n w_i) = (k^n y_i|k^n w_i)_o − λ_{k^n y_i} − λ_{k^n w_i}`:
   - by (I1), `liminf_i (k^n y_i|k^n w_i)_o ≥ (x_n|a)_o − 2δ`;
   - by Claim A, `limsup_i λ_{k^n y_i} ≤ (x_n|ξ)_o + δ` and `limsup_i λ_{k^n w_i} ≤ (a|ξ)_o + δ`.
5. Combining steps 2 and 4: `(x_n|a)_o − (x_n|ξ)_o ≤ Q + (a|ξ)_o + 20δ` for every `n ≥ 0`.
6. By hypothesis, `(x_n|a)_o → ∞`. By (I3), `(a|ξ)_o ≥ min{(a|x_n)_o, (x_n|ξ)_o} − 3δ`, so for large
   `n`, `(x_n|ξ)_o ≤ (a|ξ)_o + 3δ`.
7. So the left side of step 5 tends to `∞`, a contradiction. ∎

Alternative, with heavier imports. By arXiv:2406.12982 Citation 1.12 ([Man08, §4.1]), `p(k) = 0` means
`k` is not loxodromic. The same source states that a parabolic element has exactly one fixed point in
`∂X`, so `k` would be elliptic, with bounded orbits. Then `(x_n|a)_o = (x|a)_{k^{−n}o}` stays bounded.
This route needs Manning's theorem and the fixed-point count, which were not read, so the proof above
is preferred.

## Part 5. Proof sketch of (C4)

- Let `φ: X → H^2` be a quasi-isometry with quasi-inverse `ψ`, and let `ξ ≠ η` be fixed by `∂G`.
- The boundary extension `∂φ` is a homeomorphism `∂X → S^1` (classical; Bridson–Haefliger III.H.3.9,
  not re-read). Let `γ` be the geodesic of `H^2` from `∂φ(η)` to `∂φ(ξ)`, and put `ℓ := ψ ∘ γ`, a
  quasi-geodesic in `X` converging to `η` and `ξ` at its ends.
- For `h ∈ G`, `φ ∘ h ∘ ℓ` is a quasi-geodesic of `H^2` with constants independent of `h`. Its ends
  converge to `∂φ(h η) = ∂φ(η)` and `∂φ(ξ)`.
- By the Morse lemma for bi-infinite quasi-geodesics in `H^2` with common endpoints (Bridson–Haefliger
  III.H.1.7 plus a limiting argument; not re-read), it lies within `M` of `γ`, with `M` independent of
  `h`. So `φ(G·ℓ(0)) ⊆ N_M(γ)`.
- If `G·ℓ(0)` were `r`-dense in `X`, then `φ(X)` would lie in a bounded neighbourhood of `γ`. Since
  `φ(X)` is coarsely dense in `H^2`, `H^2` itself would lie within bounded distance of the geodesic `γ`.
  That is false: the points at distance `t` from `γ` along a perpendicular exist for every `t`.
