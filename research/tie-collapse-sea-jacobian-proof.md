---
rg: 2
id: tie-collapse-sea-jacobian-proof
kind: route
title: Push the uniform sea measure through the lift, compute the cylinder Jacobian, and fill charge levels by a flux identity and a chromatic cluster expansion
target: collapse-lifts-with-tied-largest-fibers-are-surjective
requires:
  - bijective-ca-preserve-uniform-bernoulli-measure
  - surjunctivity-passes-to-subgroups
---

Complete proof. Notation as in the target. Automata act by `(σx)(g) = f(x|_{gM})` for a finite memory
`M ∋ 1`. We enlarge `M` so that one memory serves `τ`, `Φ` and every inverse used below. `ν_Z` is the uniform
Bernoulli measure on `Z^G`.

## Step 0. Constants and the three failing sizes

`Φ` is injective and permutes the finitely many constant configurations of `B^G`. So some power `Φ^m` fixes
all of them. Then `τ^m` fixes every constant of `A^G`, because `r` maps constants onto constants. The power is
injective, and it is surjective exactly when `Φ` is. From now on write `Φ, τ` for `Φ^m, τ^m`.

Fix `b ∈ Z`. `Φ` maps `Q_b^G` into `r^{-1}(τ(b^G)) = r^{-1}(b^G) = Q_b^G`. So the rest map `T_b = Φ|_{Q_b^G}`
is an injective automaton on `q` letters. If it is not surjective, `q ∈ NS(G)`. Otherwise `T_b` is bijective.

## Step 1. The sea Jacobian lemma

Let `Y ⊇ Z` be finite alphabets and `σ` an automaton on `Y^G`. Assume `σ` is injective on `L_Y` (the
configurations with finitely many sites outside `Z`) and that `σ(Z^G) = Z^G` bijectively. Then `σ` maps `L_Y`
into `L_Y`. Fix weights `λ_a > 0` for `a ∈ Y \ Z`. For a finite `E ⊂ G` and `p ∈ (Y \ Z)^E`, let `L_{E,p}` be the
configurations whose particle set is exactly `E` and which carry `p` there. Identify `L_{E,p}` with `Z^{G \ E}`
and put

    M_λ(A) = Σ_{E,p} (Π_{g ∈ E} λ_{p(g)}) · ν_{G∖E}(A ∩ L_{E,p}).

This is a G-invariant σ-finite Borel measure on `L_Y`. Each sea site carries the uniform probability on `Z`,
so every sea letter has weight `1/|Z|`.

*Cylinders.* Take `E, p`, a finite `K ⊇ E M^{-1} M` and `w ∈ Z^{K \ E}`. Put
`S = {x ∈ L_{E,p} : x|_{K∖E} = w}`, so `M_λ(S) = Π_E λ · |Z|^{k - |K|}` with `k = |E|`. Let `N = E M^{-1}`, so
that `N M ⊆ K`. For `g ∉ N` the window `gM` misses `E`. Fix `s ∈ Z^E`, and for `x ∈ S` let `z_x` be `x` with
`p` replaced by `s`. Then:
- `x ↦ z_x` is a bijection from `S` onto `C = {z ∈ Z^G : z|_E = s, z|_{K∖E} = w}`.
- `σx = σz_x` off `N`.
- `σx|_N = π` and `σz|_N = π'` are fixed patterns, since both are read from inside `K`.

Hence `σS = {y : y|_N = π, y|_{G∖N} ∈ P}` and `σC = {y : y|_N = π', y|_{G∖N} ∈ P}`, with
`P = {σz|_{G∖N} : z ∈ C}`. Since `σ|_{Z^G}` is a homeomorphism, `P` is clopen. It preserves `ν_Z` by
`bijective-ca-preserve-uniform-bernoulli-measure`. So

    |Z|^{-|N|} ν_{G∖N}(P) = ν_Z(σC) = ν_Z(C) = |Z|^{-|K|}.

Every particle of `σx` lies in `N`. Let `E'` be the particle set of `π`, with `k' = |E'|`. Then

    M_λ(σS) = Π_{E'} λ · |Z|^{k' - |N|} · ν_{G∖N}(P) = Π_{E'} λ · |Z|^{k' - |K|},

which gives the ratio stated in the target:

    M_λ(σS) / M_λ(S) = |Z|^{k'-k} · Π_{E'} λ / Π_E λ.                       (J)

*Invariance.* For `λ ≡ 1/|Z|` the ratio is `1`. The cylinders, over all admissible `K`, together with `∅`, form
a π-system of sets of finite measure that generates the Borel sets and covers `L_Y` by countably many pieces.
`σ` is injective and Borel on `L_Y`, so by Lusin–Souslin it maps Borel sets to Borel sets, and `A ↦ M_λ(σA)`
is a measure. It agrees with `M_λ` on the π-system, so `M_λ(σA) = M_λ(A)` for every Borel `A ⊆ L_Y`.

## Step 2. Pushing through the collapse gives a charge inequality

*Transfer principle.* Let `Z_A ⊆ A` be a sea for `τ` and `Z_B = r^{-1}(Z_A)` a sea for `Φ`. Assume every fiber over
`Z_A` has the same size `t`, that `τ` and `Φ` are bijective on the two sea shifts, and that both are injective.
- Upstairs, give every letter of `B` weight `1/|Z_B|`. By Step 1 with ratio `1`, `Φ` preserves the resulting
  measure `μ_B` on `L_B`.
- Downstairs, `r` maps `L_B` onto `L_A` and `r_* μ_B = M_λ`, with `λ_a = |Q_a| / |Z_B|` for particles `a`. A sea
  site pushes the uniform law on `Z_B` to the uniform law on `Z_A`, because the fibers over `Z_A` are equal, and
  a particle `a` collects the weight of its `|Q_a|` preimages.

For a cylinder `S` around `x ∈ L_A` we have `Φ(r^{-1}S) ⊆ r^{-1}(τS)`, since `r ∘ Φ = τ ∘ r`. Hence

    M_λ(τS) = μ_B(r^{-1}τS) >= μ_B(Φ r^{-1}S) = μ_B(r^{-1}S) = M_λ(S).            (T)

Combine (T) with (J). With `|Z_B| = t|Z_A|` we get `|Z_A| λ_a = |Q_a|/t`, so (J) reads

    Π_{particles of τx} (|Q_a|/t) >= Π_{particles of x} (|Q_a|/t).                  (C)

*Sea `{b}`: the tied letters are invariant.* Take `Z_A = {b}` and `Z_B = Q_b`, so `t = q`. The shift `{b}^G` is
a point, and `Φ` is bijective on `Q_b^G` by Step 0. The other letters of `Z` are particles of factor `1`, and
every other factor is `< 1`. Let `u` have a `b`-sea and finitely many sites carrying other letters of `Z`. Then
(C) gives `Π_{τu} >= 1`, so every particle of `τu` lies in `Z`. Such `u` are dense in `Z^G`, `τ` is continuous
and `Z^G` is closed, so `τ(Z^G) ⊆ Z^G`.
- `τ|_{Z^G}` is an injective automaton on `|Z|` letters. If it is not onto, `|Z| ∈ NS(G)` (when `|Z| >= 2`;
  when `|Z| = 1` it is trivially onto).
- Otherwise `Φ` maps `B_Z^G` injectively into `r^{-1}(Z^G) = B_Z^G`, a full shift on `q|Z|` letters. If that is
  not onto, `q|Z| ∈ NS(G)`.

This proves item 1 of the target, or one of the three alternatives.

*Sea `Z`: the charge never increases.* Now take `Z_A = Z` and `Z_B = B_Z`, so `t = q` again. For a particle,
`|Q_a|/q = e^{-w(a)}`, so (C) reads `e^{-W(τx)} >= e^{-W(x)}`, that is `W(τx) <= W(x)`. This is item 2.

## Step 3. Equality fills the fiber, and the surjectivity criterion

*Item 5.* Suppose `W(τx) = W(x)`, and take `S` a cylinder around `x` as in Step 1 (sea `Z`). Then (T) is an
equality, so `μ_B(r^{-1}τS ∖ Φ r^{-1}S) = 0`. We show the difference is empty.
- `r^{-1}S` is compact: finitely many choices on `E` and on `K ∖ E`, and `B_Z` elsewhere. So `Φ(r^{-1}S)` is
  compact, hence closed.
- By Step 1, `r^{-1}τS = {y : r(y)|_N = π, r(y)|_{G∖N} ∈ P}` with `P` clopen. This is a clopen part of a
  product set, on which `μ_B` is a product measure with positive weights.
- So every nonempty relatively open subset of `r^{-1}τS` has positive measure. Hence `Φ(r^{-1}S) = r^{-1}τS`.

Now let `y ∈ F_{τx} ⊆ r^{-1}τS`. Write `y = Φ(y')` with `y' ∈ r^{-1}S`. Then `τ(r(y')) = r(y) = τx`, so
`r(y') = x` by injectivity of `τ`, that is `y' ∈ F_x`. Thus `Φ(F_x) = F_{τx}`; the inclusion `⊆` holds always.

*Item 3, forward.* Suppose `τ(L) = L` and `W ∘ τ = W` on `L`. By item 5,
`Φ(B^G) ⊇ ∪_{x ∈ L} F_{τx} = r^{-1}(τL) = r^{-1}(L)`. This set is dense in `B^G`, because it contains every
configuration with finitely many sites outside `B_Z`. `Φ(B^G)` is compact, so `Φ` is onto.

*Item 3, backward.* Suppose `Φ` is onto. Then it is bijective, and its inverse is an automaton. `τ` is onto
because `r` is, so `τ^{-1}` is an automaton too, and `r ∘ Φ^{-1} = τ^{-1} ∘ r`.
- `τ^{-1}` fixes `Z^G` setwise, so it maps `L` into `L`. Hence `τ(L) = L`.
- The pair `(Φ^{-1}, τ^{-1})` satisfies every hypothesis used in Steps 1 and 2 with sea `Z`: injective, and
  bijective on `B_Z^G` and `Z^G`. So `W(τ^{-1}y) <= W(y)`, and together with item 2, `W ∘ τ = W` on `L`.

## Step 4. Levels below `2 w_min` are filled

Charges take values in the locally finite set of nonnegative combinations of the `w(a)`. The level `L_0 = Z^G`
is filled by item 1. Let `0 < c < 2 w_min`, and suppose `τ(L_{c'}) = L_{c'}` for every level `c' < c`.

*Conservation.* Take `x ∈ L_c`. If `W(τx) = c' < c`, then `τx = τx'` for some `x' ∈ L_{c'}`. Since
`x' != x`, this contradicts injectivity. So by item 2, `τ(L_c) ⊆ L_c`. Every `x ∈ L_c` has exactly one
particle, since two particles already give charge `>= 2 w_min`.

*Rooting.* Let `R_c = {x ∈ L_c : the particle sits at 1_G}`. It is the finite union, over the particles `a`
with `w(a) = c`, of the compact sets `{a} × Z^{G∖{1}}`. Let `M = M_λ` with `λ ≡ 1/|Z|`, so that
`M(R_c) = #{a : w(a) = c} / |Z| < ∞`, and `M|_{R_c}` has full support.
- For `x ∈ R_c`, `τx` agrees with a sea image off `M^{-1}`, so its particle sits at some `h(x) ∈ M^{-1}`.
- `h(x)` is read from `x|_{M^{-1}M}`, so `h` is locally constant.
- Define `τ'(x)` as the translate of `τx` that puts its particle at `1_G`. Then `τ'` is continuous on `R_c`
  and maps `R_c` into `R_c`.
- `τ'` is injective. If `τ'x = τ'y`, then `τx` is a translate of `τy`, say by `g`. By equivariance and
  injectivity of `τ`, `x` is the same translate of `y`. Both have their particle at `1_G` and one particle
  each, so `g` is trivial and `x = y`.

*Measure.* On each clopen piece `{h(x) = h}`, `τ'` is a translate of `τ`. `M` is G-invariant, and it is
`τ`-invariant by Step 1. The images of the pieces are disjoint by injectivity, so `M(τ' R_c) = M(R_c)`.
`τ'R_c` is compact, so `R_c ∖ τ'R_c` is open in `R_c` and has measure `0`. By full support it is empty.

*Conclusion.* Every `x ∈ R_c` is a translate of some `τx'`, hence lies in `τ(L_c)`. By translation, so does
every `x ∈ L_c`. There are finitely many levels below `2 w_min`, so induction proves the first sentence of
item 4. The second follows from conservation and item 5.

## Step 5. All levels: set-up, and where preimages live

Steps 5 to 7 remove the restriction `c < 2 w_min`.

*Countable reduction.* Let `H` be the subgroup generated by the memory `M`, which serves `Φ`, `τ` and the
inverse `ι` of `τ|_{Z^G}` used below. `H` is countable. Each of these automata acts coset by coset on
`gH`, as a copy of the automaton with the same rule over `H` (see `surjunctivity-passes-to-subgroups`).
So injectivity and surjectivity of each one hold over `G` iff they hold over `H`. By the same coset argument,
an injective non-onto automaton over `H` on `n` letters induces one over `G`, so `NS(H) ⊆ NS(G)`. Every
alternative in the target therefore transfers from `H` to `G`, and from here on `G` is countable.

*Standing hypotheses.* By Steps 0 to 3, unless one of `q`, `|Z|`, `q|Z|` lies in `NS(G)`:
- `τ` is injective;
- `τ|_{Z^G}` is bijective, with inverse automaton `ι`;
- `W ∘ τ <= W` on `L`.

Only these three facts are used until the last line of Step 7. The first is used only on `L`.

*Notation.*
- Put `D_s = (M^{-1}M)^s`. It is symmetric and contains `1`, `D_s D_t ⊆ D_{s+t}`, and `M ∪ MM ⊆ D_2`.
- Call `g, h` `s`-close when `g^{-1}h ∈ D_s`. This relation is invariant under left translation.
- `s`-components, `s`-connected and `s`-split (not `s`-connected) refer to the graph of `s`-closeness on a
  finite set.
- If `Γ` is `s`-connected with at most `k` points, then `Γ ⊆ γ D_{(k-1)s}` for every `γ ∈ Γ`.
- `P(x)` is the particle set of `x ∈ L`.

*Induction hypothesis.* Fix a charge value `c > 0`. Assume `τ(L_{c'}) = L_{c'}` for every level `c' < c`.
The conservation paragraph of Step 4 applies verbatim and gives `τ(L_c) ⊆ L_c`. So `τ` restricted to each
`L_{c'}` with `c' < c` is a bijection. Put `k = ⌊c / w_min⌋`, a bound for `|P(x)|` on every level `<= c`.

*Three local facts.* The rule of `τ` maps `Z`-patterns into `Z`, since `τ(Z^G) ⊆ Z^G`. Write `j` for the
rule of `ι`. For `y ∈ A^G` and `h` with `y|_{hM}` `Z`-valued, put `ι_loc(y)(h) = j(y|_{hM})`.
- (F1) `P(τx) ⊆ P(x) D_1`. If `gM` misses `P(x)`, then `τx(g) ∈ Z`.
- (F2) If `x` is `Z`-valued on `hMM`, then `τx` is `Z`-valued on `hM` and `ι_loc(τx)(h) = x(h)`. To see this,
  take `z ∈ Z^G` equal to `x` on `hMM`. Then `τz = τx` on `hM`, and `ι(τz) = z`.
- (F3) Let `y` be `Z`-valued on `gMM`, and let `x` agree with `ι_loc(y)` on `gM`. Then `τx(g) = y(g)`. To see
  this, take `z ∈ Z^G` equal to `y` on `gMM`. Then `ι z = ι_loc(y)` on `gM`, and `τ(ι z) = z`.

**Lemma 5.1 (preimages stay near images).** For `x ∈ L` with at most `k` particles,
`P(x) ⊆ P(τx) D_ρ`, where `ρ = 6k`.

*Proof.* Let `Γ` be a `6`-component of `P(x)`. Suppose `Γ D_5` misses `P(τx)`; we derive a contradiction.
Put `U = Γ D_2`. Let `x''` equal `ι_loc(τx)` on `U` and `x` elsewhere. This is defined, because `τx` is
`Z`-valued on `UM ⊆ Γ D_3`. Then `x'' ∈ L`, `x''` is `Z`-valued on `Γ`, and so `x'' != x`.

We check that `x''` agrees with `ι_loc(τx)` on `ΓD_4`. Take `h ∈ Γ D_4 ∖ U`.
- `hMM ⊆ hD_2` misses `Γ`, because `h ∉ ΓD_2`.
- `hMM ⊆ ΓD_6` misses the other particles, which are not `6`-close to `Γ`.
- So `x` is `Z`-valued on `hMM`, and (F2) gives `x(h) = ι_loc(τx)(h)`.

Now fix `g ∈ G`.
- If `gM` misses `U`, then `x'' = x` on `gM` and `τx''(g) = τx(g)`.
- Otherwise `g ∈ U M^{-1} ⊆ Γ D_3`. So `gM ⊆ ΓD_4`, where `x'' = ι_loc(τx)`. Also `τx` is `Z`-valued on
  `gMM ⊆ ΓD_5`. By (F3), `τx''(g) = τx(g)`.

Thus `τx'' = τx` with `x'' != x`, both in `L`, which contradicts injectivity on `L`. So every `6`-component
`Γ` has a point within `D_5` of `P(τx)`. Since `Γ ⊆ γ D_{6(k-1)}` for each `γ ∈ Γ`, every particle of `x` lies
in `P(τx) D_{6k}`. ∎

**Lemma 5.2 (split targets are hit).** Put `S_0 = 2ρ + 12`. Every `y ∈ L_c` whose particle set is `S_0`-split
lies in `τ(L_c)`.

*Proof.* Split `P(y) = P_1 ⊔ P_2` into nonempty parts, with no point of `P_2` `S_0`-close to `P_1`.
- For `i = 1, 2`, let `y_i` be `y` with the sites of `P_{3-i}` overwritten by a fixed `z_0 ∈ Z`.
- Then `W(y_i) < c`, so `y_i = τ x_i` for some `x_i ∈ L` of the same charge.
- By Lemma 5.1, `P(x_i) ⊆ P_i D_ρ`.
- Put `U_i = P_i D_{ρ+2}`. These are disjoint.

Define `x = x_i` on `U_i` and `x = ι_loc(y)` elsewhere. For `h ∉ U_1 ∪ U_2`, `hM` misses `P(y)`, so `x` is
defined.

*Claim: `x = x_i` on `P_i D_{ρ+6}`.* Take `h` in this set but outside `U_i`.
- `hMM ⊆ hD_2` misses `P_i D_ρ ⊇ P(x_i)`, so (F2) gives `x_i(h) = ι_loc(y_i)(h)`.
- `y_i = y` on `hM ⊆ P_i D_{ρ+7}`, because `P_{3-i}` lies outside `P_i D_{S_0}`.
- Also `h ∉ U_{3-i}`, so `x(h) = ι_loc(y)(h) = x_i(h)`.

*Checking `τx = y` at a site `g`.*
- If `g ∈ P_i D_{ρ+5}`, then `gM ⊆ P_i D_{ρ+6}`. So `τx(g) = τx_i(g) = y_i(g) = y(g)`, the last because
  `g ∉ P_{3-i}`.
- If `g` lies in neither set, then `gM` misses `U_1 ∪ U_2`. So `x = ι_loc(y)` on `gM`. Also `y` is `Z`-valued
  on `gMM ⊆ gD_2`, since `g ∉ P_i D_2`. (F3) gives `τx(g) = y(g)`.

`x ∈ L`, with particle set exactly `P(x_1) ⊔ P(x_2)`, since `x` is `Z`-valued off `U_1 ∪ U_2`. So
`W(x) = W(y_1) + W(y_2) = c`, and `τx = y`. ∎

Hence the missing set `D_c = L_c ∖ τ(L_c)` consists of configurations whose particle set is `S_0`-connected.

**Lemma 5.3 (images of atoms are local).** Let `x ∈ L` and let `Γ ⊆ P(x)` be such that no other particle is
`4`-close to `Γ`. Then `P(τx) ∩ ΓD_1` is determined by the pattern `x|_{ΓD_2}`. Moreover
`P(τx) = ⊔_Γ (P(τx) ∩ ΓD_1)` over the `4`-components of `P(x)`, or over any coarser such partition.

*Proof.* For `g ∈ ΓD_1`, `τx(g)` is read from `x|_{gM}`, and `gM ⊆ ΓD_2`. The decomposition follows from (F1),
since the sets `ΓD_1` are disjoint. ∎

## Step 6. A flux identity for the missing set

Let `M = M_λ` with `λ ≡ 1/|Z|`, so every letter has weight `1/|Z|`. A cylinder fixing `x` on a finite `K ⊇ P(x)`
has mass `|Z|^{-|K|}`. By Step 1, `M(τA) = M(A)` for Borel `A ⊆ L_c`. For `G`-invariant Borel `A ⊆ L_c`, put

    M̄(A) = ∫_A 1[1 ∈ P(x)] / |P(x)| dM(x).

**Lemma 6.1 (transport).** For `G`-invariant Borel `A ⊆ L_c`, `M̄(τ^{-1}A) = M̄(A ∩ τL_c)`.

*Proof.* Use the convention `(gx)(h) = x(g^{-1}h)`, so `P(gx) = gP(x)`. Put

    m(x, g, h) = 1_A(τx) 1[g ∈ P(x)] 1[h ∈ P(τx)] / (|P(x)| |P(τx)|).

Level `c > 0` and conservation make both sets nonempty. Equivariance gives `m(fx, fg, fh) = m(x, g, h)`.
`M` is `G`-invariant, so

    ∫ m(x, 1, h) dM = ∫ m(h^{-1}x, h^{-1}, 1) dM = ∫ m(x, h^{-1}, 1) dM.

Summing over the countable group (Tonelli) gives the mass transport principle
`∫ Σ_h m(x,1,h) dM = ∫ Σ_g m(x,g,1) dM`.
- The left side is `M̄(τ^{-1}A)`.
- The right side is `∫ φ(τx) dM(x)` with `φ(y) = 1_A(y) 1[1 ∈ P(y)] / |P(y)|`.
- `τ` is an injective measure-preserving map of `L_c` into itself, so this equals `∫_{τL_c} φ dM = M̄(A ∩ τL_c)`. ∎

Put `S_1 = 2k S_0 + 2` and `C = {x ∈ L_c : P(x) is S_1-connected}`.
- `M̄(C) < ∞`. A rooted `x ∈ C` has `P(x) ⊆ D_{(k-1)S_1}`, so there are finitely many choices of
  `(P(x), x|_{P(x)})`, each of mass at most `1`.
- `D_c ⊆ C`, because `S_0 <= S_1` and by Lemma 5.2.
- `D_c` is `G`-invariant.

Applying Lemma 6.1 to `A = C`,

    M̄(D_c) = M̄(C) - M̄(C ∩ τL_c) = M̄(C) - M̄(τ^{-1}C) = ∫ f dM̄,   f = 1_C - 1_C ∘ τ.        (Flux)

Both terms are finite, so `f` is `M̄`-integrable.

*`f` vanishes off split configurations.* Let `P(x)` be `S_0`-connected and `γ ∈ P(x)`. Then
`P(x) ⊆ γ D_{(k-1)S_0}`, and by (F1) `P(τx) ⊆ γ D_{(k-1)S_0 + 1}`. Any two points of this set are
`(2(k-1)S_0 + 2)`-close, hence `S_1`-close. `P(τx)` is nonempty by conservation. So `x ∈ C` and `τx ∈ C`,
and `f(x) = 0`.

The flux is carried by configurations whose particle set is `S_0`-split. By Lemma 5.3 their images are
superpositions of the images of the pieces, each at a level below `c`. Step 7 compares them with genuinely
independent pieces.

## Step 7. Cluster expansion over independent-sea models

*Atoms.* An atom is a pair `a = (Γ, ω)` with the following properties.
- `Γ ⊂ G` is finite, nonempty and `S_0`-connected.
- `ω ∈ A^{ΓD_2}` has particle set exactly `Γ`.

It carries a charge `W(a)`, a weight `m(a) = |Z|^{-|ΓD_2|}`, and an output `o(a) = P(τx) ∩ ΓD_1` for any
`x ∈ L` with `x|_{ΓD_2} = ω` in which no other particle is `4`-close to `Γ`. By Lemma 5.3 the output is
well defined. The atoms of `x ∈ L` are its `S_0`-components with their windows. Since `S_0 >= 5`, the
windows of distinct atoms of `x` are disjoint.

A finite sequence of atoms `a = (a_1, …, a_m)` has a closeness graph `E(a)` on `{1, …, m}`: `i ~ j` for
`i != j` when some point of `Γ_i` is `S_0`-close to some point of `Γ_j`. Put:

    r(a) = Σ_j 1[1 ∈ Γ_j] / Σ_j |Γ_j|,
    F(a) = [∪_j Γ_j is S_1-connected] - [∪_j o(a_j) is S_1-connected].

*Real side.* Call a set of atoms far if its closeness graph has no edges. For a far set `𝔞` of charge `c`, the
configurations whose atom set is `𝔞` form the cylinder that fixes the disjoint windows and is `Z`-valued
elsewhere. Its mass is `Π m(a)`. On this cylinder `f = F(𝔞)`, by Lemma 5.3, and
`1[1 ∈ P]/|P| = r(𝔞)`. These cylinders partition `L_c` into countably many pieces, so

    M̄(D_c) = Σ_{far sets 𝔞 of charge c} r(𝔞) F(𝔞) Π_{a ∈ 𝔞} m(a),                (R)

and the sum converges absolutely. Singletons contribute `0` by the end of Step 6.

*Models.* Take `n >= 2` and an ordered composition `c = c_1 + … + c_n` into charge values `c_i > 0`. Every
`c_i < c`. Put:
- `X = L_{c_1} × … × L_{c_n}`, with the measure `M^{⊗n}` and the diagonal `G`-action;
- `T̃ = τ × … × τ`;
- `N(ξ) = Σ_i |P(x_i)|` for `ξ = (x_i)`.

By the induction hypothesis each factor map is a bijection of `L_{c_i}` preserving `M`. So `T̃` is a
bijection of `X` preserving `M^{⊗n}`: it does so on rectangles, which form a π-system, and Lusin–Souslin
handles the images as in Step 1. Define:

    M̄_n(A) = ∫_A #{i : 1 ∈ P(x_i)} / N(ξ) dM^{⊗n},
    C̃ = {ξ : ∪_i P(x_i) is S_1-connected}.

The proof of Lemma 6.1 applies with `m(ξ, g, h) = 1_A(T̃ξ) #{i : g ∈ P(x_i)} #{j : h ∈ P(τx_j)} / (N(ξ) N(T̃ξ))`.
Since `T̃` is onto, it gives `M̄_n(T̃^{-1}A) = M̄_n(A)` for invariant `A`. As in Step 6, `M̄_n(C̃) < ∞`, so

    ModelFlux(c_1, …, c_n) = ∫ (1_{C̃} - 1_{C̃} ∘ T̃) dM̄_n = M̄_n(C̃) - M̄_n(T̃^{-1}C̃) = 0.        (M)

*Expanding a model into atoms.* For `ξ ∈ X`, let `𝔟_i` be the far atom set of `x_i`.
- `1_{C̃}(ξ) - 1_{C̃}(T̃ξ) = F(𝔟_1 ⊎ … ⊎ 𝔟_n)`. This uses Lemma 5.3 inside each factor, and
  `P(τx_i) = ⊔_{a ∈ 𝔟_i} o(a)`.
- The density `#{i : 1 ∈ P(x_i)}/N(ξ)` equals `r` of the concatenated atoms.
- The cell `{ξ : the atom set of x_i is 𝔟_i for all i}` has mass `Π_i Π_{a ∈ 𝔟_i} m(a)`.

So `ModelFlux` is an absolutely convergent sum over tuples `(𝔟_1, …, 𝔟_n)` of far sets with charges `c_i`.

Such a tuple is the same thing as a set of `m = Σ|𝔟_i|` distinct labeled items `(i, a)`. Listing the items in
order gives exactly `m!` pairs `(a_1, …, a_m; β)`, where:
- `β : {1..m} → {1..n}` is a surjection;
- every fiber of `β` is independent in `E(a)`, since a fiber is a far set;
- and conversely each such pair comes from exactly one tuple.

Sum `(M)` with weights `(-1)^n / n` over `n >= 2` and all ordered compositions of `c`. This is a finite
combination of absolutely convergent series. Here `n <= k`, and there are finitely many charge values below `c`.
The result is

    0 = Σ_m (1/m!) Σ_{(a_1..a_m), Σ W(a_j) = c} r(a) F(a) Π_j m(a_j) · κ(E(a)),

with

    κ(E) = Σ_{n >= 2} ((-1)^n / n) · n! · S_n(E) = Σ_{n >= 2} (-1)^n (n-1)! S_n(E).

Here `S_n(E)` is the number of partitions of the vertex set into `n` independent blocks. The ordered
surjections are counted by `n! S_n`.

*The coefficient.* The chromatic polynomial is `χ_E(x) = Σ_n S_n(E) x(x-1)…(x-n+1)`, whose coefficient of `x`
is `Σ_n (-1)^{n-1}(n-1)! S_n(E)`. Hence `κ(E) = S_1(E) - [x]χ_E = [E has no edges] - [x]χ_E`.
- *No edges, `m >= 2`.* Then `χ_E = x^m`, so `κ = 1`.
- *`m = 1`.* Then `κ = 1 - 1 = 0`.
- *Some edge, disconnected.* `χ_E` is the product of the chromatic polynomials of the components, each
  divisible by `x`. So `[x]χ_E = 0` and `κ = 0`.
- *Connected, `m >= 2`.* The terms vanish for another reason, namely `F(a) = 0`. Each `Γ_j` is `S_0`-connected,
  and the edges join them by `S_0`-close pairs. So `∪Γ_j` is an `S_0`-connected set, and it has at most `k`
  points because the total charge is `c`. Also `∪o(a_j) ⊆ (∪Γ_j) D_1` is nonempty. The bound at the end of
  Step 6 makes both unions `S_1`-connected.

So only sequences with no edges and `m >= 2` survive, with coefficient `1`. These are the `m!` orderings of
the far sets of `m` atoms. Since `r` and `F` are symmetric, the surviving sum is exactly the right side of
(R). Therefore `M̄(D_c) = 0`.

*From measure zero to empty.* Let `E ∋ 1` be `S_0`-connected with at most `k` points, and let
`p ∈ (A∖Z)^E` have charge `c`. Put `K = L_{E,p}`. It is compact, homeomorphic to `Z^{G∖E}`, and `M|_K` is a
multiple of the full-support measure `ν`.
- By Lemma 5.1, `τ^{-1}K ∩ L_c` lies in `{x ∈ L_c : P(x) ⊆ E D_ρ}`. This set is compact: `x` is `Z`-valued
  off a finite set, and the charge is read from that set.
- So `τ(L_c) ∩ K` is compact, and `D_c ∩ K` is open in `K`.
- `M̄(D_c) >= M(D_c ∩ K)/k`, so `D_c ∩ K` is a null open set, hence empty.
- Every element of `D_c` has a translate in some such `K`, by Lemma 5.2.

So `D_c = ∅` and `τ(L_c) = L_c`.

*Conclusion.* Charge values form a set with finitely many elements below every bound, so induction fills
every level and conserves `W` on all of `L`. Item 3 now shows that `Φ` is onto, so `τ` is onto because `r` is.
With the countable reduction, this proves the target: one of `q`, `|Z|`, `q|Z|` lies in `NS(G)`, or `Φ` and
`τ` are surjective.

## Where each hypothesis is used

- Injectivity of `Φ` and `τ` is used in Steps 0, 2 and 3.
- Steps 1 and 4 to 7 use only three facts: `τ` is injective on `L`, `τ` is bijective on `Z^G`, and
  `W ∘ τ <= W`. So they show that every automaton with these three properties maps `L` onto `L`
  (Steps 4 to 7 are that statement).
- *On `G`.* The measures need `G` countable, for σ-finiteness, the π-system and Lusin–Souslin. The countable
  reduction at the start of Step 5 applies to every step, since all the automata involved act coset by coset.
  No other property of `G` is used: no soficity or amenability, and no finite approximation.
- *Why Step 4 alone stops at `2 w_min`.* Two-particle configurations rooted at one particle still form a
  noncompact set of infinite measure, because every relative position is allowed. Measure preservation of `τ`
  alone therefore says nothing there.
- *How Steps 5 to 7 get past it.* They measure only the flux across the boundary of the finite-measure set of
  `S_1`-connected configurations. That flux is carried by split configurations. The same flux vanishes in the
  product models, because the lower levels are already bijective. Inclusion and exclusion over the
  independent-sea models matches the two sides exactly: the chromatic coefficient `κ` is `1` on far atom
  families and `0` on disconnected overlapping ones, and connected ones carry no flux.
