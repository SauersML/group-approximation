# Pointed pre-injectivity gives sections of cover pairs (2026-09-18)

Agent `swarm-0917-w14-w14-gs-last1`, wave swarm-0917. Target: `constant-point-sft-domains-admit-no-post-surjective-covers`
(CP), and through it `gottschalk-surjunctivity-conjecture`. Claim: `pointed-pre-injective-cover-pairs-admit-sections`.

## 0. Setting and conventions

- `A` is a finite alphabet and `G` a group, acting by `(g.x)(h) = x(g^-1 h)`. So `(g^-1.x)(1) = x(g)`.
- `x ~ x'` means that `x` and `x'` differ at finitely many sites. `Δ(x, x')` is the set of those sites.
- `Fin_p(X) = {x ∈ X : x ~ p}`.
- `X ⊆ A^G` is a closed `G`-invariant subshift. `F : X → A^G` is continuous and equivariant.
- `F` is *strongly post-surjective with lifts in `X`* with constant `Φ` (finite) if, for all `x ∈ X` and
  `z ~ F(x)`, there is `x' ∈ X` with `x' ~ x`, `F(x') = z` and `Δ(x, x') ⊆ Δ(F(x), z)Φ`. This is the definition of
  `strict-pairs-give-dual-failures-on-bounded-defect-domains` and of the scheduled-sections artifact.
- A *cover pair* adds that `X ⊊ A^G` is an SFT. A *section* is a continuous equivariant `s : A^G → X` with
  `F ∘ s = id`.

Finite type is never used below; only closedness of `X` is.

## 1. Theorem P

**Theorem P.** Let `c^G ∈ X` be a constant and put `d^G = F(c^G)`, which is constant because `F` is equivariant.
If `F` is injective on `Fin_c(X)`, then `(X, F)` has a section. The section is the cellular automaton with memory
`Φ^-1` whose local rule `σ` is read off unique pointed lifts. If `X ≠ A^G`, then `G` is not surjunctive.

*Proof.*

**(1) Existence and uniqueness of pointed lifts.** Let `y ∈ Fin_d(A^G)`. Apply the lift property at
`x = c^G`, `z = y` (note `y ~ d^G = F(c^G)`). This gives `x' ∈ X` with `x' ~ c^G` and `F(x') = y`. Any two such
points lie in `Fin_c(X)` and have the same image, so they coincide. Write `s(y)` for this point. Then
`s : Fin_d(A^G) → Fin_c(X)` satisfies `F(s(y)) = y`. It is a bijection, since `F` maps `Fin_c(X)` into `Fin_d`
(`F` is a sliding block code) and is injective there.

**(2) The value at `1` depends only on `y|_(Φ^-1)`.** Let `y, y' ∈ Fin_d(A^G)` with `y|_(Φ^-1) = y'|_(Φ^-1)`. Put
`Δ = Δ(y, y')`. It is finite and `Δ ∩ Φ^-1 = ∅`. If `1 ∈ ΔΦ`, then `1 = δφ` for some `δ ∈ Δ`, `φ ∈ Φ`, so
`δ = φ^-1 ∈ Φ^-1`, which is impossible. So `1 ∉ ΔΦ`.
- Apply the lift property at `x = s(y)` with `z = y'`. Here `y' ~ y = F(s(y))`.
- It gives `x' ∈ X` with `x' ~ s(y)`, `F(x') = y'` and `Δ(s(y), x') ⊆ ΔΦ`.
- Then `x' ~ c^G`, so `x' ∈ Fin_c(X)` with `F(x') = y'`. By (1), `x' = s(y')`.
- Since `1 ∉ Δ(s(y), x')`, `s(y')(1) = s(y)(1)`.

Every pattern `π ∈ A^(Φ^-1)` is the restriction of some `y ∈ Fin_d`: put `π` on `Φ^-1` and `d` elsewhere. So
`σ(π) = s(y)(1)`, for any `y ∈ Fin_d` with `y|_(Φ^-1) = π`, defines a map `σ : A^(Φ^-1) → A`.

**(3) Equivariance.** Let `g ∈ G` and `y ∈ Fin_d`. Then `g.y ∈ Fin_d`. The point `g.s(y)` lies in `X` (invariance),
is asymptotic to `g.c^G = c^G`, and has image `F(g.s(y)) = g.F(s(y)) = g.y`. By (1), `s(g.y) = g.s(y)`. Hence

```text
s(y)(g) = (g^-1.s(y))(1) = s(g^-1.y)(1) = σ((g^-1.y)|_(Φ^-1)),     and   (g^-1.y)(φ) = y(gφ).
```

**(4) Extension by density.** Let `s̄ : A^G → A^G` be the cellular automaton `s̄(y)(g) = σ((y(gφ))_(φ ∈ Φ^-1))`. It
is continuous and equivariant, and by (3) it agrees with `s` on `Fin_d(A^G)`. The set `Fin_d(A^G)` is dense in
`A^G`, because every cylinder contains a point equal to `d` outside a finite set.
- *Image in `X`.* `s̄(Fin_d) = s(Fin_d) ⊆ X`. `X` is closed and `s̄` is continuous, so `s̄(A^G) ⊆ X`.
- *Right inverse.* `F ∘ s̄` and `id_(A^G)` are continuous maps `A^G → A^G` that agree on the dense set `Fin_d`,
  so `F ∘ s̄ = id`.

So `s̄` is a section.

**(5) Non-surjunctivity.** `F ∘ s̄ = id` forces `s̄` to be injective. If `X ≠ A^G`, then `s̄(A^G) ⊆ X ⊊ A^G`, so `s̄`
is an injective, non-surjective cellular automaton on `A^G`. `∎`

**Remarks on the proof.**
- The only uses of group structure are `g.c^G = c^G` in (3) and the inversion `Φ ↦ Φ^-1` in (2).
- No colouring, seed or scheduling appears. Lifts made at sites whose write region `gΦ` misses `1` never touch
  `1`. Uniqueness then makes the lift independent of the order and the route taken. This is exactly what the
  scheduled sections needed a colouring for.
- Pointed injectivity is a hypothesis on one asymptotic class only. It is strictly weaker than pre-injectivity,
  since `F` may fail to be injective on other classes.

## 2. Theorem P' (periodic points)

**Theorem P'.** Let `H ≤ G` have finite index, let `p ∈ X` satisfy `H.p = p`, and put `q = F(p)`, which is also
`H`-fixed. If `F` is injective on `Fin_p(X)`, there is a continuous `H`-equivariant `s̄ : A^G → X` with
`F ∘ s̄ = id`. If `X ≠ A^G`, then `G` is not surjunctive.

*Proof.*
- **Lifts.** Step (1) goes through verbatim and gives `s : Fin_q(A^G) → Fin_p(X)`.
- **Locality.** Step (2) is run at an arbitrary site `t`. If `y, y' ∈ Fin_q` agree on `tΦ^-1`, then
  `t ∉ Δ(y, y')Φ`, so `s(y)(t) = s(y')(t)`. This defines `σ_t : A^(tΦ^-1) → A`, with every pattern realised by
  filling with `q`.
- **Equivariance.** Step (3) gives `s(h.y) = h.s(y)` for `h ∈ H`, because `h.p = p`.
- **Local rules.** Fix a finite right transversal `T` (`G = ⊔_(t ∈ T) Ht`). Then
  `s(y)(ht) = s(h^-1.y)(t) = σ_t(((h^-1.y)(tφ))_(φ ∈ Φ^-1)) = σ_t((y(htφ))_(φ ∈ Φ^-1))`.
- **Extension.** The right-hand side defines a continuous `H`-equivariant `s̄` on `A^G`, which agrees with `s` on
  the dense set `Fin_q(A^G)`. Step (4) gives `s̄(A^G) ⊆ X` and `F ∘ s̄ = id`.
- **Recoding.** `x ↦ (h ↦ (x(ht))_(t ∈ T))` is an `H`-equivariant homeomorphism `A^G ≅ B^H` with `B = A^T`. `H`
  acts on `G` by left multiplication and preserves each right coset `Ht`. Under it, `s̄` becomes an injective,
  non-surjective automaton `θ` over `H`, with memory `N` and rule `μ`.
- **Induction.** `θ_G(x)(g) = μ((x(gn))_(n ∈ N))` acts on each left coset `g_i H` as a copy of `θ`. So it is
  injective and not surjective over `G`. `∎`

`cover-pair-sections-pull-back-along-retraction-data` (T3, landed on the bus by `swarm-0917-w13-w13-gs-follow`)
records the same finite-index relaxation for sections. Theorem P' supplies the section from pointed injectivity.

## 3. Theorem Q: sections are exactly pointed prunings

**Theorem Q.** For a cover pair `(X, F)` (or any closed `X` with `F` strongly post-surjective with lifts in `X`)
the following are equivalent.
1. `(X, F)` has a section.
2. *(Pointed pruning.)* There are a closed `G`-invariant `X' ⊆ X` and a constant `c^G ∈ X'` with these two
   properties: `F|_(X')` is strongly post-surjective with lifts in `X'`, and it is injective on `Fin_c(X')`.

*Proof.*
- **2 ⇒ 1.** Theorem P applied to `(X', F|_(X'))` gives `s̄ : A^G → X' ⊆ X` with `F ∘ s̄ = id`.
- **1 ⇒ 2.** Let `s` be a section with memory `M_s`. Put `X' = s(A^G)`. It is compact and invariant, hence a
  closed subshift of `X`.
  - *It contains a constant.* `s(a^G)` is `G`-fixed, hence constant.
  - *`F` is injective on `X'`.* Every `x ∈ X'` equals `s(F(x))`: write `x = s(y)`, and then `F(x) = y`.
  - *Lifts stay in `X'`.* Let `x = s(y) ∈ X'` and `z ~ F(x) = y`. Put `x' = s(z) ∈ X'`. Then `F(x') = z`. Also
    `s(z)(g) ≠ s(y)(g)` forces `gM_s ∩ Δ(y, z) ≠ ∅`, so `Δ(x, x') ⊆ Δ(y, z)M_s^-1`. Hence `F|_(X')` is strongly
    post-surjective with lifts in `X'` and constant `M_s^-1`. `∎`

`X'` may be taken sofic (an automaton image of the full shift), and in general it cannot be taken to be the
whole of `X`.

**Consequence (the de-colouring need 36774ad3 restated as a pruning problem).** Need 36774ad3 asks whether every
constant-point cover pair (over every group) has a section. By Theorem Q this is the statement

```text
PRUNE:  every constant-point cover pair (X, F) contains a closed invariant lift-closed X' through some
        constant c^G on which F is injective on Fin_c(X').
```

- PRUNE(G) together with surjunctivity of `G` gives CP(G). A pair would have a section by Theorem Q, which is
  impossible by Proposition C (or by Theorem P, step 5).
- At a surjunctive `G`, CP(G) and PRUNE(G) are both equivalent to "there are no constant-point cover pairs".
  So PRUNE adds nothing group by group. Its content is as a proof strategy for `Gottschalk ⇒ CP`, uniform in
  `G`: find `X'` by deleting the colliding perturbations.
- PRUNE is refutable at any group. A deficient pair, or any section-less pair over a non-surjunctive group,
  refutes it (Section 5).
- Operationally, a counterexample to CP at a surjunctive group is a constant-point cover pair in which every
  closed, invariant, lift-closed subsystem through a constant has two distinct finite perturbations of that
  constant with equal image. This is a condition on finite perturbations only, with no colouring, seed or
  symmetric locus.

## 4. Corollaries

**C1 (surjunctive groups collide everywhere).** Let `G` be surjunctive and `(X, F)` a cover pair. For every
finite-orbit point `p ∈ X`, `F` is not injective on `Fin_p(X)`. If `p` has stabilizer `H` of finite index,
Theorem P' applies. In particular `F` is not pre-injective. If CP fails at a surjunctive `G`, then at every
constant `c^G` of the counterexample domain there are `x ≠ x'` in `Fin_c(X)` with `F(x) = F(x')`.

**C2 (CP equals constant-point PSD).** Let PSD_c(G) say that every constant-point cover pair over `G` is
pre-injective, and let PSD_c^SI(G) restrict this to strongly irreducible domains. Then CP(G) ⟺ PSD_c(G) and
CP^SI(G) ⟺ PSD_c^SI(G).
- "⇒" is vacuous.
- "⇐" goes as follows. A constant-point pair is pre-injective, so by Theorem P `G` is not surjunctive, and `G`
  carries a strict pair `(τ, σ)`. By `strict-pairs-give-dual-failures-on-bounded-defect-domains` (items 1, 2, 4
  and 5, with the parameters stated there), `(X_R, σ|_(X_R))` is a cover pair over the same alphabet. It is
  strongly irreducible, contains the constant `τ(a^G)` and is not pre-injective. This contradicts PSD_c
  (respectively PSD_c^SI).

So `proper-sft-domains-admit-no-dual-failures`, restricted to constant-point domains, is at each group
equivalent to CP restricted to strongly irreducible domains. The kill-test recorded in that node ("a strongly
irreducible arrow-type example would refute it") therefore splits cleanly:
- at a surjunctive group, a strongly irreducible constant-point example refutes PSD and CP together;
- a strongly irreducible example with no finite orbit bears on PSD only.

**C3 (Gottschalk as pointed injectivity on a proper subshift).** `G` is non-surjunctive iff some proper closed
subshift `X ⊊ A^G` contains a constant `c^G` and carries a strongly post-surjective `F : X → A^G`, with lifts in
`X`, that is injective on `Fin_c(X)`.
- "⇐" is Theorem P, which uses closedness only.
- "⇒": take an injective non-surjective `τ` with memory `M`, `X = τ(A^G)` (proper and closed, containing the
  constant `τ(c^G)`) and `F = τ^-1`. `F` is continuous and equivariant, and `F(τ(z)) = z`. Lifts: for `x = τ(u)`
  and `z ~ u`, the point `τ(z) ∈ X` works, with `Δ(τ(u), τ(z)) ⊆ Δ(u, z)M^-1`.

Here `X` is sofic, not necessarily of finite type. Whether it can be taken of finite type is open. It can be
whenever `τ(A^G)` is an SFT.

**C4 (deficiency forces collisions).** Let `(X, F)` be a cover pair over any group and `D = A \ φ(C_X)` its
constant deficiency. If `D ≠ ∅`, then `F` is not injective on `Fin_c(X)` for any constant `c^G ∈ X`. Otherwise
Theorem P gives a section, and `cover-pair-sections-force-fixed-point-surjectivity` forces `D = ∅`. The same
holds for `D_H` and `H`-fixed points of finite-index `H`, via Theorem P'. An `H`-equivariant section maps
`Fix(K)` into `X ∩ Fix(K)` for every `K ≤ H`.

## 5. Calibrations (consistency checks, by hand)

- **Free monoid `{a,b}*`** (the calibration of `cover-pair-sections-force-fixed-point-surjectivity`). Take
  `X = {x : x(wb) = 0 for all w}` and `F(x)(w) = x(wa)`, with `D = {1}`. Let `δ_ε` be `1` at the empty word and `0`
  elsewhere. Then `δ_ε ∈ X`, since `ε` is not of the form `wb`. Also `F(δ_ε)(w) = δ_ε(wa) = 0` for all `w`, so
  `F(δ_ε) = F(0^G)`.
  - So the pair collides on `Fin_0(X)`, as C4 predicts from `D ≠ ∅`.
  - The collision is at the root, the one site that is not of the form `wa`.
- **Bounded-defect pairs `(X_R, σ)`.** They have the section `τ` and are not pre-injective (item 4 there). So
  pointed injectivity is sufficient for a section but not necessary. The pruning of Theorem Q is `X' = τ(A^G)`.
- **A non-free `G`-set (outside the theorem, for orientation only).** Let `BS(1,2)` act on the vertices of its
  Bass–Serre tree. Each vertex `v` has a parent and two children. Take `X = {x ∈ {0,1}^V : no vertex has both
  children equal to 1}` and `F(x)(v) = x(child_1(v)) ∨ x(child_2(v))`. This pair is post-surjective with lifts in
  `X` and `D = {1}`. The two single-site perturbations of `0` at the two children of one vertex have the same
  image. So it collides on `Fin_0`, as the group statement C4 would predict. This example is not a group shift,
  and it separates nothing.

## 6. What this kills, and what is left

**Class kill (invariant: injectivity of `F` on the asymptotic class of a finite-orbit point).** No search for a
counterexample to CP, or to `Gottschalk ⇒ CP`, at a surjunctive group can succeed inside pairs that are
injective on `Fin_p(X)` for some finite-orbit `p ∈ X`. The dying step is Theorem P, steps (2)–(4): unique
pointed lifts are local and extend by density to a section, and Proposition C then contradicts surjunctivity.
This removes, among others:
- partial conjugacies;
- inverses `τ^-1` of injective automata restricted to SFT images;
- "reversible cover" designs;
- every pre-injective candidate.

It also removes every strongly irreducible constant-point candidate that satisfies the conclusion of
`proper-sft-domains-admit-no-dual-failures`.

**What is left.** A counterexample at a surjunctive group must be a constant-point cover pair that collides at
every finite-orbit point, and every lift-closed subsystem through a constant must collide as well. The positive
direction of need 36774ad3 is now PRUNE of Section 3: delete colliding perturbations while keeping lifts. It
fails on deficient pairs (C4), so any proof of PRUNE must first show `D = ∅`. That is the open group question
recorded in `cover-pair-sections-force-fixed-point-surjectivity`.

**Not done.** CP is not decided at any nonsofic group. Whether the sofic domain in C3 can always be replaced by a
domain of finite type is open.

