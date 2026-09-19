---
rg: 2
id: l2-finite-projectives-over-amenable-groups-satisfy-weak-bass
kind: claim
title: Over a torsion-free amenable group, a countably generated projective integral module of finite L2-dimension has rational rank at most its L2-dimension
distinct_from:
  amenable-cd-two-bass-defect-equals-euler-characteristic: that proves the rank-gap target follows from this inequality for one module, the relation module of a cd-2 group, and that flatness and finite truncations cannot give it; this is the inequality for all countably generated projectives
  l2-small-projectives-with-rank-gap-are-finitely-generated: that shows an L2-small projective is finitely generated when a rank gap holds; this asks for a Bass-type inequality on the core with no finitely generated summand, with no rank-gap hypothesis
---

**OPEN.** Let `G` be a torsion-free amenable group, `U = U(G)`, and let `C` be a countably
generated projective `Z[G]`-module with `dim_U(U ⊗_{Z[G]} C) < ∞`. Then

> `rank_Q(Q ⊗_{Z[G]} C) <= dim_U(U ⊗_{Z[G]} C)`,

where `Q` is the trivial module. In other words, the Bass defect `D(C)` of
`amenable-cd-two-bass-defect-equals-euler-characteristic` is `<= 0`.

**Why it matters.** By item 3 of `amenable-cd-two-bass-defect-equals-euler-characteristic`, this
statement implies `amenable-cd-two-groups-have-an-l2-rank-gap`, and so Kropholler's question in
dimension 2. It is enough to have it when `G` is finitely generated with `cd G = 2` and finite
abelianization, and `C` is the part `P'` of the relation module that has no nonzero finitely
generated direct summand. For a counterexample `K`, that `P'` has `D(P') = 1 + b_2(K) >= 1`.
This is the direction proved. The converse is not known.

**What is known.**

- *Finitely generated `C`:* equality holds. This is the weak Bass conjecture for amenable groups
  (Berrick–Chatterji–Mislin; recalled): the Hattori–Stallings rank of `C` is concentrated at `1`.
- *Direct sums* of modules for which it holds: both sides are additive in `[0, ∞]`.
- *Induction from a subgroup:* for `H <= G` and `C` over `Z[H]`,
  `Q ⊗_{Z[G]} (Z[G] ⊗_{Z[H]} C) = Q ⊗_{Z[H]} C`, and the `U(G)`-dimension of the induced module
  equals the `U(H)`-dimension of `U(H) ⊗ C`. So the class of `(G, C)` satisfying the inequality is
  closed under induction.
- *Virtually finitely generated abelian `G`:* take a normal free-abelian `A` of finite index.
  `Z[A]` is commutative noetherian with connected spectrum, so by Bass ("big projective modules are
  free"; recalled) the restriction of `C` to `A` is either free of infinite rank, which gives
  `dim = ∞`, or finitely generated. So `C` is finitely generated over `Z[G]`, and the first case
  applies. This is Step 5 of `amenable-cd-two-bass-defect-equals-euler-char-proof`.

**Calibrations (hypotheses that cannot be dropped).**

- *Torsion-freeness.* With coefficients `Q[G]` and `G` finite, `C = Q[G]e` for
  `e = |G|^{-1} Σ g` has rank 1 and `U`-dimension `1/|G|`.
- *Projectivity, not flatness.* Over the Hantzsche–Wendt group, the flat colimit module `M_B` of
  item 5 of `amenable-cd-two-bass-defect-equals-euler-characteristic` has rank `n`, `U`-dimension
  `n − 1` and defect 1. So the analogous inequality for countably generated flat modules is
  false. Any proof has to use a splitting `C ⊕ C'' = Z[G]^(∞)` and not just a colimit
  presentation.
- *Finite `L²`-dimension.* Without it, `C = Z[G]^(∞)` gives `∞ <= ∞`, which says nothing. A
  hypothesis weaker than finite dimension, such as "no finitely generated summand", would not
  give a numerical statement.

**Where a proof would have to go.** Write `C` as the image of an idempotent
`E ∈ M_∞(Z[G])` (each row finitely supported), acting by right multiplication. Then
`rank_Q(Q ⊗ C) = rank_Q ε(E)`. For a finite matrix `E`, `dim_U = tr_{NG}(E) = Σ_i E_{ii}(1)`, and
the Bass conjecture gives `rank ε(E) = Σ_i Σ_g E_{ii}(g) = tr_{NG}(E)`. For an infinite `E`,
neither identity is available. The sums need not converge absolutely, and `ε(E)` is an
idempotent of infinite size whose rank is not controlled by its diagonal.
The obstruction items 4–6 of `amenable-cd-two-bass-defect-equals-euler-characteristic` show that
finite corners of `E` and the `U`-dimensions alone cannot carry the argument. A proof has to use
the relation `E² = E` over `Z[G]` globally, for example through a trace on a suitable ideal of
column-finite matrices that restricts to the Hattori–Stallings trace on finite corners.

## Attempts

- **2026-09-18 (lane `w13-112`): specialization from the universal field. Proved for locally
  indicable and virtually locally indicable groups. Flat arguments work for exactly the locally
  indicable groups.** See `flat-weak-bass-holds-exactly-for-locally-indicable-groups`
  (proposed ESTABLISHED).
  - *Characterization.* For every group `G`, the following are equivalent:
    - `G` is locally indicable;
    - `rank_Q ε(A) <= rk_U(A)` for every matrix `A` over `Z[G]`;
    - `rank_Q(Q ⊗ M) <= dim_U(U ⊗ M)` for every flat module `M`.

    The proof of the forward direction: by Jaikin-Zapirain (2021), `D(G)` is the universal
    division ring of fractions, and Cohn specialization to the augmentation gives the rank
    inequality. Lazard's theorem then carries it to flat modules. The converse: Fox matrices of
    a finitely generated subgroup with `b_1 = 0` give a flat module `M_B` of positive defect.
  - *New cases of this node.* The statement holds for every locally indicable group, amenable or
    not, and for all flat modules. It is subgroup-closed. By Swan's theorem it passes up finite
    index, with `rank_Q(Q ⊗_G C) = rank_Q(Q ⊗_N C)/[G:N]`. So it holds for every virtually
    locally indicable group, and a proof for `K` may pass to any finite-index subgroup first.
  - *Obstruction.* Item 5 of `amenable-cd-two-bass-defect-equals-euler-characteristic` was a
    Hantzsche–Wendt example. It now holds for every group that is not locally indicable. In
    particular the counterexample `K` itself carries a countably generated flat module of defect
    `>= 1`. `K` is not virtually locally indicable, since otherwise it would be elementary
    amenable. So every case of this node that matters for the flagship lies outside the reach
    of flat arguments.
  - *Where the difference is visible.* Hantzsche–Wendt separates the flat statement from the
    projective one. There the statement holds only because of Swan's theorem: the
    `Q[G/N]`-module `Q[G/N] ⊗ C` is free, so its trivial isotypic part is exactly its `1/[G:N]`
    share. `M_B` violates this.
  - *Next step.* Find a replacement for Swan's theorem when `K` has no finite-index locally
    indicable subgroup. Concretely, for `N ⊴ K` with `K/N` infinite and amenable, does
    `Z[K/N] ⊗_{Z[K]} C` satisfy an isotypic-share identity in the sense of `U(K/N)`? This is an
    "L²-Swan" statement for big projectives over the quotient.
- **2026-09-18 (lane `w14-112`): L²-Swan. It is weak Bass over the quotient and cannot be
  lifted. Over residually finite groups the target is Lück approximation.** See
  `rf-weak-bass-defect-is-degree-two-approximation-defect` (proposed ESTABLISHED).
  - *Finite-quotient Swan for big projectives.* For any `K`, any `C` with `r(C) < ∞` and any
    finite quotient `F`, `Q[F] ⊗ C ≅ Q[F]^{r(C)}`. The proof: Bass's big-projectives theorem
    forces `Z[F] ⊗ C` to be finitely generated, and then Swan applies.
  - *Residually finite `K`.* `D(C) >= 0` always. `D(C)` equals the failure of Lück approximation
    for `C`, given by an explicit interchange-of-limits formula over row truncations. So this
    node, for residually finite groups, says exactly: the idempotent's row truncations approximate
    uniformly.
  - *cd 2.* Without finite presentability, `χ_Q` is multiplicative on finite-index subgroups. In
    the residually finite amenable case, `D(P) = χ_Q = lim b_2(N_i)/[K:N_i]`.
  - *Consequence: Kropholler's question for residually finite groups is equivalent, in both
    directions, to `b_2(N_i) = o([K:N_i])`.* This is Lück approximation in degree 2, and it is
    also equivalent to this node for relation modules. A residually finite counterexample has
    `b_2(N) >= [K:N] − 1` for every finite-index `N`.
  - *Obstruction for L²-Swan.* For `C = P` and `Γ = K/N` infinite, L²-Swan is the inequality
    `χ^{(2)}(K; Γ) >= χ_Q(K)`, i.e. this node over `Γ`. Lifting it from `Γ` to `K` needs
    `χ^{(2)}(K; Γ) <= 0`. In a counterexample the two cannot both hold, for any `Γ`. The lifting
    inequality is false for finitely presented modules (`Z²`, `Z[K]/(x−1)`). If `b_1(K) = 0`, the
    only locally indicable quotient is trivial.
  - *Next step.* Degree-2 Lück approximation for residually finite amenable groups of cd 2
    without type `FP_2`. Show `b_2(N_i)/[K:N_i] → 0`, or build a residually finite amenable
    `K` with `b_1 = 0` whose `b_2` grows linearly with slope `1 + b_2(K)`. Non-residually-finite
    counterexamples remain outside this reduction.
- **2026-09-18 (lane `w15-112`): pro-p completions and Golod–Shafarevich. `D(P) >= 0` holds
  without residual finiteness, and a counterexample has `b_1 = O(√index)` on every finite cover.**
  See `amenable-cd-two-pro-p-completions-not-golod-shafarevich` (proposed ESTABLISHED).
  - *Exact mod-p Euler characteristics.* Finite-quotient Swan passes to `Z_p[F]`-lattices,
    because projectives over `Z_p[F]` are determined by their `Q_p`-character. So
    `1 − b_1(N; F_p) + b_2(N; F_p) = [K:N] χ_Q(K)` for every finite-index `N` and every `p`, and
    `H_2(N; Z)` is free.
  - *Golod–Shafarevich bound.* The pro-p completion of `N` has at most `d − 1 + [K:N]χ`
    relations. It is not GS, by Ershov–Jaikin-Zapirain (a GS group has an infinite (T)
    quotient). So `(b_1(N; F_p) − 2)² <= 4 [K:N] χ` unless `b_1(N; F_p) <= 1`. Consequences:
    - `χ >= 0`, i.e. `D(P) >= 0` for the relation module, for every finitely generated
      amenable cd-2 group, not only residually finite ones;
    - `b_1(N; Q) <= 2 + 2√([K:N]χ)` uniformly over all finite-index `N`;
    - if `χ = 0`, every pro-p completion of every finite-index subgroup is p-adic analytic of
      dimension `<= 2`, with `b_1(N; F_p) <= 2`.
  - *Where it stops.* GS turns few relations into non-amenability. A counterexample has many
    relations (`b_2 ~ (1 + b_2(K))·index`) and few generators, so the bound constrains a
    counterexample and does not refute one. The information lost is the injection
    `H^2(N_p̂) → H^2(N)`. Under p-goodness, the open question becomes pro-p: does an infinite
    finitely generated pro-p group of cd 2 with `χ > 0` have a GS open subgroup? Perfect-cover
    counterexamples, whose pro-p completions are all finite, are invisible to this route.
  - *Next step.* Either settle that pro-p question, or combine the `O(√index)` bound on `b_1`
    with the `(1 + b_2(K))·index` growth of `b_2` in a single finite cover, for example through
    the cup-product map `Λ² H^1(N; F_p) → H^2(N; F_p)`, whose image has dimension
    `O(index)`.
- **2026-09-18 (lane `w16-112`): the cup-product step and the pro-p fallback are killed by a
  Kazhdan lattice. Profinite data cannot see amenability here.** See
  `pro-p-route-cannot-see-amenability-in-cd-two` (proposed ESTABLISHED; the congruence subgroup
  property is imported).
  - *The calibration group.* Let `Γ` be a torsion-free finite-index subgroup of `SU(h)(Z[1/2])`,
    where `h` is the definite hermitian form over `Q(√−7)`. Then `Γ` is a cocompact lattice in
    `SL_3(Q_2)`. It acts freely on the building, with `V` vertex orbits, `7V` edge orbits and `7V`
    triangle orbits, so it has type F, cd 2 and `χ = V >= 1`.
    - Property (T) gives `b_1(N; Q) = 0` and `b_2(N; Q) = V[Γ:N] − 1` for every finite-index
      `N`. This is the exact profile of a finite-abelianization counterexample.
    - By the congruence subgroup property, every `N_p̂` is finite (`p = 2`) or p-adic analytic
      (`p` odd), so none is Golod–Shafarevich. So `Γ` satisfies the bound
      `b_1(N; F_p) <= 2 + 2√(V[Γ:N])` of the `w15-112` node.
    - No `N` is p-good with `N_p̂` infinite, since an analytic pro-p group of cd `<= 2` has
      `χ = 0`.
  - *What dies.* Suppose an argument uses amenability only through the non-GS property of pro-p
    completions. It may add Euler identities, Bass/Swan structure over finite quotients, cup or
    Massey products in `H^*(N; F_p)`, or degree-refined GS inequalities. Any such argument would
    prove `χ(Γ) <= 0`. This includes the planned combination of `b_1 = O(√index)` with
    `b_2 ~ χ·index` through `Λ² H^1 → H^2`. It also includes the pro-p fallback, since even a
    positive answer only yields "no p-good infinite completion", which `Γ` already has.
  - *What amenability must supply.* `Γ` differs from a counterexample in two ways:
    - `b_2^{(2)}(Γ) = V > 0`, its relation module is free, and `D = 0`;
    - it has (T), so its finite quotients are expanders.

    A refutation must therefore use `L²` vanishing, which is this node, or Følner-type failure
    of (τ) in the finite quotients. Mod-p cohomology alone cannot do it.
  - *Next step.* For residually finite `K`, attack the degree-2 approximation
    `b_2(N_i)/[K:N_i] → 0` of `rf-weak-bass-defect-is-degree-two-approximation-defect` by
    transferring Følner sets of `K` into the finite quotients `K/N_i`. The quantity to control is
    `H_2` of `P ⊗ Z[K/N_i]` restricted to Følner-tiled pieces. Test it first on `Γ`, where the
    same scheme must fail because its quotients expand.
