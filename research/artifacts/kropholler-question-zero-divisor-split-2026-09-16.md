# Kropholler's question: the zero-divisor split and what survives in dimension three

Lane `hi-fron-amenable-groups-of-finite-cd-a` (frontier swarm), 2026-09-16.

Supports:

- the claims `amenable-finite-cd-integral-group-rings-are-domains` (H1) and
  `amenable-finite-cd-domain-groups-are-virtually-solvable` (H2);
- the routes `kropholler-question-via-zero-divisor-split` (H1 and H2 give the root
  `amenable-groups-of-finite-cd-are-virtually-solvable`) and
  `amenable-finite-cd-domains-via-kaplansky` (Kaplansky over `Q` gives H1).

**Scope.**

- Sections 1–3 are elementary consequences of the imports in Section 0.
- Sections 4–5 prove two special cases of H2 in dimension 3 by combining known theorems.
- Section 6 records exactly where Degrijse's dimension-2 argument stops in dimension 3, with an
  explicit example.
- Section 7 is a filter on candidate counterexamples.
- Novelty is not claimed for anything here. The combinations look folklore-level, and the
  literature search (Section 8) was not exhaustive.

Throughout, `cd` is cohomological dimension over `Z`. A ring is a *domain* when it is nonzero and
has no zero divisors.

## 0. Imports and standard facts

Imports, with where each statement was read:

- **(I1) Degrijse, Theorem A.** "Let G be an amenable group such that ℤ[G] is a domain. If G has
  cohomological dimension n and is of type FP_{n-1}, then G is of type FP."
- **(I2) Degrijse, Theorem B.** "Every amenable group G of cohomological dimension 2 such that ℤ[G]
  is a domain is solvable and hence isomorphic to a solvable Baumslag-Solitar group BS(1,m) for some
  non-zero m∈ℤ or to a non-cyclic subgroup of the additive rationals."

  Both are quoted verbatim from D. Degrijse, *Amenable groups of finite cohomological dimension and
  the zero divisor conjecture*, arXiv:1609.07635 (v1, 24 Sep 2016), read from the arXiv HTML render
  on 2026-09-16. Publication metadata from Crossref, 2026-09-16: Math. Ann. 386 (2023), no. 1–2,
  1151–1162, published online 28 June 2022. The published text was not read, and theorem numbering
  there may differ.
- **(I3) Hillman + Hillman–Linnell.** An elementary amenable group of finite cd is torsion-free of
  finite Hirsch length (Hillman, J. Austral. Math. Soc. Ser. A 50 (1991), Lemma 2). Such a group has a
  locally finite normal subgroup with virtually solvable quotient (repository node
  `hillman-linnell-finite-hirsch-length-theorem`). Degrijse's introduction combines the two in the
  sentence: "Since all elementary amenable groups of finite cohomological dimension must be
  torsion-free and have finite Hirsch length by [14, Lemma 2], one can conclude from [15, Corollary 1]
  that they are virtually solvable."
- **(I4) Stallings–Swan.** A group of cd at most 1 is free. Degrijse cites Stallings, Bull. Amer.
  Math. Soc. 74 (1968); Swan's extension to groups that are not finitely generated was not re-fetched.
- **(I5) Linnell / Kropholler–Linnell–Moody.** A torsion-free elementary amenable group has domain
  complex group algebra (repository node `elementary-amenable-torsion-free-strong-atiyah`).
- **(I6) Strebel.** A subgroup of infinite index in a `PD_n` group has cd `< n`. Source:
  R. Strebel, Comment. Math. Helv. 52 (1977), not re-fetched. Hillman, arXiv:1608.01407, Section 15,
  uses it: "An injective endomorphism of a PD₃-group must have image of finite index, by Strebel's
  theorem."
- **(I7) Bieri–Strebel, Theorem A.** If `G` is of type `FP_2` and `pi : G -> Z` is onto, then `G` is
  an HNN extension whose base is a finitely generated subgroup of `ker pi`, with stable letter
  mapped to a generator. When `G` has no nonabelian free subgroup, Britton's lemma forces the
  extension to be ascending.
  - *What was read.* Degrijse's proof of Theorem B says only "Since G is of type FP2, i.e. almost
    finitely presented, it follows from [7, Theorem A] that G can be realised as an HNN-extension",
    followed by the Britton sentence. Here [7] is R. Bieri and R. Strebel, *Almost finitely presented
    soluble groups*, Comment. Math. Helv. 53 (1978).
  - *Recalled, not re-fetched.* The refinements (finitely generated base inside `ker pi`, stable
    letter mapping to a generator) for `FP_2` groups were not re-read. The repository node
    `bieri-strebel-splitting-over-kernel-of-map-to-z` states them for finitely presented groups, from
    Cornulier–de la Harpe.
  - Section 6.1, item 3 needs the `FP_2` form with these refinements. That is this artifact's
    weakest import.
- **(I8) Gildenhuys.** "every solvable group of cohomological dimension two is isomorphic to either a
  solvable Baumslag-Solitar group or a non-cyclic subgroup of the additive rationals". Quoted from
  Degrijse's text, citing D. Gildenhuys, Math. Z. 166 (1979), Theorem 5.
- **(I9) Tits alternative.** A finitely generated linear group over a field either contains a
  nonabelian free subgroup or is virtually solvable. Source: J. Tits, J. Algebra 20 (1972), not
  re-fetched. Only Corollary 2.3 uses it.

Standard facts, each proved here or classical:

- **(S1) Monotonicity and torsion.** If `H <= G` then `cd H <= cd G`, because a projective
  `ZG`-resolution of `Z` is a projective `ZH`-resolution (`ZG` is free over `ZH`). A nontrivial
  finite cyclic group `C` of order `q` has `H^{2k}(C; Z) = Z/q` for all `k >= 1`, so `cd C = ∞`.
  Hence groups of finite cd are torsion-free, and `cd G = 0` forces `G = 1`.
- **(S2) Top degree.** If `cd N = m < ∞` then `H^{m+1}(N; -) = 0`, so `H^m(N; -)` is right exact.
  Some module `M'` has `H^m(N; M') != 0`. Choosing a free module `F` onto `M'` gives
  `H^m(N; F) -> H^m(N; M')` onto, hence `H^m(N; F) != 0`.
- **(S3) Type FP and sums.** If `N` is of type FP, then `H^k(N; ⊕_i M_i) = ⊕_i H^k(N; M_i)` for
  all `k`. The reason: `Hom_{ZN}(P, ⊕ M_i) = ⊕ Hom_{ZN}(P, M_i)` for finitely generated `P`, and
  cohomology commutes with direct sums of cochain complexes. With (S2): if `N` is of type FP with
  `cd N = m`, then `H^m(N; ZN) != 0`.
- **(S4) LHS for `Z` quotients.** For `1 -> N -> G -> Z -> 1` and any `ZG`-module `M`, the
  Lyndon–Hochschild–Serre spectral sequence has only the columns `p = 0, 1`. It therefore gives exact
  sequences `0 -> H^1(Z; H^{k-1}(N; M)) -> H^k(G; M) -> H^0(Z; H^k(N; M)) -> 0`. In particular
  `cd G <= cd N + 1`.
- **(S5) Elementary amenable closure.** The class `EG` contains finite and abelian groups and is
  closed under subgroups, quotients, extensions and directed unions. Solvable and virtually solvable
  groups lie in `EG`.

## 1. The split: root ⇔ H1 ∧ H2

The two halves are:

- **H1.** If `G` is amenable with `cd G < ∞`, then `Z[G]` is a domain.
- **H2.** If `G` is amenable with `cd G < ∞` and `Z[G]` is a domain, then `G` is virtually solvable.

**Remark 1.0.** `Z[G]` is a domain if and only if `Q[G]` is. If `alpha beta = 0` in `Q[G]` with
`alpha, beta != 0`, choose positive integers `a, b` with `a alpha` and `b beta` in `Z[G]`. Then
`(a alpha)(b beta) = 0` in `Z[G]`. The converse holds because `Z[G]` is a unital subring of `Q[G]`.

**Lemma 1.1 (H1 and H2 give the root).** Let `G` be amenable with `cd G < ∞`. By H1, `Z[G]` is a
domain. By H2, `G` is virtually solvable. ∎

**Lemma 1.2 (Kaplansky over `Q` gives H1).** Let `G` have `cd G < ∞`. By (S1), `G` is
torsion-free. Kaplansky's conjecture for the field `Q` makes `Q[G]` a domain, and by Remark 1.0 so
is `Z[G]`. Amenability is not used. ∎

**Lemma 1.3 (the root gives both halves).**

- H2 is the root with an extra hypothesis.
- For H1, let `G` be amenable with `cd G < ∞`. The root makes `G` virtually solvable, hence
  elementary amenable (S5), and `G` is torsion-free (S1). So `C[G]` is a domain (I5), and therefore
  so is its subring `Z[G]`. ∎

So the root is equivalent to `H1 ∧ H2`. Only the direction of Lemma 1.1 is recorded as a route,
which keeps the graph acyclic.

**Dimension 2.** By (I2), (I4) and (S1), H2 holds for groups of cd at most 2 (Section 3). So in
dimension 2 the root is *equivalent* to H1: an amenable group of cd 2 is virtually solvable if and
only if its integral group ring is a domain. The "only if" direction is Lemma 1.3.

## 2. Reduction to finitely generated groups

**Proposition 2.1.** Let `cd G < ∞`. If every finitely generated subgroup of `G` is virtually
solvable, then `G` is virtually solvable.

*Proof.*

1. Each finitely generated subgroup is virtually solvable, so it lies in `EG` (S5).
2. `G` is the directed union of its finitely generated subgroups, so `G ∈ EG` (S5).
3. `G` is elementary amenable with `cd G < ∞`, so it is virtually solvable (I3). ∎

**Proposition 2.2.** Each of the root, H1 and H2 holds for all groups if and only if it holds for
all finitely generated groups.

*Proof.* The hypotheses pass to subgroups:

- subgroups of amenable groups are amenable;
- `cd` is monotone (S1);
- `Z[H]` is a unital subring of `Z[G]`, so it is a domain when `Z[G]` is.

For the root and H2, apply Proposition 2.1 to `G`, whose finitely generated subgroups satisfy the
hypotheses. For H1, a pair of zero divisors in `Z[G]` has finite supports, so it lies in `Z[H]` for
the finitely generated subgroup `H` generated by those supports. ∎

**Corollary 2.3 (linear case).** Let `G` be amenable with `cd G < ∞`, and suppose `G` embeds in
`GL_n(k)` for some field `k`. Then `G` is virtually solvable.

*Proof.*

1. Let `H` be a finitely generated subgroup of `G`. It is linear.
2. `H` is amenable, so it contains no nonabelian free subgroup (`F_2` is not amenable, and
   amenability passes to subgroups).
3. By the Tits alternative (I9), `H` is virtually solvable.
4. Proposition 2.1 finishes the proof. ∎

So every counterexample to the root (or to H2) is non-linear over every field. If a counterexample
exists, then a finitely generated one exists (Proposition 2.2). Section 7 records a second filter.

## 3. Dimension at most 2, and which steps of the proof are dimension-specific

**Proposition 3.1 (H2 for `cd <= 2`).** Let `G` be amenable with `cd G <= 2` and `Z[G]` a domain.
Then `G` is solvable, and `G` is one of: the trivial group, `Z`, a noncyclic subgroup of `Q`, or
`BS(1,m)` with `m != 0`.

*Proof.*

- **cd 0.** `G = 1` (S1).
- **cd 1.** `G` is free and nontrivial (I4). It is amenable, so it contains no `F_2`, hence
  `G ≅ Z`.
- **cd 2.** This is (I2). ∎

In the cd-1 case the domain hypothesis is automatic, since `Z[Z]` is a Laurent polynomial ring.

**Anatomy of Degrijse's proof of (I2).** The quotes below are from arXiv:1609.07635, proof of
Theorem B, read on 2026-09-16. Each step is followed by what happens in cohomological dimension 3.

- **Step B1 (finite type).**
  - Dimension 2: "First consider the case where G is finitely generated. In this case it follows
    from Theorem A that G is of type FP." Finite generation is `FP_1 = FP_{n-1}` for `n = 2`.
  - Dimension 3: (I1) needs `FP_2`, and a finitely generated group in H2 of cd 3 need not be
    `FP_2` (Section 6.1).
- **Step B2 (a map onto `Z`).**
  - Dimension 2: "Since amenable groups satisfy the Bass conjecture by [4], we conclude from
    [10, Section 4.1] that the ordinary Euler characteristic of G coincides with the L2-Euler
    characteristic." That characteristic vanishes, and with `cd G = 2` this gives `b_1(G) >= 1`.
    Degrijse's bibliography gives [4] as Berrick–Chatterji–Mislin and [10] as Eckmann (not
    re-fetched).
  - Dimension 3: `1 - b_1 + b_2 - b_3 = 0` does not force `b_1 > 0`. The Hantzsche–Wendt group
    (Section 6.2) is an example.
- **Step B3 (ascending HNN).**
  - Dimension 2: "Since G is of type FP2, i.e. almost finitely presented, it follows from [7,
    Theorem A] that G can be realised as an HNN-extension ... Since G is amenable, it does not
    contain non-abelian free subgroups. This forces the HNN-extension to be ascending, by Britton's
    Lemma."
  - Dimension 3: this step transfers verbatim, given `FP_2` and `b_1 > 0`.
- **Step B4 (the base has smaller dimension).**
  - Dimension 2: "assume by contradiction cd(K)=2. Since K must be one ended (since it does not
    contain non-abelian free subgroups) this implies that H^1(K,ℤ[G])=0. But by [9, Th. 0.1], the
    map α in the Mayer-Vietoris sequence H^1(K,ℤ[G]) → H^2(G,ℤ[G]) → H^2(K,ℤ[G]) →α H^2(K,ℤ[G])
    associated to the ascending HNN-extensions G=K∗_t is injective. We therefore conclude that
    H^2(G,ℤ[G])=0, contradicting the assumption that cd(G)=2." Here [9] is K. S. Brown and
    R. Geoghegan, *Cohomology with free coefficients of the fundamental group of a graph of groups*,
    Comment. Math. Helv. 60 (1985), 31–45. Theorem 0.1 there was not read.
  - Dimension 3: this is where the argument stops (Section 6.3).
- **Step B5 (classification).**
  - Dimension 2: `K` is free by Stallings (I4), and amenable, so `K = Z` and `G = BS(1,m)`.
  - Dimension 3: Hillman, arXiv:2102.02947, classifies the torsion-free elementary amenable groups
    of Hirsch length 3 and cd 3 (Section 8). Its statements were read only through ar5iv, and
    nothing here uses them.
- **Step B6 (arbitrary groups).**
  - Dimension 2: "every finitely generated subgroup of G either infinite cyclic or a solvable
    Baumslag-Solitar group ... G must be solvable", followed by (I8).
  - Dimension 3: Proposition 2.1 is the analogue in every dimension.

## 4. Dimension 3, fibred case

**Lemma 4.2.** Let `1 -> N -> G -> Z -> 1` be exact, with `N` of type FP and `cd N = m < ∞`. Then
`cd G = m + 1` and `H^{m+1}(G; ZG) != 0`.

*Proof.*

1. **Upper bound.** By (S4), `cd G <= m + 1`.
2. **Reduction to `H^1`.** Take `M = ZG` in (S4). Since `H^{m+1}(N; -) = 0`, the sequence gives
   `H^{m+1}(G; ZG) ≅ H^1(Z; W)`, where `W = H^m(N; ZG)` and `Z` acts through conjugation.
3. **Decomposing the coefficients.** Fix `t ∈ G` mapping to `1`.
   - As a left `ZN`-module, `ZG = ⊕_{j ∈ Z} Z[N t^j]`, and `Z[N t^j] ≅ ZN` via `x ↦ x t^{-j}`.
   - By (S3), `W = ⊕_j V_j` with `V_j = H^m(N; Z[N t^j]) ≅ H^m(N; ZN)`.
4. **How `t` acts.** On cochains, `t` acts by `f ↦ (n_1, …) ↦ t f(t^{-1} n_1 t, …)`.
   - Left multiplication by `t` carries `Z[N t^j]` onto `Z[N t^{j+1}]`, so `t` maps `V_j`
     isomorphically onto `V_{j+1}`.
   - The identification of (S3) is natural, so it respects this action.
   - Hence `W ≅ ⊕_j t^j V_0` is the induced `Z[t^{±1}]`-module.
5. **Computing `H^1(Z; W)`.** For the infinite cyclic group, `H^1(Z; W) = W / (t - 1) W`. Consider
   the map `σ : W -> V_0`, `Σ_j t^j v_j ↦ Σ_j v_j`, with `v_j ∈ V_0`.
   - `σ` is onto, and `σ((t - 1) W) = 0`.
   - Conversely, let `Σ_j v_j = 0`, with only finitely many `v_j` nonzero. Put
     `c_j = - Σ_{i <= j} v_i`. Then `c_j = 0` for `|j|` large, and
     `(t - 1) Σ_j t^j c_j = Σ_j t^j (c_{j-1} - c_j) = Σ_j t^j v_j`.
   - So `ker σ = (t - 1) W`, and `H^1(Z; W) ≅ V_0 ≅ H^m(N; ZN)`.
6. **Nonvanishing.** `H^m(N; ZN) != 0` by (S3), so `H^{m+1}(G; ZG) != 0` and `cd G = m + 1`. ∎

**Proposition 4.1 (H2 for fibred groups of cd 3).** Let `G` be amenable with `cd G = 3` and `Z[G]`
a domain. Suppose `π : G -> Z` is onto and `N = ker π` is of type `FP_2`. Then `N ≅ BS(1,m)` for
some `m != 0`, and `G` is solvable of derived length at most 3.

*Proof.* `N` is amenable, `Z[N]` is a domain, and `cd N <= 3` (S1). Consider the three cases.

- **cd N = 3.** `N` is of type `FP_2 = FP_{3-1}`, so (I1) makes it of type FP. Lemma 4.2 then
  gives `cd G = 4`, a contradiction.
- **cd N <= 1.** (S4) gives `cd G <= 2`, a contradiction.
- **cd N = 2.** By (I2), `N` is `BS(1,m)` or a noncyclic subgroup of `Q`. Finitely generated
  subgroups of `Q` are cyclic and `N` is finitely generated, so `N ≅ BS(1,m)` with `m != 0`.

`BS(1,m)` is metabelian and `G/N` is abelian, so `G` has derived length at most 3. ∎

**Remarks.**

- The hypothesis "`N` of type `FP_2`" is used only in the case `cd N = 3`, to reach (I1) and (S3).
- Suppose `N` is only finitely generated and `cd N = 3`. Then Lemma 4.2 is unavailable, and this
  subcase stays open. A non-FP kernel can have `cd(N ⋊ Z) = cd N`: take `N = Z[1/2]` inside
  `BS(1,2)`. That kernel is not finitely generated, though.
- Proposition 4.1 does not need `G` itself to be of finite type.

## 5. Dimension 3, Poincaré duality case

**Proposition 5.1.** Let `G` be an amenable `PD_3` group with `Z[G]` a domain. Suppose some
finite-index subgroup `G_0 <= G` has a normal subgroup `N` of infinite index with `G_0 / N`
elementary amenable. For example, `G_0` maps onto `Z`, which is the case whenever the virtual first
Betti number of `G` is positive. Then `G` is virtually solvable.

*Proof.*

1. `N` has infinite index in `G`, so `cd N <= 2` by Strebel (I6).
2. `N` is amenable and `Z[N]` is a domain, so `N` is solvable (Proposition 3.1, which covers groups
   that are not finitely generated).
3. `G_0` is solvable-by-elementary-amenable, so `G_0 ∈ EG` (S5).
4. The normal core of `G_0` in `G` has finite index and lies in `EG`, so `G ∈ EG` (S5).
5. `cd G = 3`, so `G` is virtually solvable by (I3). ∎

**Remarks.**

- Aspherical closed 3-manifold groups are already covered by geometrization. Proposition 5.1 is
  only new, if at all, for `PD_3` groups not known to be 3-manifold groups.
- Hillman's problem list, arXiv:1608.01407 (read via ar5iv on 2026-09-16), asks "Is G virtually
  representable onto ℤ?" (Q16) for `PD_3` groups `G`. A positive answer would reduce the amenable
  `PD_3` case of H2 to Proposition 5.1.
- Without the domain hypothesis, the same proof needs H1 only for subgroups of cd at most 2.

## 6. Where the dimension-2 argument stops in dimension 3

### 6.1 Step B1 fails: a finitely generated group of cd 3 in H2 that is not `FP_2`

Let `A = Z[1/6]`, and let `G = A ⋊ <t>` with `t a t^{-1} = (2/3) a`. Since `2/3` is a unit of `A`,
this is an automorphism.

1. **`G` is finitely generated.** The subgroup of `A` generated by the `t`-conjugates of `1` is the
   additive span of `(2/3)^k`, `k ∈ Z`, which is the ring `Z[2/3, 3/2]`. That ring contains
   `3/2 - 1 = 1/2` and `1 - 2/3 = 1/3`, so it equals `A`. Hence `G = <1, t>`.
2. **`G` is in H2.**
   - `G` is metabelian, hence amenable.
   - `G` is torsion-free, being an extension of torsion-free groups.
   - `G` is elementary amenable, so `C[G]` is a domain by (I5), and so is `Z[G]`.
3. **`G` is not of type `FP_2`.**
   - In `G`, `[t, a] = (2/3)a - a = -(1/3)a`. Since `3` is a unit of `A`, `[G,G] = A`, and
     `π : G -> Z` with kernel `A` is onto.
   - Suppose `G` were `FP_2`. By (I7), `G` is an ascending HNN extension with finitely generated
     base `K <= A` and stable letter `s = a_0 t` for some `a_0 ∈ A`.
   - `K != 1`, since otherwise `G ≅ Z`. `K` is a finitely generated subgroup of `Q`, so `K = cZ`
     for some `c != 0`.
   - `s` acts on `A` as multiplication by `2/3`. Ascending means `(2/3)^{±1} K ⊆ K` for one sign,
     so `(2/3)^{±1} ∈ Z`. That is false.
4. **`cd G = 3`.**
   - *Upper bound.* `A` is a countable directed union of infinite cyclic groups, so `cd A <= 2`.
     This is Berstein's bound for countable directed unions: standard, not re-fetched. Then
     `cd G <= 3` by (S4).
   - *Not cd 1 or less.* `G` is nonabelian and amenable, so it is not free (I4, S1).
   - *Not cd 2.* By (I2), `G` would be `BS(1,m)`, which is finitely presented, or abelian.
     Neither is possible, by item 3.

So in dimension 3, finite generation does not give the `FP_{n-1}` hypothesis of (I1). The group is
solvable, so this is not a counterexample to anything. It only shows that Step B1 does not
transfer.

### 6.2 Step B2 fails: vanishing Euler characteristic gives no map onto `Z`

Let `G` be the fundamental group of the Hantzsche–Wendt flat 3-manifold. It is a torsion-free
Bieberbach group, so it is `PD_3`, virtually `Z^3`, of type F, and it has domain group ring (I5).
Its first homology is finite (`Z/4 ⊕ Z/4`; standard, not re-fetched), so `b_1(G) = 0` while
`χ(G) = 0`. Hence in dimension 3 the Euler-characteristic step gives no map onto `Z`, even for
groups of type F. Passing to finite index can still produce one (here `Z^3`), and this is why
Proposition 5.1 asks only for a virtual map onto `Z`.

### 6.3 Step B4 fails: the ascending-HNN base

**Proposition 6.3.** Let `G` be amenable with `cd G = 3`, `Z[G]` a domain, `G` of type `FP_2`, and
`b_1(G) > 0`. Then `G` is an ascending HNN extension `K *_φ`, where `K` is finitely generated and
`φ : K -> K` is injective. If `cd K <= 2`, then `G` is solvable of derived length at most 3.

*Proof.*

1. By (I1), `G` is of type FP.
2. `b_1 > 0` gives a map `π` onto `Z`. By (I7), `G = <K, s | s k s^{-1} = φ(k)>` with `K`
   finitely generated inside `ker π`. After replacing `s` by `s^{-1}` if needed,
   `s K s^{-1} ⊆ K`.
3. `U = ∪_{j >= 0} s^{-j} K s^j` is an increasing union, since `s K s^{-1} ⊆ K`.
   - `s U s^{-1} = s K s^{-1} ∪ U = U` and `s^{-1} U s ⊆ U`.
   - Each term contains `K`, so `K` normalizes each term.
   - Since `G = <K, s>`, `U` is normal in `G`. Also `U <= ker π`, and `G / U` is generated by the image of `s`. Hence
   `U` is the normal closure of `K`, which is `ker π`.
4. If `cd K <= 2`, then `K ∈ {Z, BS(1,m)}` by Proposition 3.1 (`K != 1`, since `G` is not cyclic:
   `cd G = 3`). So `ker π` is an increasing union of metabelian groups, hence metabelian. Therefore
   `G` has derived length at most 3. ∎

**The remaining case is `cd K = 3`.** The Mayer–Vietoris sequence of the ascending HNN extension
(standard) reads

`H^2(K; ZG) -α-> H^2(K; ZG) -> H^3(G; ZG) -> H^3(K; ZG) -α-> H^3(K; ZG)`,

with `α = id - β`, where `β` is restriction to `s K s^{-1}` followed by conjugation by `s`. Since
`G` is FP with `cd 3`, `H^3(G; ZG) != 0` (S3). So `α` fails to be onto in degree 2, or fails to be
one-to-one in degree 3. In dimension 2, Degrijse removes the first possibility by one-endedness of
`K` (degree 1) and the second by Brown–Geoghegan. In dimension 3 two things are missing:

- **(G1)** Nothing forces `H^2(K; ZG) = 0`, or `α` onto in degree 2. One-endedness controls only
  degree 1.
- **(G2)** `K` is only finitely generated, not known to be `FP_2`. So neither (I1) nor (S3) applies
  to `K`, and this lane did not read whether Brown–Geoghegan Theorem 0.1 covers degree 3 for such
  `K`.

**A partial grading argument.** Suppose `K` is of type FP. Then
`ZG = ⊕_j Z[π^{-1}(j)]` is a sum of `ZK`-submodules, and (S3) gives
`H^m(K; ZG) = ⊕_j W_j`, where `W_j = H^m(K; Z[π^{-1}(j)])`. The map `β` raises `j` by one and the
identity preserves it.

- `α` is one-to-one: the lowest-degree component of `w` survives in `α(w)`.
- If `β` is one-to-one and `W != 0`, then `α` is not onto. An element concentrated in one degree is
  not in the image: compare the lowest and highest components of a preimage.

The MV sequence always gives `cd G <= m + 1`. So with `K` of type FP, `cd K = m`, and `β`
one-to-one in degree `m`, it gives
`coker(α) ↪ H^{m+1}(G; ZG)`, hence `H^{m+1}(G; ZG) != 0` and `cd G = m + 1`. (Here "raises `j` by
one" means one fixed direction; the other direction is symmetric.) This leaves:

**(Q-a)** For an ascending HNN extension `G = K *_φ` with `K` of type FP and `cd K = m`, is
`cd G = m + 1`? The grading argument settles it when `β` is injective in degree `m`, and it does
not settle it otherwise. In the situation of Proposition 6.3, a positive answer together with (G2)
(`K` of type `FP_2`) would exclude `cd K = 3`. Every amenable group of cd 3 of type `FP_2` with
`b_1 > 0` and domain group ring would then be solvable.

## 7. A filter on candidate counterexamples: micro-supported actions

The repository already has this for actions on the line (`finite-cd-groups-have-no-micro-supported-line-action`,
`finite-cd-line-groups-bound-disjointly-supported-families`). The same argument works on any
Hausdorff space. That version covers tree-boundary actions, which underlie several known families
of amenable groups that are not elementary amenable.

**Proposition 7.1.** Let a torsion-free group `G` act faithfully by homeomorphisms on a Hausdorff
space `X`. For open `U ⊆ X`, let `rist_G(U)` be the set of elements fixing `X ∖ U` pointwise.

- (a) If `U_1, …, U_k` are pairwise disjoint open sets with `rist_G(U_i) != 1` for each `i`, then
  `Z^k <= G`, so `k <= cd G`.
- (b) If `X` is nonempty with no isolated points and `rist_G(U) != 1` for every nonempty open `U`,
  then `cd G = ∞`.

*Proof.*

(a) Pick `1 != g_i ∈ rist_G(U_i)`.

1. Each `g_i` fixes `X ∖ U_i` pointwise and is a bijection, so `g_i(U_i) = U_i`.
2. For `i != j`, `g_j` fixes `U_i ⊆ X ∖ U_j` pointwise. So `g_i` and `g_j` commute: check the
   three regions `U_i`, `U_j` and the rest.
3. Suppose `∏ g_i^{n_i} = 1`. On `U_1` only `g_1^{n_1}` acts, so `g_1^{n_1}` is trivial on `U_1`,
   and it is trivial off `U_1` too. Faithfulness gives `g_1^{n_1} = 1`, and torsion-freeness gives
   `n_1 = 0`. The same holds for every `i`.
4. So `Z^k <= G`, and `k = cd Z^k <= cd G` (S1).

(b) Suppose `cd G < ∞`.

1. A nonempty open subset of `X` is infinite: a finite one would be discrete and open, hence made of
   isolated points.
2. So any nonempty open set contains two disjoint nonempty open subsets (Hausdorff). Iterating gives
   `k` pairwise disjoint nonempty open sets for every `k`.
3. Part (a) then gives `k <= cd G` for every `k`, a contradiction. (`G` is torsion-free by
   hypothesis; in (b) this also follows from (S1).) ∎

**Consequences.** These are standard facts, not re-fetched.

- Torsion-free weakly branch groups act micro-supportedly on the boundary of their rooted tree, a
  Cantor set, so they have infinite cd. The Basilica group is one: amenable, not subexponentially
  amenable, and not elementary amenable.
- Thompson's `F` acts micro-supportedly on `(0,1)`.
- Groups with torsion have infinite cd by (S1). This covers the Grigorchuk group and topological
  full groups of Cantor minimal systems.

So none of these families can be a counterexample to the root. Any counterexample is torsion-free
and not elementary amenable. It is not linear (Corollary 2.3). It has no faithful micro-supported
action on a Hausdorff space without isolated points. If one exists, a finitely generated one exists
(Proposition 2.2).

## 8. Literature checked, and status as of 2026-09-16

**Primary sources read.**

- **Degrijse, arXiv:1609.07635 (v1, 24 Sep 2016).**
  - Read from the arXiv HTML render on 2026-09-16: introduction, Theorems A and B, and the proof of
    Theorem B, including the bibliography entries [9] and [27].
  - Crossref metadata (2026-09-16): Math. Ann. 386 (2023) 1151–1162.
  - The published text was not read.
- **J. A. Hillman, *Elementary amenable groups of cohomological dimension 3*, arXiv:2102.02947**
  (v1 5 Feb 2021, v3 29 Jan 2022; journal reference J. Group Theory 27 (2024) 1–11).
  - Abstract read on arXiv on 2026-09-16.
  - The theorem statements were read through ar5iv on 2026-09-16, version not identified, and the
    quotes below come from that render.
  - Scope: the classification in the abstract is for Hirsch length 3. Corollary 9 reads "If G is a
    torsion-free elementary amenable group of Hirsch length 3 then c.d.G = 3 ⇔ G is constructible ⇔
    G is finitely presentable ⇔ G is one of the groups listed in Theorem 8 above."
  - This is consistent with Section 6.1, whose group has Hirsch length 2 and cd 3. Nothing here uses
    it: it is about groups already known to be elementary amenable.
- **J. A. Hillman, problem list on `PD_3` groups, arXiv:1608.01407.** Read via ar5iv on 2026-09-16.
  Questions Q16 and Q26, the Section 15 sentence quoted in (I6), and the Section 10 sentence "Since
  an elementary amenable group of finite cohomological dimension is virtually solvable, ...".
- **P. Kropholler, P. Linnell, W. Lück, *Groups of small homological dimension and the Atiyah
  Conjecture*, arXiv:math/0401312 (23 Jan 2004).** Abstract read on 2026-09-16. It contains "a
  finitely generated elementary amenable group G of cohomological dimension less or equal to 2
  possesses a finite 2-dimensional model for BG". This concerns elementary amenable groups only and
  is not used.
- **I. Emmanouil, K. Golfis, W. Ren, *Gorenstein dimensions and Hirsch length of groups*,
  arXiv:2608.22386 (v1 23 Aug 2026, v2 8 Sep 2026).** Abstract read on 2026-09-16. It concerns
  virtually soluble groups and elementary amenable groups of finite Hirsch length. In the abstract
  it neither answers nor mentions Kropholler's question.

**Cited from secondary quotation or memory, not re-fetched.**

- Strebel (I6), Stallings/Swan (I4), Bieri–Strebel (I7), Gildenhuys (I8), Tits (I9).
- Brown–Geoghegan Theorem 0.1.
- Berstein's bound for directed unions.
- Hantzsche–Wendt homology.
- The Basilica group and topological full groups.

**Status.**

- Web searches on 2026-09-16 found no claimed resolution of Kropholler's question, and no
  published proof of H2 in dimension 3. The query strings were not preserved. This lane's search
  budget ran out during the external gate.
- The root node's own record (2026-09-13) agrees.
- This is evidence of openness, not proof of it.

