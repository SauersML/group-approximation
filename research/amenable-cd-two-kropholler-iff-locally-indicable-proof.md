---
rg: 2
id: amenable-cd-two-kropholler-iff-locally-indicable-proof
kind: route
title: The locally indicable Strong Atiyah theorem makes Q[G] a domain, the Z[G]-domain criterion makes G solvable, and a finitely generated subgroup without Z-quotient is all that can stop it
target: amenable-cd-two-kropholler-iff-locally-indicable
requires:
  - strong-atiyah-passes-to-locally-indicable-extensions
  - amenable-cd-two-solvable-iff-coherent-rational-group-algebra
  - amenable-left-orderable-groups-are-locally-indicable
  - amenable-edge-graphs-of-groups-preserve-division-ring-embeddings
  - amenable-cd-two-annihilator-iteration-closes-up
  - elementary-amenable-torsion-free-strong-atiyah
---

Notation as in the target. `U(G)` is the algebra of operators affiliated to `NG`. For a torsion-free
group `G` and a field `Q ⊆ K ⊆ C`, the *Strong Atiyah conjecture over `K`*, `SA_K(G)`, says:
for every matrix `A ∈ M_{m×n}(K[G])`, `dim_NG ker(r_A : ℓ²G^m → ℓ²G^n) ∈ Z`.

## Imports

- **(JL)** `strong-atiyah-passes-to-locally-indicable-extensions` (Jaikin-Zapirain–López-Álvarez,
  Math. Ann. 376 (2020), Proposition 6.5). If `G_1 ⊴ G_2` is torsion-free with `SA_K(G_1)`, and
  `G_2/G_1` is locally indicable, then `SA_K(G_2)`.
- **(ZD)** `amenable-cd-two-solvable-iff-coherent-rational-group-algebra`, item 3. If `G` is amenable with
  `cd_Z G <= 2`, then `G` is solvable iff `Z[G]` has no zero divisors. The solvable ones are `1`,
  `Z`, noncyclic subgroups of `Q`, and `BS(1,m)` with `m ≠ 0`.
- **(WM)** `amenable-left-orderable-groups-are-locally-indicable` (Witte Morris, AGT 6 (2006)). An
  amenable left-orderable group is LI. A finitely generated amenable group has a nontrivial
  orientation-preserving action on `R` iff it has an infinite cyclic quotient.
- **(BH)** Burns–Hale (Canad. Math. Bull. 15 (1972)): every LI group is left-orderable (recalled).
  A countable left-orderable group acts faithfully on `R` by orientation-preserving homeomorphisms
  (dynamical realisation; recalled).
- **(AE)** `amenable-edge-graphs-of-groups-preserve-division-ring-embeddings`. If `G` is the
  fundamental group of a graph of groups with amenable edge groups and every `Q[G_v]` embeds in a
  division ring, then `Q[G]` embeds in a division ring. Used only in item 5.
- **(T)** The tree alternative for amenable groups, and Serre's lemma that a finitely generated
  group of elliptic automorphisms of a tree fixes a vertex. Both are exactly as quoted in
  `amenable-cd-two-ea-radical-via-commensurated-cyclic-splitting`. Used only in item 5.
- **(SS)** Stallings–Swan: a group of `cd <= 1` is free.
- **(Ta)** Tamari: if `G` is amenable and `K[G]` is a domain, then `K[G]` is an Ore domain. It is
  used in the same form in `amenable-fp-iff-affiliated-top-homology-vanishes-proof` (J4).

## Lemma A (Strong Atiyah over Q forces a domain)

*If `G` is torsion-free and `SA_Q(G)` holds, then `Q[G]` is a domain.*

Let `a, b ∈ Q[G]` with `ab = 0` and `b ≠ 0`. Put `V = ker(r_a : ℓ²G → ℓ²G)`, where
`r_a(ξ) = ξa`. `V` is a closed left `G`-invariant subspace, and it contains `b`. Since `V ≠ 0`,
faithfulness of the von Neumann dimension gives `dim_NG V > 0`. `SA_Q(G)` applied to the `1×1`
matrix `(a)` says `dim_NG V ∈ Z ∩ (0,1]`, so `dim_NG V = 1`, and hence `V = ℓ²G`. Then
`a = r_a(δ_e) = 0`. So `Q[G]` has no nonzero right zero divisors. Applying the same argument to
the canonical involution `a ↦ a*`, which is an anti-automorphism, `Q[G]` has none on the left
either. ∎

## Lemma B (an amenable domain satisfies Strong Atiyah)

*If `G` is amenable and `Q[G]` is a domain, then `SA_Q(G)` holds.*

By (Ta), `S = Q[G] \ {0}` is an Ore set, and the Ore localisation `D = S⁻¹Q[G]` is a division ring.

- **Every `s ∈ S` is invertible in `U(G)`.** Item 1 of `amenable-cd-two-annihilator-iteration-closes-up`
  (valid for every amenable `G`, with no condition on `cd`) gives: `s` is not a zero divisor of
  `Q[G]`, so `rk(s) = 1`. Hence `r_s` is injective with dense image on `ℓ²G`, and so `s` is
  invertible in `U(G)` (Lück, *L²-invariants*, §8.2: a weak isomorphism is invertible in `U(G)`).
- **So `D ⊆ U(G)`,** by the universal property of Ore localisation.
- **Rank computation.** Let `A ∈ M_{m×n}(Q[G])`. Gaussian elimination over the division ring `D`
  gives invertible `X ∈ GL_m(D)` and `Y ∈ GL_n(D)` with `XAY = diag(1,…,1,0,…,0)`, with `r` ones.
  `X` and `Y` stay invertible over `U(G)`. So `dim_U(U(G)^m A) = r`, and
  `dim_NG ker r_A = m − r ∈ Z`. The equality `dim_NG ker r_A = m − dim_U(U^m A)` comes from Lück, §8.3 (the
  identification of `dim_NG` with `dim_U` and additivity). ∎

## Item 1

Let `G` be amenable and LI. LI groups are torsion-free: a nontrivial finite cyclic subgroup is
finitely generated and has no `Z`-quotient.

- **`SA_Q(G)`.** The trivial subgroup `1 ⊴ G` satisfies `SA_Q`, because a matrix over `Q` has
  integral kernel dimension. The quotient `G/1 = G` is LI, so (JL) gives `SA_Q(G)`.
- **Domain.** By Lemma A, `Q[G]` is a domain. By (Ta), `Q[G]` embeds in its Ore division ring,
  and by Lemma B's first two points that division ring lies inside `U(G)`.
- **Ranks.** Item 1 of `amenable-cd-two-annihilator-iteration-closes-up` then gives `rk(a) = 1`
  for every `a ≠ 0`.
- **Solvability.** If also `cd_Z G <= 2`, then `Z[G] ⊆ Q[G]` has no zero divisors, and (ZD)
  gives solvability together with the list. For finitely generated `G` of cd 2 this means
  `G ≅ BS(1,m)`. ∎

## Item 2

- **(a) ⇒ (b).** Let `G` be finitely generated amenable of cd 2. By (a) and (ZD), `G ≅ BS(1,m)`,
  which maps onto `Z`.
- **(b) ⇒ (c).** Let `G` be amenable with `cd_Z G <= 2`, and let `1 ≠ K ≤ G` be finitely
  generated. Then `cd K ∈ {1, 2}`.
  - If `cd K = 1`, then `K` is free by (SS) and amenable, so `K ≅ Z`.
  - If `cd K = 2`, then by (b) `K^{ab}` is an infinite finitely generated abelian group, so it has
    a `Z` quotient.
- **(c) ⇒ (a).** This is item 1.
- **(c) ⇒ (d).** By (BH).
- **(d) ⇒ (c).** By (WM).
- **(b) ⇔ (e).** This is the finitely generated form of (WM). ∎

For (a) the countable and uncountable cases need no separate treatment. Item 1 applies to amenable
groups of any cardinality.

## Item 3

Let `G` be amenable with `cd_Z G <= 2` and not solvable. Then `G` is torsion-free.

- **(ii).** Suppose `ab = 0` with `a, b ≠ 0`. Then `Q[H]` is not a domain. If `H` were LI, item 1
  would make `Q[H]` a domain. So `H` is not LI. Some nontrivial finitely generated `K ≤ H` has no
  `Z`-quotient, i.e. `K^{ab}` is finite.
  - `cd K = 1` is impossible, since then `K ≅ Z`.
  - So `cd K = 2`, and `K` is not `BS(1,m)` (which maps onto `Z`). By (ZD), `K` is not solvable,
    so `K` is a counterexample.
- **(i).** By (ZD), `Z[G]` has zero divisors, and hence so does `Q[G]`. Apply (ii).
- **(iii).** The facts about LI groups used here are standard and proved in one line each.
  - **Closure under subgroups.** Clear.
  - **Closure under products.** A nontrivial finitely generated subgroup of `∏ L_i` has a
    nontrivial coordinate projection. That projection is a nontrivial finitely generated
    subgroup of some `L_i`, so it maps onto `Z`.
  - **Closure under extensions.** Let `N ⊴ E` with `N` and `E/N` LI, and let `1 ≠ F ≤ E` be
    finitely generated. If `F ⊄ N`, then `FN/N` is a nontrivial finitely generated subgroup of
    `E/N`, so it maps onto `Z`. Otherwise `F ≤ N`, and `F` maps onto `Z` directly.

  Put `R(G) = ∩ { N ⊴ G : G/N LI }`. Then `G/R(G)` embeds in the product of the quotients `G/N`,
  so it is LI, and `R(G)` is the least such normal subgroup.
  - **`R(G)` is LI-perfect.** `R(R(G))` is characteristic in `R(G)`, hence normal in `G`. The
    group `G/R(R(G))` is an extension of the LI group `R(G)/R(R(G))` by the LI group `G/R(G)`, so
    it is LI. Minimality gives `R(G) ⊆ R(R(G))`, so `R(R(G)) = R(G)`.
  - **`Q[R(G)]` is not a domain.** Otherwise Lemma B gives `SA_Q(R(G))`. Then (JL), applied to
    `R(G) ⊴ G` with LI quotient, gives `SA_Q(G)`, and Lemma A makes `Q[G]` a domain. That
    contradicts (ZD).
  - **`R(G) ≠ 1`.** Otherwise `G` is LI and item 1 makes `G` solvable.
  - **`cd R(G) = 2`.** Suppose `cd R(G) <= 1`. Every finitely generated subgroup is free by (SS)
    and amenable, hence cyclic, so `R(G)` is torsion-free locally cyclic and LI. A nontrivial LI
    group is a nontrivial LI quotient of itself, contradicting LI-perfection.

  Applying (ii) inside `R(G)` gives a finitely generated counterexample `K ≤ R(G)` with finite
  abelianization. ∎

## Item 4

Let `X = { Γ ∈ C : Γ amenable ⇒ Γ elementary amenable }`. We show that `X` contains the free
groups and is closed under both operations. Then `X ⊇ C` by minimality of `C`.

- **Free groups.** An amenable free group has rank at most 1, so it is elementary amenable.
- **Directed unions.** Let `Γ = ∪ Γ_i` with `Γ_i ∈ X`, and let `Γ` be amenable. Each `Γ_i` is
  amenable, hence elementary amenable. The class of elementary amenable groups is closed under
  directed unions, so `Γ` is elementary amenable.
- **Extensions.** Let `N ⊴ Γ` with `N ∈ X` and `Γ/N` elementary amenable, and let `Γ` be amenable.
  Then `N` is amenable, hence elementary amenable. The class of elementary amenable groups is
  closed under extensions, so `Γ` is elementary amenable.

So amenable members of `C` are elementary amenable. Conversely, elementary amenable groups lie in
`C`: the trivial group is free, and `C` is closed under extensions by elementary amenable
quotients. For a finitely generated amenable group of cd 2, `Γ ∈ C` iff `Γ` is elementary
amenable, iff `Γ ≅ BS(1,m)` by (ZD) and `elementary-amenable-torsion-free-strong-atiyah`.

**Beyond EA.** The Grigorchuk–Machì group (Mat. Zametki 53 (1993)) is finitely generated, acts
faithfully on `R` (so it is left-orderable), and has intermediate growth. So it is amenable and not
elementary amenable (Chou: finitely generated elementary amenable groups have polynomial or
exponential growth). By (WM) it is LI. Hence the class of amenable LI groups is not contained in
the class of elementary amenable groups. This is recalled and not used in any proof. ∎

## Item 5

Let `K` be finitely generated with `H_1(K; Q) = 0`, acting on a tree `T` without inversions and
without a global fixed vertex. By (T), one of two cases holds.

**Case 1: `K` fixes an end `ω`.** The Busemann homomorphism `β : K → Z` vanishes, because `K^{ab}`
is finite. A hyperbolic element fixing `ω` has `ω` as an end of its axis, so `β ≠ 0` on it. Hence
every element is elliptic. By Serre's lemma `K` then fixes a vertex, a contradiction.

**Case 2: `K` preserves a pair of ends `{ω_1, ω_2}` and fixes neither.** `K` preserves the geodesic
line `ℓ` joining them and acts on `ℓ` through `Isom(ℓ) ≅ Z ⋊ Z/2`.

- **The image is infinite.** If it were finite, it would have order at most 2 on `ℓ`. It then
  fixes a vertex of `ℓ` or the midpoint of an edge. The latter is an inversion, which is excluded.
  So `K` fixes a vertex, a contradiction.
- **The image is dihedral.** An infinite subgroup of `Z ⋊ Z/2` is either infinite cyclic or
  infinite dihedral. `Z` is excluded because `H_1(K; Q) = 0`. So `K ↠ D_∞ = Z/2 * Z/2`.
- **The splitting.** Pulling back the free-product splitting of `D_∞` gives
  `K = A *_C B`. Here `C = ker(K → D_∞)`, and `A, B` are the preimages of the two factors, with
  `[A : C] = [B : C] = 2`.

If `K` is moreover an amenable counterexample, then `C` is amenable. If `Q[A]` and `Q[B]` were
domains, they would embed in their Ore division rings (Ta), and (AE) would embed `Q[K]` in a
division ring. But `K` is not solvable, so by (ZD) `Q[K]` is not a domain, a contradiction. So
`Q[A]` or `Q[B]` is not a domain. By item 3(ii), applied to the vertex group (amenable,
`cd <= 2`), it contains a finitely generated counterexample. ∎

## Calibrations

- **Hantzsche–Wendt group `P`.** `P = π_1` of the didicosm, the flat 3-manifold with
  `H_1 = Z/4 ⊕ Z/4`. It is torsion-free and virtually `Z³`, so elementary amenable, and
  `cd P = 3`.
  - It is not a unique-product group (Promislow 1988), so it is not left-orderable, and hence
    not LI.
  - It has finite abelianization, so the three-dimensional analogue of item 2(b) fails.
  - `Q[P]` is a domain (Kropholler–Linnell–Moody), so item 1's sufficient condition is not
    necessary in dimension 3.
  - In dimension 2 the list in (ZD) consists of LI groups. That is exactly why (a) ⇒ (c) holds.
- **Lamplighter.** `Z/2 ≀ Z` fails LI at its torsion. Item 1 correctly does not apply, and the
  group has thin idempotents.

## What was not proved

- (Q_ab) itself.
- Any statement that passes `SA_Q` through a finite-index overgroup. It is open in general
  whether `SA_Q(N)` for a torsion-free `G ⊇ N` of finite index implies `SA_Q(G)`. So "virtually
  LI" does not suffice for item 1 by this proof. This is the precise place a proof of (Q_ab)
  through virtual `b_1` would need a new input.
