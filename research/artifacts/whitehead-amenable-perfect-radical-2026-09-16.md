# Finite normal subgroups, amenable radicals and perfect radicals of Whitehead counterexamples (lane hi-spec-whitehead, 2026-09-16)

Status: unreviewed. Novelty unverified, see Section 8. All proofs are complete and
self-contained, apart from the imported graph claims named in the text and standard facts
about von Neumann algebras, covering spaces and cellular homology.

## 0. Results and what is new

Throughout, `κ` is the Kaplansky trace, `P(G)` is the perfect radical of a group `G` (its
largest perfect subgroup) and `r = b_1(K)`.

- **Theorem A (new as far as checked).** Let `K` be a finite connected 2-complex. If
  `π_1(K)` has a nontrivial finite normal subgroup, then `χ(K) >= 1`. Equivalently, a
  finitely presentable group with a nontrivial finite normal subgroup has deficiency at most
  0. The proof uses `κ` and the action of torsion on `π_2`.
- **Theorem B.** Let `K` be a finite connected 2-complex and `G = π_1(K)`.
  - If `χ(K) < 0`, no finite-index subgroup of `G` contains a nontrivial amenable normal
    subgroup.
  - If `χ(K) = 0` and some finite-index subgroup of `G` contains one, then `K` is aspherical.

  The infinite-subgroup half is Cheeger--Gromov plus the L²-Euler characteristic (compare
  Hillman, Theorems 2.4′ and 2.5′). The finite half is Theorem A.
- **Lemma H (Adams 1955, Howie 1979).** Let `X` be a connected 2-complex with `H_2(X) = 0` and
  `H_1(X)` torsion-free. Then the covering of `X` associated with `P(π_1 X)` is acyclic, and if
  `P(π_1 X) = 1` then `X` is aspherical. Only the statement is recalled from Rosebrock's
  survey; the proof in Section 6 is reconstructed here.
- **Theorem C (the Whitehead application).** Let `K` be a finite connected subcomplex of a
  contractible 2-complex, `G = π_1(K)` and `r = b_1(K)`.
  1. If `P(G)` is amenable, `K` is aspherical.
  2. If `r >= 1` and some finite-index subgroup of `G` contains a nontrivial amenable normal
     subgroup, `K` is aspherical.
  3. If `K` is not aspherical, then:
     - `G` is infinite;
     - `P(G)` is non-amenable;
     - `b_1^(2)(G) > r - 1`;
     - if `r >= 1`, every finite-index subgroup `H <= G` has trivial amenable radical, and
       so does `P(G)`.

**What is new relative to the graph and the sources read.**

- **Theorem A.** In the 2-complex setting it was not found in Hillman's book (arXiv:math/0212142v3,
  full-text search on 2026-09-16). The closest statement found is Hillman's Theorem 15.6, which
  excludes finite normal subgroups for strongly minimal PD₄-complexes by a different
  cohomological-periodicity argument. Theorem A adds non-L² information: see the
  `SL(2,5) × F_2` check in 4.4.
- **Theorem C.1** weakens the hypothesis `P(G) = 1` of Howie's 1979 theorem to "`P(G)` is
  amenable", in the finite-contractible setting that Whitehead's conjecture reduces to
  (Section 7.0). The genuinely new case is a nontrivial *finite* perfect radical, or more
  generally a finite normal subgroup, when `r >= 1`:
  - the r = 0 case is the graph's hyperlinear claim;
  - the infinite amenable case is routine L²;
  - the graph's one-cell claim `whitehead-one-cell-counterexamples-have-positive-first-l2-betti`
    excludes only *infinite* (normalish) amenable subgroups, and only for `r = 1` one-cell
    complements.
- **LOT groups (Corollary A.4).** They have no nontrivial finite normal subgroup, no
  nontrivial torsion element with finitely many conjugates, and no nontrivial finite subgroup
  whose normalizer has finite index. This is partial progress on `lot-groups-are-torsion-free`
  (OPEN), which quotes Barreto--Minian: "it is not even known whether all LOT groups are
  torsion-free."

## 1. Conventions

- Complexes are CW complexes. For a connected complex `K` with `G = π_1(K)`, the group `G` acts
  freely and cellularly on the left of the universal cover `K̃`.
- For a ring `R`, `C_i(K̃; R)` is a free left `R[G]`-module with one basis element for each
  `i`-cell of `K` (a chosen lift). When `K` is finite of dimension 2 with `c_i` cells of
  dimension `i`, `C_i(K̃;R) ≅ R[G]^{c_i}` and `χ(K) = c_0 - c_1 + c_2`.
- When `K` is 2-dimensional, `π_2(K) ≅ H_2(K̃; Z) = Z_2(K̃; Z)` by Hurewicz. This is a free
  abelian group, being a subgroup of the free abelian group `C_2(K̃;Z)`, and it is a left
  `Z[G]`-module. Its rationalization `M_Q := π_2(K) ⊗ Q = H_2(K̃; Q)` is a `Q[G]`-module, and
  `π_2(K) → M_Q` is injective.
- `τ : C[G] → C` is the coefficient of the identity, `τ(Σ a_g g) = a_1`. On matrices,
  `τ(M) = Σ_i τ(M_ii)`, so `τ(MN) = τ(NM)` for rectangular `M`, `N` of compatible sizes.
- A finitely generated projective left `Q[G]`-module `P` is isomorphic to `Q[G]^n ε` for an
  idempotent `ε ∈ M_n(Q[G])` acting by right multiplication on row vectors.
  - Its **Kaplansky rank** is `κ(P) := τ(ε)`.
  - `κ` is well defined. Padding with zeros, if `Q[G]^n ε ≅ Q[G]^n ε′`, the isomorphism and its
    inverse are right multiplication by matrices `α = εαε′` and `β = ε′βε` with `αβ = ε` and
    `βα = ε′`. So `τ(ε) = τ(αβ) = τ(βα) = τ(ε′)`.
  - `κ` is additive on direct sums (block-diagonal idempotents).
  - For an idempotent `a ∈ Q[G]`, `κ(Q[G]a) = τ(a)`. In particular `κ(Q[G]) = 1`.
- `P(G)` is the subgroup generated by all perfect subgroups of `G`.
  - It is perfect: each generator lies in some perfect `Q = [Q,Q] <= [P(G), P(G)]`.
  - It is characteristic, hence normal.
  - It equals the terminal term `G^(β)` of the transfinite derived series: `G^(0) = G`,
    `G^(α+1) = [G^(α), G^(α)]`, `G^(λ) = ∩_{α<λ} G^(α)`. Indeed a perfect `Q <= G^(α)`
    satisfies `Q = [Q,Q] <= G^(α+1)`, limits are intersections, and the series stops at a
    perfect term.
- The **amenable radical** `A(G)` is the largest amenable normal subgroup. It exists: two
  amenable normal subgroups generate an amenable normal subgroup, and directed unions of
  amenable groups are amenable.

## 2. Kaplansky positivity (standard; proof included)

**Lemma K.** Let `ε ∈ M_n(C[G])` be idempotent. Then `τ(ε)` is a real number `>= 0`, and
`τ(ε) = 0` only if `ε = 0`. Consequently a finitely generated projective `Q[G]`-module `P`
with `κ(P) = 0` is zero.

*Proof.*

- **Setup.** Let `N(G)` be the group von Neumann algebra: the weak closure of the left regular
  representation `λ` of `C[G]` on `ℓ²(G)`. The trace `τ(x) = ⟨x δ_1, δ_1⟩` is a faithful
  positive normal trace on `N(G)` extending the coefficient-of-identity trace. The same holds
  for `M_n(N(G))`, acting on `ℓ²(G)^n` with `τ(x) = Σ_i τ(x_ii)`. The map
  `λ : M_n(C[G]) → M_n(N(G))` is injective, since `λ(x)` applied to the vectors `δ_1 e_j`
  recovers the columns of `x`.
- **Range projection.** `E := λ(ε)` is a bounded idempotent. Its range `ker(1 - E)` is closed,
  and the orthogonal projection `p` onto it lies in `M_n(N(G))`, because the range is
  invariant under the commutant.
- **Similarity.** `Ep = p`, because `E` is the identity on its range, and `pE = E`. Put
  `x := E - p`. Then `xp = Ep - p = 0` and `px = pE - p = x`, so `x² = (xp)x = 0`. Hence
  `(1-x)(1+x) = 1` and
  `(1-x) p (1+x) = p + px - xp - xpx = p + x = E`.
- **Conclusion.** By the trace property, `τ(E) = τ(p (1+x)(1-x)) = τ(p) = τ(p*p) >= 0`. If
  `τ(E) = 0`, faithfulness gives `p = 0`, so `x = px = 0` and `E = 0`, hence `ε = 0`.
- **Modules.** Apply this to an idempotent representing `P`. `∎`

(Kaplansky's theorem, with Montgomery's refinement `0 < τ(ε) < 1` for `ε ≠ 0, 1`; recalled,
not re-read. The similarity trick above is the usual proof.)

## 3. Torsion acts nontrivially on `π_2`

**Lemma T.** Let `K` be a connected 2-dimensional CW complex, `G = π_1(K)`, and `g ∈ G` of
finite order `k >= 2`. Then there is `S ∈ π_2(K) = Z_2(K̃; Z)` with `gS ≠ S`.

*Proof.*

- **Free `Z[C]`-modules.** Let `C = ⟨g⟩ ≅ Z/k`, `N := 1 + g + ... + g^{k-1}` and
  `ε : C_0(K̃;Z) → Z` the augmentation (sum of coefficients). Each `C_i(K̃;Z)` is a free
  `Z[C]`-module, since `C` acts freely on cells. On a free `Z[C]`-module `F`:
  - (F1) `ker(1 - g) = N F`;
  - (F2) `ker N = (1 - g) F`;
  - (F3) `F` is torsion-free.

  It suffices to check this on `F = Z[C]`. For `a = Σ_{i<k} a_i g^i`, `(1-g)a = 0` iff all
  `a_i` are equal iff `a = a_0 N`. Also `Na = (Σ a_i) N`, so `Na = 0` iff `Σ a_i = 0` iff
  `a = Σ_{i>=1} a_i (g^i - 1) ∈ (1-g) Z[C]`.
- **A 2-cycle.** Let `x̃` be a 0-cell of `K̃`. Since `K̃` is connected there is a 1-chain `γ`
  with `∂γ = g x̃ - x̃`. Then `∂(Nγ) = N(g-1)x̃ = (g^k - 1)x̃ = 0`. Since `H_1(K̃;Z) = 0`, there
  is a 2-chain `c` with `∂c = Nγ`. Put `S := (1 - g)c`. Then `∂S = (1-g)Nγ = (1 - g^k)γ = 0`,
  so `S ∈ Z_2(K̃;Z)`.
- **Suppose `gS = S`.** Then `(1-g)² c = 0`, so `(1-g)c = N d` for some `d` by (F1). Applying
  `N` gives `0 = N(1-g)c = N² d = k N d`, so `Nd = 0` by (F3) and `(1-g)c = 0`. By (F1)
  again, `c = N c′`. Then `N(γ - ∂c′) = Nγ - ∂c = 0`, so by (F2) `γ = ∂c′ + (1-g)δ` for a
  1-chain `δ`.
- **Contradiction.** Applying `∂`, `g x̃ - x̃ = (1-g)∂δ`, i.e. `(1-g)(∂δ + x̃) = 0`. By (F1)
  `∂δ + x̃ = N y` for a 0-chain `y`. Apply `ε`: `ε(∂δ) = 0` and `ε(x̃) = 1`, so
  `1 = ε(Ny) = k ε(y)`. This is impossible since `k >= 2`. `∎`

*Remarks.*

- The special case where `c` is a single relator cell is the remark recalled in Rosebrock's
  survey (p. 445, as quoted in `lot-groups-are-torsion-free`): `(1-g)[r] ≠ 0` in `π_2(K)`.
- Equivalently, by dimension shifting in Tate cohomology: if `C` acted trivially on `π_2`, the
  exact sequence `0 → π_2 → C_2 → C_1 → C_0 → Z → 0` of `Z[C]`-modules, with `C_i` free, would
  give `Z/k = Ĥ^0(C; Z) ≅ Ĥ^3(C; π_2) ≅ ⊕ Ĥ^1(C; Z) = 0`. Tate cohomology of a finite
  group commutes with direct sums and vanishes on free modules.

