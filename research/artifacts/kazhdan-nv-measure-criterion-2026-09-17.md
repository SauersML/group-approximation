# Kazhdan subgroups of nV: the measure criterion (2026-09-17)

Lane swarm-0917-w2-zar-pull-2, role transplanter, family entropy-measure.
Target hole: `kazhdan-subgroups-of-brin-thompson-groups-are-finite`.

Summary. For a subgroup `K <= nV` with property (T), the slope cocycle becomes a
measurable integer coboundary for every `K`-invariant probability measure, and
transporting deep bricks along the potential gives almost invariant vectors in
`l^2` of a genuine `K`-set of marked clopen pieces. Property (T) then forces every
invariant probability measure to live on the open set `U_K` of points having a
clopen neighbourhood fixed pointwise by a finite-index subgroup. Consequently:

- **Theorem.** `K` is finite iff `U_K = C^n` iff every nonempty closed
  `K`-invariant subset of `C^n` carries a `K`-invariant Borel probability measure.
- So the flagship hole is **equivalent** to the purely dynamical statement: every
  minimal closed invariant set of a Kazhdan subgroup of `nV` carries an invariant
  probability measure.

## 0. Notation and standard facts

- `C = {0,1}^ω`. For a finite word `v`, `[v] = vC`. A **brick** is
  `[v] = [v_1] x ... x [v_n] ⊆ C^n`, its **shape** is
  `|v| = (|v_1|,...,|v_n|) ∈ N^n`. A brick determines its words, hence its shape.
  Its **canonical chart** is `φ_[v]: C^n -> [v]`, `(x_1,...,x_n) -> (v_1x_1,...,v_nx_n)`.
- `g ∈ nV` is a homeomorphism of `C^n` admitting a finite partition into bricks
  `[w^(j)]` such that `g(w_1x_1,...,w_nx_n) = (w'_1x_1,...,w'_nx_n)` on each piece;
  that is, `g ∘ φ_[w] = φ_[w']`. Say `g` is **canonical on** a brick `B` if
  `g(B)` is a brick `B'` and `g ∘ φ_B = φ_B'`. Let `D_g` be the maximal
  coordinate of the shapes of such a partition.
- **Sub-bricks.** If `g` is canonical on `[w]` with image `[w']`, it is canonical on
  every sub-brick `[wu]`, with image `[w'u]`.
- **Deep bricks.** If a brick `B` has shape `k` with every `k_i >= D_g`, then `B`
  lies inside one piece of the partition (the piece containing a point of `B` has
  words that are prefixes of the words of `B`), so `g` is canonical on `B`.
- **Slope cocycle.** `s(g,x) = |w| - |w'| ∈ Z^n` for `x` in a brick `[w]` on which
  `g` is canonical with image `[w']`. It does not depend on the brick: on a common
  sub-brick both give the same image brick and the same difference of shapes.
  `s(g,·)` is locally constant, hence bounded. If `g` is canonical on `B ∋ x` of
  shape `k`, then `g(B)` is the brick of shape `k - s(g,x)` containing `gx`.
- **Cocycle identity** `s(gh,x) = s(g,hx) + s(h,x)`: take a brick `B ∋ x` so deep
  that `h` is canonical on `B` and `g` is canonical on `h(B)`; compose the charts.
- **Property (T)**, defining form (Bekka–de la Harpe–Valette, *Kazhdan's Property
  (T)*, Definition 1.1.3): there are a finite `Q ⊆ K` and `ε > 0` such that every
  unitary representation with a vector `ξ ≠ 0`, `max_{q∈Q} ||π(q)ξ - ξ|| < ε||ξ||`,
  has a nonzero invariant vector.
- **Delorme–Guichardet** (BdlHV Theorem 2.12.4, for countable discrete groups):
  property (T) is equivalent to property (FH), so for every orthogonal
  representation `π` of `K` on a real Hilbert space and every 1-cocycle `b`
  (`b(gh) = b(g) + π(g) b(h)`) there is `F` with `b(g) = π(g)F - F`. Standard, not
  re-read at source; this and the defining form of (T) are the only imports.

## 1. The integer potential

**Lemma 1.** Let `K <= nV` have (T), and let `ν` be a `K`-invariant Borel probability
measure on `C^n`. There is a Borel `F: C^n -> Z^n` with, for every `g ∈ K`,
`s(g,y) = F(y) - F(gy)` for `ν`-a.e. `y`.

*Proof.*
- `π(g)f = f ∘ g^{-1}` is an orthogonal representation of `K` on
  `H = L^2(C^n,ν; R^n)`, because `ν` is invariant.
- `b(g)(x) = s(g, g^{-1}x)` lies in `H` since `s(g,·)` is bounded. It is a cocycle:
  `b(gh)(x) = s(gh, h^{-1}g^{-1}x) = s(g, g^{-1}x) + s(h, h^{-1}(g^{-1}x)) = b(g)(x) + (π(g)b(h))(x)`.
- By Delorme–Guichardet, `b(g) = π(g)F_0 - F_0` for some `F_0 ∈ H`, that is
  `s(g, g^{-1}x) = F_0(g^{-1}x) - F_0(x)` a.e.; substituting `y = g^{-1}x` (the
  substitution preserves `ν`) gives `s(g,y) = F_0(y) - F_0(gy)` a.e.
- `K` is countable, so off one null set this holds for all `g`. Then
  `F_0(gy) - F_0(y) ∈ Z^n`, so `θ = F_0 mod Z^n: C^n -> T^n` satisfies
  `θ(gy) = θ(y)` a.e. Let `L: T^n -> [0,1)^n` be the Borel lift and
  `F = F_0 - L∘θ`. Then `F` is `Z^n`-valued a.e. (redefine it as `0` on the null
  set where not) and `F(y) - F(gy) = F_0(y) - F_0(gy) = s(g,y)` a.e. ∎

## 2. The marked-piece K-set

Let `Ω` be the set of pairs `(E, φ)` where `E ⊆ C^n` is clopen and `φ: C^n -> E` is a
homeomorphism. `nV`, hence `K`, acts on `Ω` by `g·(E,φ) = (gE, g∘φ)`; this is a group
action with no conditions.

- If `g` is canonical on a brick `B`, then `g·(B, φ_B) = (gB, φ_gB)`.
- The stabilizer of `(E,φ)` acts as the identity on `E`: `g∘φ = φ` and `φ` is onto `E`.
- Let `Ω_fin` be the union of the finite `K`-orbits and `Ω_inf = Ω \ Ω_fin`. Both are
  `K`-invariant, `l^2(Ω) = l^2(Ω_fin) ⊕ l^2(Ω_inf)` as representations, and
  `l^2(Ω_inf)` has no nonzero invariant vector (an invariant vector is constant on
  orbits and square summable, so zero on infinite orbits).
- Define `U_K = ∪{E : (E,φ) ∈ Ω_fin}`. It is open, and `K`-invariant because
  `g·(E,φ)` has the same finite orbit. Equivalently, `U_K` is the set of points
  having a clopen neighbourhood fixed pointwise by a finite-index subgroup of `K`:
  a finite orbit has a finite-index stabilizer that is trivial on `E`, and
  conversely if a finite-index `K_0` fixes `E` pointwise then `(E, φ)` is fixed by
  `K_0` for any chart `φ` of `E`, so its orbit is finite. `U_K` does not depend
  on any measure.

## 3. Invariant measures live on U_K

**Proposition 2.** Let `K <= nV` have (T). Every `K`-invariant Borel probability
measure `ν` on `C^n` satisfies `ν(U_K) = 1`.

*Proof.* Fix a Kazhdan pair `(Q, ε)` and the potential `F` of Lemma 1. Let
`D = max_{q∈Q} D_q`.

- For `c ∈ N` define `Ψ_c: C^n -> Ω ∪ {*}` by `Ψ_c(x) = (B, φ_B)`, where `B` is the
  brick of shape `k_c(x) = c·1 + F(x)` containing `x`, if every coordinate of
  `k_c(x)` is at least `D`; otherwise `Ψ_c(x) = *`. `Ψ_c` is Borel with countable
  range. `K` fixes `*`.
- **Equivariance on a good set.** Let `G_c` be the set of `x` such that for all
  `q ∈ Q`: `s(q,x) = F(x) - F(qx)`, `k_c(x) >= D` and `k_c(qx) >= D`
  coordinatewise. For `x ∈ G_c` and `q ∈ Q`, `q` is canonical on the brick `B` of
  shape `k_c(x)` containing `x`, and `qB` is the brick of shape
  `k_c(x) - s(q,x) = c·1 + F(qx)` containing `qx`. So `q·Ψ_c(x) = Ψ_c(qx) ∈ Ω`.
  Since `F` is finite a.e., `ν(C^n \ G_c) -> 0` as `c -> ∞`.
- **Almost invariant measures.** Let `m_c = (Ψ_c)_* ν` on the countable set
  `Ω ∪ {*}`. By invariance of `ν`, `q_* m_c` is the image of `ν` under
  `x -> q·Ψ_c(x)` and `m_c` is the image under `x -> Ψ_c(qx)`. These maps agree on
  `G_c`, so `||q_* m_c - m_c||_1 <= 2ν(C^n \ G_c)`, and the same bound holds for the
  restrictions to `Ω`, which is invariant.
- **Almost invariant vectors.** Put `ξ_c = (m_c|_Ω)^{1/2} ∈ l^2(Ω)`. Then
  `||ξ_c||^2 = m_c(Ω) >= ν(G_c) -> 1`, and by `(√a - √b)^2 <= |a - b|`,
  `||λ(q)ξ_c - ξ_c||^2 <= ||q_* m_c - m_c||_1 -> 0` for each `q ∈ Q`, where `λ` is
  the permutation representation (`λ(q)ξ_c = (q_* m_c)^{1/2}`).
- **(T).** Write `ξ_c = α_c + β_c` with `α_c ∈ l^2(Ω_fin)`, `β_c ∈ l^2(Ω_inf)`. The
  decomposition is invariant and orthogonal, so
  `||λ(q)β_c - β_c|| <= ||λ(q)ξ_c - ξ_c||`. `l^2(Ω_inf)` has no invariant vectors,
  so by the Kazhdan pair `max_q ||λ(q)β_c - β_c|| >= ε||β_c||`. Hence
  `||β_c|| -> 0`, i.e. `m_c(Ω_inf) -> 0` and `m_c(Ω_fin) -> 1`.
- **Conclusion.** `Ψ_c(x) ∈ Ω_fin` implies `x ∈ E ⊆ U_K` for the brick `E` of
  `Ψ_c(x)`. So `ν(U_K) >= m_c(Ω_fin) -> 1`. ∎

## 4. The criterion

**Theorem 3.** For `K <= nV` with property (T) the following are equivalent.
1. `K` is finite.
2. `U_K = C^n`.
3. Every nonempty closed `K`-invariant subset of `C^n` carries a `K`-invariant
   Borel probability measure.
4. Every minimal closed `K`-invariant subset of `C^n` carries a `K`-invariant Borel
   probability measure.

*Proof.*
- (1 ⇒ 2): the trivial subgroup has finite index and fixes `C^n` pointwise.
- (1 ⇒ 3): average the point masses over a finite orbit in the closed set.
- (3 ⇔ 4): every nonempty closed invariant set contains a minimal one (Zorn and
  compactness), and a measure on a subset is a measure on the set.
- (3 ⇒ 2): `Z = C^n \ U_K` is closed and invariant. If nonempty it carries an
  invariant probability measure `ν` with `ν(Z) = 1`, contradicting Proposition 2.
- (2 ⇒ 1): by compactness finitely many `E_1,...,E_r` with `(E_j, φ_j) ∈ Ω_fin` cover
  `C^n`. The intersection `K_0` of their stabilizers has finite index and is the
  identity on each `E_j`, so `K_0 = 1`. ∎

**Corollary 4 (shape of a counterexample).** If `K <= nV` is an infinite Kazhdan
subgroup, then `Z_K = C^n \ U_K` is a nonempty closed invariant set carrying no
`K`-invariant probability measure; no point of `Z_K` has a clopen neighbourhood fixed
pointwise by a finite-index subgroup; and every invariant probability measure of `K`
is carried by the open set `U_K`, on which `K` is locally virtually trivial.

## 5. What this does and does not give

- **Decomposition.** `kazhdan-subgroups-of-brin-thompson-groups-are-finite` is
  equivalent to `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures`.
  Neither direction needs anything beyond Theorem 3.
- **The remaining statement must use nV (remark, standard facts, not part of the
  established chain).** Abstract Kazhdan groups have minimal Cantor actions without
  invariant measures: `SL_3(Z[1/p])` is dense in `SL_3(Q_p)`, which acts transitively
  on the Cantor set `P^2(Q_p)`, so the lattice acts minimally; an invariant
  probability measure would be invariant under the closure `SL_3(Q_p)`, and
  Furstenberg's lemma rules that out for this non-compact simple group acting on
  projective space. So the open statement is not a fact about Kazhdan groups acting
  on Cantor sets; the slope cocycle and brick transport must enter again.
- **Ping-pong subgroups are no test.** Non-abelian free subgroups of `V` acting by
  ping-pong have measure-free minimal sets, so the hypothesis (T) is essential in the
  open statement too.
- **Generality.** The proof uses only: a countable group of homeomorphisms of a
  compact space, a `Z^n`-valued locally constant cocycle, and a countable family of
  clopen "bricks" indexed by a point and a shape vector that every element transports
  canonically once the shape is deep. It should therefore apply to subgroups of the
  Brin–Thompson–Higman groups built on products of `{0,...,d-1}^ω`; this lane did not
  write that version out.

## 6. Dead ends recorded by this lane

- **Twisted Koopman cocycle.** Using the quasi-invariant product measure `μ` (with
  Radon–Nikodym derivative `2^{Σ s}`) instead of an invariant `ν`, the half-density
  representation is unitary but `x -> s(g, g^{-1}x)` is not a cocycle for it: the
  identity picks up the factor `2^{Σ s/2}`. The Liouville-current version (a kernel on
  `C^n x C^n` à la Navas for V) needs `Π_i 1/μ_i(x_i ∧ y_i)`, which is not square
  integrable near the partial diagonals `{x_i = y_i}` for `n >= 2`: it dies at
  codimension-one coincidences, the same place commensurated subcubes die.
- **Shape-weighted bricks.** The family of canonical bricks with shapes in `[a,b]^n`,
  weighted by any function of the shape, is not almost invariant: an element with
  slope `s` changes the level mass by `2^{Σ s}`, so the boundary levels carry a fixed
  fraction of the mass. The potential `F` of Lemma 1 is exactly what repairs this, and
  it exists only in the presence of an invariant measure.
- **Skew product.** `C^n x Z^n` with `g(x,ℓ) = (gx, ℓ - s(g,x))` preserves
  `μ ⊗ 2^{Σℓ}` counting, but it is an infinite measure; producing almost invariant
  vectors from it requires a finite normalization, which again is an invariant
  measure on `C^n`.

## 7. Finiteness from a continuous potential (side lemma)

`K <= nV` is finite iff there is a locally constant `φ: C^n -> Z^n` with
`s(g,x) = φ(x) - φ(gx)` for all `g ∈ K`, `x`. (⇐) is the continuous version of
Section 3: the bricks of shape `c·1 + φ(x)` for large `c` form a finite partition
permuted canonically by `K`, and the kernel of the permutation action is trivial.
(⇒) for finite `K` take `c` beyond all depths; `B*(x) = ∩_{g∈K} g B_c(g^{-1}x)`
is a brick with `hB*(x) = B*(hx)` canonically, and its shape minus `c·1` is a
locally constant potential. Theorem 3 is the measurable, (T)-driven version.
