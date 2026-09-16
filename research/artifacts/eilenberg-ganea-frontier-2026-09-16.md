# Eilenberg--Ganea frontier: small-fiber images of the Poincaré spine (swarm lane hi-fron, 2026-09-16)

Lane `hi-fron-eilenberg-ganea-conjecture`, angle FRONTIER. The hole worked was
`bestvina-brady-epsilon-map-conjecture`. It was locked for this lane.

**Result in one paragraph.**
- Sections 2--3 prove two lemmas in full:
  - a coarse-lifting lemma for ε-maps (Lemma 1);
  - a Kervaire--Laudenbach consequence for subcomplexes of contractible 2-complexes
    (Proposition Q). It strengthens `acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear`.
- Section 4 isolates the statement NE (`spine-epsilon-images-avoid-contractible-2-complexes`).
  - It is the exact geometric input the Bestvina--Brady argument needs.
  - It is implied both by the ε-map conjecture (with the acyclic-subcomplex theorem) and by
    Whitehead's conjecture, and it implies geometric dimension 3 for `H_L`.
  - Sections 5--6 prove the partial results and record where every attack dies.

## 1. Frontier map and literature gate

**Graph beneath the root (landed head, 2026-09-16).**
- `eilenberg-ganea-conjecture` has no direct route.
- Its only live refutation path is `bestvina-brady-poincare-kernel-has-geometric-dimension-three`.
- That claim has one route, `epsilon-map-conjecture-gives-poincare-kernel-gd-three`. Its only
  OPEN requirement is `bestvina-brady-epsilon-map-conjecture`.
- The other two requirements are ESTABLISHED:
  - `acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear` (claim A);
  - `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`.
- The complementary side is `bb-kernel-gd-two-if-l-lies-in-contractible-2-complex` (claim C,
  ESTABLISHED). It gives geometric dimension 2 whenever `L` is a subcomplex of a contractible
  2-complex.
- So the ε-map conjecture is the highest-leverage hole. It is a statement about maps out of one
  fixed finite 2-complex, and it is the whole remaining input of the only refutation path.

**External gate (dated sources).** The searches were done 2026-09-16. The web search budget ran
out during the gate, and the arXiv API then returned HTTP 429. Only the sources below were
consulted.

| Source | Status here | What it gives |
|---|---|---|
| Bestvina--Brady, Invent. Math. 129 (1997) 445--470 | pinned earlier on main (hl-whitehead artifact) | Theorem 8.7, the shadow construction, the Remark on p. 470 |
| T. T. Nguyên-Phan, arXiv:1907.12063v1 (2019) | pinned earlier on main (ε-map node) | "it remains open"; the relative form fails in dimension 1 |
| Nitsche--Thom, J. Group Theory 25 (2022), arXiv:1811.07737v2 | pinned on main (`kervaire-laudenbach-holds-for-hyperlinear`) | Theorems 1.2 and 1.3 |
| S. Gersten, *Asphericity for certain groups of cohomological dimension 2*, arXiv:1501.06875v3 | abstract only, via web tool (as on main) | a finite subcomplex of an aspherical 2-complex is aspherical iff cd π_1 ≤ 2 |
| A. Kar, N. Nikolov, *2D problems in groups*, arXiv:1801.04484 (Jan 2018) | abstract via web tool | deficiency stabilisation, Wall's D2 problem, relation gap; no statement on ε-maps or on `H_L` |
| I. J. Leary, arXiv:1512.06609v4 | abstract via web tool | uncountably many groups of type FP; cd versus gd not decided |
| *Groups acting on trees and the Eilenberg-Ganea problem for families*, arXiv:1911.03457; *On cohomological dimension of group homomorphisms*, arXiv:2302.09686; *Small value of cohomological dimension of group homomorphisms*, arXiv:2509.14615 | titles from search results only, bodies **unread** | the titles concern the families version and dimension of homomorphisms, not the classical conjecture for `H_L` |
| E. Pasku, arXiv:2107.12293 | abstract only, **unverified**, unrefereed | claims the one-cell case of Whitehead; not used |
| J. Howie, Math. Proc. Cambridge Philos. Soc. 127 (1999) 487--493 | abstract only | plus-construction reading of Theorem 8.7 |
| A. J. Berrick, J. A. Hillman (2019) | title only, content **unverified** | not used |

**Gate verdict.** No source dated 2023--2026 among those seen settles the Eilenberg--Ganea
conjecture, the ε-map conjecture, or the geometric dimension of `H_L`. This is a spot check,
cut short by the rate limit. It is not a literature review.

## 2. Lemma 1: coarse lifting of ε-maps

**Setting.**
- `L` is a finite simplicial complex, and `d` is a metric on `|L|` inducing its topology. The
  standard choice is the path metric in which each simplex is a regular Euclidean simplex of
  side 1.
- For a vertex `w`, `st(w)` is the open star: the union of the open simplices that have `w` as a
  vertex. A point `x` lies in `st(w)` iff `w` is a vertex of the carrier `supp(x)`, the unique
  simplex containing `x` in its interior.
- `δ > 0` is a Lebesgue number of the open cover `{st(w)}`.

**Lemma 1.** Let `K` be a finite simplicial complex and `g: |L| → |K|` a continuous surjection
whose point preimages all have diameter `< ε`, with `ε ≤ δ`. Then there are an iterated
barycentric subdivision `K'` of `K` and a simplicial map `λ: K' → L` with `λ ∘ g ≃ id_L`.
Consequently:
- `g_*: π_n(L) → π_n(K)` is injective for all `n`;
- `λ_*: π_1(K) → π_1(L)` is surjective;
- `π_1(L)` is a retract of `π_1(K)` up to the conjugation induced by the free homotopy.

This is the construction in the proof of Bestvina--Brady Theorem 8.7. There the extension over
skeleta runs inside contractible stars. Here it is made simplicial, so that no extension step
is needed.

**Proof.**

(a) *Controlled neighbourhoods.*
- For `y ∈ |K|`, the fiber `F_y = g^{-1}(y)` is compact and nonempty, with `diam F_y < ε`.
- Put `η_y = (ε − diam F_y)/3` and `U_y = {x : d(x, F_y) < η_y}`. Then
  `diam U_y ≤ diam F_y + 2η_y < ε`.
- `g` is a closed map, from compact to Hausdorff. So `g(|L| − U_y)` is closed and misses `y`.
- Hence `V_y = |K| − g(|L| − U_y)` is an open neighbourhood of `y` with `g^{-1}(V_y) ⊆ U_y`.

(b) *Choice of λ on vertices.*
- Let `μ` be a Lebesgue number of the open cover `{V_y}` of the compact metric space `|K|`.
- The mesh of iterated barycentric subdivisions tends to 0. So choose `K'` in which every closed
  vertex star `St(u)` has diameter `< μ`.
- Then `St(u) ⊆ V_y` for some `y`. So `g^{-1}(St(u))` has diameter `< ε ≤ δ`, and it is nonempty
  since `g` is surjective.
- It therefore lies in some open star `st(w)`. Choose one such `w` and put `λ(u) = w`.

(c) *λ is simplicial.*
- Let `τ = [u_0, ..., u_k]` be a simplex of `K'`, `y` a point of its interior, and `x ∈ F_y`
  any point.
- `y ∈ St(u_i)` for every `i`, so `x ∈ st(λ(u_i))` for every `i`.
- So every `λ(u_i)` is a vertex of `supp(x)`. Together they span a face of `supp(x)`, which is a
  simplex of `L`.
- Hence `λ` extends linearly over `τ`.

(d) *Straight-line homotopy.*
- Let `x ∈ |L|` and `y = g(x)`, with `y` in the interior of `τ`.
- `λ(y)` is a convex combination of the `λ(u_i)`. By (c), applied to this `x ∈ F_y`, these are
  vertices of `supp(x)`. So `λ g (x) ∈ supp(x)`.
- If `x` lies in a closed simplex `σ` of `L`, then `supp(x) ⊆ σ`. So `x` and `λ g(x)` both lie in
  `σ`, and `H(x, s) = (1 − s) x + s λ g(x)`, computed affinely in `σ`, is continuous on `σ × I`.
- These formulas agree on common faces, so `H` is a homotopy `id_L ≃ λ ∘ g`.

(e) *Consequences.*
- A free homotopy `id ≃ λg` makes `λ_* g_*` an isomorphism on every `π_n`, after the change of
  basepoint along the track of the base point.
- So `g_*` is injective and `λ_*` is surjective. ∎

**Remarks.**
- Only continuity and surjectivity of `g` are used. The PL hypothesis in the ε-map conjecture is
  not needed here.
- If `K` is a subcomplex of a simplicial complex `Y`, iterated barycentric subdivision of `Y`
  restricts to that of `K`. So `K'` can be taken to be a subcomplex of a subdivision `Y'` of `Y`.

## 3. Proposition Q: kernels that die in H_1-injective enlargements

**Proposition Q** (claim `subcomplex-pi1-kernels-vanish-in-hyperlinear-quotients`).
Let `Y` be a contractible 2-dimensional CW complex, and let `K ⊆ Z ⊆ Y` be finite connected
subcomplexes such that `H_1(K; Z) → H_1(Z; Z)` is injective. Put
`N = ker(π_1(K) → π_1(Z))`.
- (a) Every homomorphism `ρ: π_1(K) → Q` to a hyperlinear group satisfies `ρ(N) = 1`.
- (b) If `H_1(K; Z) = 0`, every homomorphism from `π_1(K)` to a hyperlinear group is trivial. In
  particular `π_1(K)` has no nontrivial finite quotient.

Taking `ρ = id` in (b) recovers `acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear`.

**Proof of (a).** The steps follow `acyclic-subcomplex-pi1-nonhyperlinear-proof`, with two
changes: `H_1(K)` need not vanish, and the words are pushed along `ρ`.

*Step 1: relative H_2 vanishes.*
- `C_2(Z) ⊆ C_2(Y)` with the same boundary map, and there are no 3-cells. So
  `H_2(Z) = Z_2(Z) ⊆ Z_2(Y) = H_2(Y) = 0`.
- The pair sequence `0 = H_2(Z) → H_2(Z, K) → H_1(K) → H_1(Z)` gives
  `H_2(Z, K) ≅ ker(H_1(K) → H_1(Z)) = 0`.

*Step 2: normal form.*
- As in Step 3 of the cited proof, collapse a forest of edges outside `K`. Each component of the
  forest meets `K` in exactly one vertex, and the forest contains every vertex of `Z` outside `K`.
- This is a homotopy equivalence rel `K` onto `Z'' = K ∪ (a 1-cells) ∪ (b 2-cells)`, with the new
  1-cells attached at vertices of `K`.
- `H_2(Z'', K) = 0`, and `N = ker(i: π_1(K) → π_1(Z''))`.
- Van Kampen gives `π_1(Z'') = (π_1(K) * F_a) / <<w_1, ..., w_b>>`, with `i` induced by the
  first factor.

*Step 3: the exponent-sum matrix is injective.*
- The relative cellular complex of `(Z'', K)` is `Z^b → Z^a → 0`. Its first map is the
  exponent-sum matrix `E` of `ε(w_1), ..., ε(w_b)`, where `ε: π_1(K) * F_a → F_a` kills `π_1(K)`.
- So `ker E = H_2(Z'', K) = 0`.
- The one-vertex presentation complex `P` of `<x_1, ..., x_a | ε(w_1), ..., ε(w_b)>` has cellular
  complex `Z^b → Z^a → Z`, with first map `E` and second map 0. So `H_2(P) = ker E = 0`.

*Step 4: push along ρ and apply Nitsche--Thom.*
- Put `w'_j = (ρ * id)(w_j) ∈ Q * F_a`. The augmentation killing `Q` sends `w'_j` to `ε(w_j)`,
  so the presentation complex of the pushed system is the same `P`.
- By `kervaire-laudenbach-holds-for-hyperlinear` (Nitsche--Thom, Theorem 1.2, with `G := Q`
  hyperlinear), the system `w'_1, ..., w'_b` is solvable in a group `H ⊇ Q`: there is
  `h ∈ H^a` with `w'_j(h) = 1` for all `j`.
- Define `Φ: π_1(K) * F_a → H` by `ρ` (followed by `ι: Q ⊆ H`) on `π_1(K)` and `x_i ↦ h_i`.
  Then `Φ(w_j) = w'_j(h) = 1`. So `Φ` factors as `Φ̄: π_1(Z'') → H` with `Φ̄ ∘ i = ι ∘ ρ`.
- For `n ∈ N`: `ι(ρ(n)) = Φ̄(i(n)) = 1`, and `ι` is injective. So `ρ(n) = 1`.

*Degenerate cases.* If `b = 0` then `i` is injective and `N = 1`. If `a = 0` then `ker E = Z^b`
forces `b = 0`. ∎

**Proof of (b).**
- By Step 1 of `acyclic-subcomplex-pi1-nonhyperlinear-proof`, there is a finite connected
  subcomplex `Z ⊆ Y` containing `K` with `π_1(K) → π_1(Z)` trivial. The null-homotopies of the
  finitely many generator loops are compact and meet `K`.
- `H_1(K) = 0`, so the injectivity hypothesis holds vacuously, and `N = π_1(K)`.
- By (a), `ρ = 1`.
- Finite groups are hyperlinear, by the left regular representation, as recorded in the cited
  proof. So there is no nontrivial finite quotient. ∎

**Remarks (recalled standard facts, not pinned).**
- Amenable groups and residually finite groups are sofic, and sofic groups are hyperlinear (the
  last is in the Nitsche--Thom sentence quoted on main).
- A finitely generated subgroup of `GL_n(C)` is residually finite (Mal'cev).
- So in case (b), a nontrivial `π_1(K)` has no nontrivial amenable quotient and no nontrivial
  homomorphism to any `GL_n(C)`. These remarks are not part of the claim node.

**Variant through Nitsche--Thom Theorem 1.3 (not in the claim).**
- Theorem 1.3 is quoted verbatim on main: the conclusion holds when the presentation complex
  `P` admits a covering with trivial second homology.
- `P` is homotopy equivalent to `Z'' / K ≃ Z / K`. Hence (a) also holds when `Z / K` admits a
  covering with trivial `H_2`, without assuming that `H_1(K) → H_1(Z)` is injective.
- §6.1 shows this variant never applies to the enlargements that matter.

## 4. The statement NE and its position

Throughout, `L` is a flag triangulation of a spine of the Poincaré homology sphere, with the unit
path metric of §2. `L` is acyclic, and `π_1(L) = I* = SL(2,5)` has order 120.

**NE** (claim `spine-epsilon-images-avoid-contractible-2-complexes`). There is `ε > 0` such that
no contractible 2-dimensional simplicial complex `Y` contains a finite subcomplex `K` that is the
image of a surjective PL map `g: |L| → |K|` whose point preimages all have diameter `< ε`.

**TF** (claim `contractible-2-complex-subcomplexes-have-torsion-free-pi1`). Every finite
connected subcomplex of a contractible 2-dimensional CW complex has torsion-free fundamental
group.

**Implications proved here (routes).**

```
whitehead-asphericity-conjecture ──► TF ──► NE ──► gd(H_L) = 3 ──► Eilenberg--Ganea fails
bestvina-brady-epsilon-map-conjecture + claim A ──► NE
```

So NE is a common weakening of the ε-map conjecture and of Whitehead's conjecture, and it is
exactly the geometric input the Bestvina--Brady argument needs. The identity `L → L` is an ε-map
for every ε, so NE contains the statement "L is not a subcomplex of a contractible 2-complex".
That statement follows from claim A. NE asks for the same conclusion for all small-fiber
perturbations of `L`.

### 4.1 Route `spine-epsilon-images-avoiding-2-complexes-give-gd-three` (NE ⇒ gd 3)

Requires NE and `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`.

1. *Bounds.* By item 1 of the dichotomy claim, `cd H_L = 2`. `X / H_L` is a 3-dimensional
   `K(H_L, 1)`. So `gd H_L ∈ {2, 3}`. Suppose `gd H_L = 2`.
2. *Simplicial model (recalled standard, not pinned).*
   - Let `W` be a 2-dimensional CW `K(H_L, 1)`.
   - Homotope the attaching maps of its 2-cells to edge-path loops in a subdivided 1-skeleton,
     by cellular and simplicial approximation. The result is a homotopy-equivalent complex with
     polygonal 2-cells.
   - Coning each polygon from an interior point gives a Δ-complex, and its second barycentric
     subdivision is a simplicial complex.
   - Its universal cover `Y` is a contractible simplicial 2-complex with a free simplicial
     `H_L`-action.
3. *Shadows.* As in the proof of Bestvina--Brady Theorem 8.7, take an `H_L`-equivariant PL map
   `φ: X_t → Y`, a vertex `v` with `s = |f(v) − t|`, and `g_v = φ ∘ σ: |L| → K_v = φ(S_(v,L))`.
   - *Uniform fiber bound.* Let `F ⊆ X_t` be a compact set whose translates cover `X_t`. The
     `H_L`-action on `Y` is a covering-space (deck) action, hence properly discontinuous with
     Hausdorff quotient, and `φ(F)` is compact. So `T = {h : hφ(F) ∩ φ(F) ≠ ∅}` is finite. If `y ∈ h_0 φ(F)`, then
     `φ^{-1}(y) ⊆ h_0 T F`. Hence `φ^{-1}(y)` has `X_t`-diameter at most `D = diam(TF)`, for
     every `y`.
     This justifies Bestvina--Brady's sentence "point preimages of φ will have diameters bounded".
   - *Rescaling.* `σ` is a quasi-isometry with constants `λ, c` independent of `s` (the
     observation after Definition 8.8, quoted in `epsilon-map-conjecture-gives-poincare-kernel-gd-three`).
     So fibers of `g_v` have unit-metric diameter at most `(λD + c)/s`.
4. *Contradiction.*
   - Take `s > (λD + c)/ε`. Then `g_v` is a surjective PL map with fibers of diameter `< ε`.
   - The image `K_v` is a compact subpolyhedron of `Y`. After a subdivision of `Y`, not
     necessarily equivariant, `K_v` is a finite connected subcomplex of the contractible
     simplicial 2-complex `Y'`, and `g_v` is still PL.
   - This contradicts NE. So `gd H_L = 3`. ∎

### 4.2 Route `epsilon-map-conjecture-gives-spine-images-avoid-2-complexes` (ε-conjecture + A ⇒ NE)

Requires `bestvina-brady-epsilon-map-conjecture` and
`acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear`.

- Let `ε_0` be given by the conjecture for the unit metric. Suppose `g: |L| → |K|` is a surjective
  PL `ε_0`-map onto a finite subcomplex `K` of a contractible simplicial 2-complex `Y`.
- *Weak form (E).* The conjecture gives `K ≃ M = L ∪ (1-cells) ∪ (2-cells)`. Choose a cellular
  homotopy equivalence `h: K → M`.
- *Transport.*
  - Let `Z = M ∪_h Y` be the pushout.
  - `K ⊆ Y` is a cofibration and `h` a homotopy equivalence. By the gluing theorem for adjunction
    spaces (recalled standard), `Y → Z` is a homotopy equivalence, so `Z` is contractible.
  - `Z` is a 2-dimensional CW complex with `M`, hence `L`, as a subcomplex.
- *Contradiction.* `L` is finite and acyclic, and `π_1(L) = I*` is finite, nontrivial and
  hyperlinear. This contradicts claim A. ∎

This is Steps 3--5 of `epsilon-map-conjecture-gives-poincare-kernel-gd-three`, made independent
of the shadows.

### 4.3 Route `contractible-2-complex-torsion-free-gives-spine-images-avoid` (TF ⇒ NE)

Requires TF only.
- Take `ε = δ`, the Lebesgue number of §2. Suppose `g: |L| → |K| ⊆ Y` is a surjective map with
  fibers of diameter `< δ`.
- By Lemma 1, `g_*: I* → π_1(K)` is injective.
- By TF, `π_1(K)` is torsion-free, but it contains the nontrivial finite group `g_*(I*)`. This is
  a contradiction. ∎

Neither PL nor simpliciality of `Y` is used.

### 4.4 Route `whitehead-conjecture-gives-torsion-free-subcomplex-pi1` (Whitehead ⇒ TF)

Requires `whitehead-asphericity-conjecture`.
- A contractible complex is aspherical. So Whitehead's conjecture makes every finite connected
  subcomplex `K` aspherical, and `K` is then a 2-dimensional `K(π_1(K), 1)`.
- Hence `cd π_1(K) ≤ 2`.
- A group of finite cohomological dimension is torsion-free (recalled standard):
  `H^n(Z/p; F_p) ≠ 0` for all `n`, and cd does not increase on subgroups. ∎

Bestvina--Brady's own proof of Theorem 8.7 uses `π_2` instead of torsion. Lemma 1 gives
`π_2(K) ⊇ π_2(L) ≠ 0`. The torsion form is recorded because TF is strictly weaker than
Whitehead's conjecture for finite subcomplexes of contractible complexes.

## 5. Consequences for small-fiber images and shadows

Let `Y` be a contractible 2-dimensional simplicial complex and `K ⊆ Y` a finite connected
subcomplex. Let `g: |L| → |K|` be a continuous surjection with fibers of diameter `< δ`, and
let `λ: K' → L` be given by Lemma 1, with `K' ⊆ Y'` iterated barycentric subdivisions. Write
`H_1(K) = Z^m`. It is free: `H_1(K) ≅ H_2(Y, K) = Z_2(Y, K)`, a subgroup of a free abelian group.

**5.1 Acyclic images are excluded (proved).** If `m = 0`, then `λ_*: π_1(K) → I*` is a surjection
onto a nontrivial finite group. This contradicts Proposition Q(b). So NE holds for all acyclic
images, with `ε = δ`.

**5.2 General images (proved).** For every finite connected `Z` with `K ⊆ Z ⊆ Y` and
`H_1(K) → H_1(Z)` injective, `ker(π_1(K) → π_1(Z)) ⊆ ker λ_*`. This is Q(a) with `ρ = λ_*`.
- Take `β ∈ π_1(L)` nontrivial. Then `λ_* g_*(β)` is conjugate to `β`, so it is nontrivial, and
  the loop `g(β)` is not null-homotopic in any such `Z`.
- Equivalently: every finite subcomplex of `Y` containing `K` in which `g(β)` is null-homotopic
  kills a nonzero class of `H_1(K)`.
- Note that `g(β)` is itself null-homologous in `K`, because `H_1(L) = 0`.

**5.3 Shadows when gd(H_L) = 2 (proved, conditional on the hypothesis gd = 2).** In the setting of
§4.1, for `s` large, the shadow image `K_v`:
- has `H_1(K_v) = Z^m` with `m ≥ 1`, by 5.1;
- has `I* ⊆ π_1(K_v)` and `π_2(L) ⊆ π_2(K_v)`, by Lemma 1;
- satisfies 5.2: every null-homotopy in `Y` of a spine loop `g_v(β)` runs through a subcomplex
  whose relative second homology over `K_v` is nonzero.

**5.4 Lemma 3: the retraction pushout (proved).** Put `Z_λ = L ∪_λ Y'`, the adjunction space of
the simplicial map `λ` on the subcomplex `K' ⊆ Y'`. Then `Z_λ` is a 2-dimensional CW complex
containing `L` as a subcomplex, and `Z_λ ≃ ∨^m S^2`.
- *π_1.* Van Kampen for adjunction spaces gives `π_1(Z_λ) = I* / <<λ_*(π_1 K)>> = 1`, since
  `λ_*` is onto and `Y` is simply connected.
- *Homology.* `Z_λ / L ≅ Y' / K'`, so `H_n(Z_λ, L) ≅ H_n(Y, K) ≅ H̃_{n−1}(K)`. With `L` acyclic,
  `H_1(Z_λ) = 0` and `H_2(Z_λ) ≅ H_1(K) = Z^m`.
- *Homotopy type.* By Hurewicz, `π_2(Z_λ) = Z^m`. A map `∨^m S^2 → Z_λ` realizing a basis is a
  homology isomorphism between simply connected CW complexes, hence a homotopy equivalence
  (Whitehead).
- For `m = 0`, `Z_λ` is a contractible 2-complex containing `L`, contradicting claim A. This is a
  second proof of 5.1.

## 6. Attempts on NE and where each dies

The notation is as in §5, with `m ≥ 1`. All the attempts below are honest failures.

**6.1 Nitsche--Thom Theorem 1.3 (covering form). Dies: every relative class is spherical.**
- The variant of Q in §3 needs a finite `Z ⊇ K` that kills the relevant loops and whose quotient
  `Z/K` has a covering with trivial `H_2`.
- Suppose `Z` kills all of `π_1(K)`. Then every class of `H_2(Z/K) = H_2(Z, K) ≅ Z^m` is spherical:
  - The boundary maps give a commuting square with the Hurewicz maps. There
    `∂_π: π_2(Z, K) → π_1(K)` is onto, and `h_1: π_1(K) → H_1(K)` is onto.
  - `∂_H: H_2(Z, K) → H_1(K)` is an isomorphism.
  - So `h_2: π_2(Z, K) → H_2(Z, K)` is onto.
  - A class represented by `(D^2, S^1) → (Z, K)` descends to `S^2 = D^2/S^1 → Z/K` with the same
    Hurewicz image.
- A spherical class lifts to every covering with nonzero image, so no covering of `Z/K` has
  trivial `H_2`.
- If `Z` kills only part of `π_1(K)`, the covering condition is not excluded. But no way was found
  to choose such a `Z` inside an arbitrary `Y`.

**6.2 Homotopy data of the pushout. Dies: examples exist with m ≥ 1.**
- `Z_λ ≃ ∨^m S^2` contains `L` (§5.4). This is not contradictory.
  - Let `β ∈ I*` be non-central. The normal subgroups of `SL(2,5)` are `1`, `{±1}` and `I*`, so
    `<<β>> = I*`. Hence `L ∪_β e^2` is simply connected with `χ = 2`, so it is `≃ S^2`.
  - Adding further 2-cells along null-homotopic loops gives complexes `≃ ∨^m S^2` containing `L`,
    for every `m ≥ 1`.
- The inclusion carries no information either. `∨^m S^2 → ∏^m S^2` is 3-connected and `L` is
  2-dimensional, so `[L, ∨^m S^2] = ∏ [L, S^2] = ∏ H^2(L; Z) = 0` by Hopf. Every map
  `L → ∨^m S^2` is null-homotopic.
- So any contradiction must use how `Z_λ` is built from a contractible `Y`, not only its homotopy
  type rel `L`.

**6.3 Rank count for Nitsche--Thom 1.2. Dies: rank deficit m.**
- For any finite `Z ⊇ K` killing `π_1(K)`, `H_2(Z, K) ≅ Z^m`. So the exponent-sum matrix `E`
  (`b` rows, `a` columns) has rank `b − m`, and `ker E = Z^m`.
- Theorem 1.2 needs `ker E = 0`. Adding unknowns or equations inside `Y` does not change
  `H_2(Z, K)`.

**6.4 Enlarge K to an acyclic subcomplex. Dies: circular.**
- If `K ⊆ K⁺ ⊆ Y` with `K⁺` finite and `H_1(K⁺) = 0`, Q(b) needs a nontrivial hyperlinear
  quotient of `π_1(K⁺)`.
- Extending `λ_*` over the new cells means solving the attaching words over `I*` itself, which is
  an overdetermined system.
- Nitsche--Thom gives solutions only in overgroups, and Q(b) shows the extension always fails.
- It was also not established that a finite acyclic `K⁺ ⊇ K` exists inside `Y` at all.

**6.5 Control the null-homotopies. Dies: no geometric control of Y.**
- By 5.2, a contradiction would follow from a single disc in `Y` bounding some `g(β)`, `β ≠ 1`,
  whose support completes no nonzero relative cycle of `Z_2(Y, K) ≅ Z^m`.
- Nothing about the contractible complex is controlled. When `gd H_L = 2`, `Y / H_L` has infinitely
  many cells, since `H_L` is not finitely presented. So there is no a priori bound on where the
  null-homotopies run.

**6.6 Correct Y by 2-cells. Dies: creates H_2.**
- Attaching 2-cells to `Y` along loops `γ · (g λ γ)^{-1}`, to make `λ` compatible with an
  inclusion, adds spheres. These loops are null-homotopic in `Y`, so `H_2 ≠ 0` and contractibility
  is lost.

**6.7 Dead invariants.**
- *Gersten's criterion.* `cd π_1(K) = ∞`, because `I* ⊆ π_1(K)`, so the criterion is silent.
- *Characteristic classes.* `H^2(K; Z) = Ext(H_1 K, Z) ⊕ Hom(H_2 K, Z) = 0`, so every complex
  line bundle over `K` is trivial.
- *L²-invariants.* Dead, by I5 of `research/artifacts/ideas-topology-2026-09-14.md`.

**6.8 Mapping cylinder. Dies: dimension 3.**
- The mapping cylinder `M_g` contains `L` and is `≃ K`. The pushout `M_g ∪_K Y` is a
  contractible complex containing `L`, but it is 3-dimensional, and `L` does lie in contractible
  3-complexes (its cone).
- The weak form (E) asks for a 2-dimensional replacement of `M_g` that still contains `L`. This is
  a relative D2-type problem. No way was found to see the obstruction from small fibers.

**6.9 TF directly. Dies: same support barrier.**
- For a torsion element `c ∈ π_1(K)` detected by a finite quotient `ρ`, Q(a) forbids `c` from dying
  in any finite `H_1`-injective enlargement.
- `c` does die in `Y`. The obstruction is again the choice of supports, as in 6.5.
- No source among those in §1 settles TF.

## 7. Exact gap

**Proved (complete, modulo the pinned Nitsche--Thom Theorem 1.2 and recalled standard topology).**
- Lemma 1.
- Proposition Q: claim `subcomplex-pi1-kernels-vanish-in-hyperlinear-quotients`, with proof route
  `subcomplex-pi1-kernels-hyperlinear-quotients-proof`. Its only requirement is
  `kervaire-laudenbach-holds-for-hyperlinear`, so the claim's status is computed from that route.
- The four implications of §4.
- The consequences of §5.

**Open.** NE, and TF, which implies it. What remains of NE after §5 is the case `m ≥ 1`.

> **Remaining case.** For small ε, there is no contractible 2-complex `Y` containing a small-fiber
> PL image `K` of `L` with `H_1(K) ≅ Z^m`, `m ≥ 1`.

- By 5.2, a counterexample `(Y, K)` has a rigid feature. For every nontrivial `β ∈ π_1(L)`, every
  finite subcomplex of `Y` in which `g(β)` is null-homotopic kills a nonzero class of `H_1(K)`.
- So a proof through Q has to produce, from the geometry of `Y`, one null-homotopy of one spine
  loop whose support completes no relative cycle of `Z_2(Y, K)`.
- That needs information about `Y` beyond contractibility. §6.2 shows the homotopy type of the
  pushout rel `L` cannot supply it, and §6.5 shows the construction gives no geometric control
  of `Y`.

**What would settle things.**
- A proof of TF, which is strictly weaker than Whitehead's conjecture for finite subcomplexes of
  contractible complexes, refutes Eilenberg--Ganea.
- A counterexample to NE is a non-aspherical finite subcomplex of a contractible 2-complex, with
  `SL(2,5)` in its fundamental group and `H_1 ≠ 0`. It would refute Whitehead's conjecture and TF.

**Novelty.** No novelty is claimed for Lemma 1 (implicit in Bestvina--Brady) or for Q. Q is a
direct extension of the argument already on main. The implication "TF ⇒ Eilenberg--Ganea fails"
was not seen in the sources of §1. It is a formal combination of Bestvina--Brady's argument,
Lemma 1 and §4.1.
