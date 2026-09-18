# Adversarial check of the twisted integral-affine groups W and W_(P,l)

Lane `bh-verify-W`, 2026-09-18. Nodes read at origin/main c9078cd61. This is an adversarial
lane check, not an external review.

**Scope.**
- `W` (bh-universal, c9a38d52c):
  - `twisted-integral-affine-full-group-is-finitely-presented`
  - `twisted-integral-affine-group-fp-via-stein-complex`
  - `integral-affine-structure-group-is-finitely-presented`
  - `integral-affine-halving-stabilizers-are-finitely-generated`
  - `non-spanning-subsets-of-an-f2-space-are-highly-connected`
  - `twisted-integral-affine-brin-thompson-group-is-simple`
  - `one-fp-simple-group-contains-every-integral-linear-group`
- The extension `W_(P,l)` (47bac5d04):
  - `twisted-s-integral-affine-groups-are-fp-and-virtually-simple`
  - `s-integral-affine-structure-group-is-finitely-presented`
  - `s-integral-splitting-stabilizers-are-finitely-generated`
  - `no-homeomorphism-shifts-primes-acting-as-l-adic-scalars`

**Sources read in full, at source, today:**
- Belk–Zaremsky arXiv:2001.04579, TeX §§4–7. On MSI at `gqsrc/bh-openq/2001.04579/twisted_Brin_Thompson.tex`.
- Zaremsky arXiv:2405.18354, TeX §§2–4. On MSI at `gqsrc/bh-one-relator/z2405.src`.
- Matui arXiv:1210.5800, TeX §4.3: the conventions on p. 5, Definition 4.9 (`pi`) and Theorem 4.16 (`simple2`).
- Bass–Milnor–Serre, Publ. IHES 33 (1967), pp. 59–62 (§1). From numdam, on MSI at `gqsrc/bh-verify-W/bms.pdf`.

## Verdicts

| Claim | Verdict |
|---|---|
| `W` finitely presented | **PASS**: no break found; every transferred step re-derived |
| `W` simple | **PASS** after a wording fix to (ii) and (iii), landed with this report |
| `W ⊇ E(Z;D) ⋊ F ⊇ GL_n(Z)` for all `n` | **PASS**: immediate, as one-piece elements |
| `Γ_X` finitely presented | **PASS** |
| Halving stabilizers finitely generated | **PASS** |
| F_2 non-spanning nerve `(r−3)`-connected | **PASS** |
| `W_(P,l)` finitely presented | **PASS** after fixing the stabilizer node's generating set (landed; conclusion unchanged) |
| `W_(P,l)^ab` finite of exponent dividing `l−1`; `D(W_(P,l))` simple and fp | **PASS** |
| `D(W_(P,l)) ⊇ GL_n(Z[1/P])` for all `n` | **PASS** |
| Six-exponentials prime-shift exclusion | **PASS**, conditional on Serre's `l`-adic six exponentials theorem (recalled, not read) |

No FAIL and no GAP. The trust surface is listed at the end.

## 1. Finite presentation of `W`

The route is a dictionary: Belk–Zaremsky's (BZ22) colors `s ∈ S` become directions, the
nonzero finitary functionals in `F_2^(D)`, and their twist group becomes `Γ_X`. I checked each
BZ22 or Zaremsky (Z24) step against the TeX.

**Forests and partitions (BZ22 Lemma 2.3, Prop 5.3).** The four W-node risk points were checked as follows.
- *Common refinement of forest partitions.* Restrict each halving of the second tree to each
  piece of the first. At a node `N` split by `χ`, the piece `a ∩ N` is a coset, and `χ` is either
  constant on it or halves it. So the leaves `a ∩ b` form a forest partition. Non-hierarchical
  partitions of `X` into cosets exist, but none is ever needed.
- *`[f] = [f']` iff the partitions agree.* Two affine charts of one coset differ by a map whose
  linear part preserves `Z_2^D`, so it lies in `GL(Z)`, and hence the maps differ by an element
  of `Γ_X`.
- *Refinement gives `≤`.* If `f'` refines `f`, then `f'f^{-1}` is a forest, by the same
  restriction argument.

**Directedness (BZ22 Prop 5.2).** Write `h = f_2^{-1} t f_1`. Refine the domain to one lattice
`L_0` on which `h` is affine, then refine the codomain to a lattice `L_1` contained in every
image lattice. Every chain `X ⊇ … ⊇ L` of 2-power index has steps of index 2.

**Elementary objects (BZ22 Prop 5.5, 5.6).**
- *Definition.* Leaves are cosets of lattices `L ⊇ 2X` in the root's chart. This is
  `Γ_X`-invariant, and closed under intervals: if `v ≤ u ≤ w` and `v ⪯ w`, then `v ⪯ u ⪯ w`,
  since `L_leaf ⊇ 2X ⊇ 2L_Q`.
- *Finiteness and joins.* An interval `[v,w]` contains finitely many elementary forests, and
  their join is again elementary.
- *Contractibility.* The Quillen argument for the Stein complex transfers verbatim.

**Stabilizers (BZ22 Lemma 6.3; Z24 Citation 4.8, Lemma 4.9).**
- *Vertices.* `Stab(v) = Γ_X ≀ S_m`.
- *Short edges.* The stabilizer is exactly `Q × Γ_X ≀ S_{m−1}`, where `Q` is the stabilizer
  of a halving; the split copy must be fixed.
- *Long edges.* Closed intervals are finite, so Zaremsky's Prop 3.1 applies. That proposition
  needs a rigid, orientation-preserving, cocompact action, and all three hold: the rank
  orients edges, and the vertices of a chain have distinct ranks.

**Cocompactness and `k`-elementary (Z24 Def 4.3, Prop 4.4, Lemma 4.6).**
- *The definition differs from Z24.* Z24 bounds the size of the forest's whole spectrum (the
  union over trees). The route bounds `dim V` tree by tree. The per-tree notion is the right
  one for `W`: `Γ_X ≀ S_r` acts on each copy separately, so it is invariant.
- *Prop 4.4 still goes through.* Its proof uses only that the join of `ℓ` single splits has
  spectrum at most `ℓ` in every tree, and so lies in `(v,w)` when `f` is not `k`-elementary.
- *Orbits.* Finitary `SL(F_2;D)`, the image of finitary `SL(Z)`, is transitive on subspaces
  of each dimension. So `X_m(2)` is `W`-cocompact.

**Descending links (BZ22 §7).**
- *Lemma 7.2 (`VE_m`).* A vertex is a partial matching with an independent label on each
  matched pair, where a label is a pair of complementary half-charts modulo `Γ_X`, and the order
  is inclusion of labeled matchings. BZ22's own proof writes `VE_m^{i,j}` as a union of stars;
  as written, a vertex matching only `{k,l}` lies in no such star. The correct cover is by the
  full subcomplexes on `A ∪ B_ℓ`, where `A ≅ VE_{m−2}` is the set of vertices that avoid
  `i, j` and `B_ℓ` is the set of vertices matching `{i,j}` with label `ℓ`. Each is
  contractible, via the Quillen retraction `a ↦ a ∧ u_ℓ` onto the cone `|B_ℓ|`, and any two
  meet exactly in `A`. The connectivity bound `ν(m) − 1` follows. This is a slip in BZ22's
  write-up; it holds verbatim for `W`.
- *Lemmas 7.4 and 7.5.* Merges of two weight-1 roots are the only `μ`-descending merges, and
  pruning is unchanged.
- *Lemma 7.6.* The atoms below `f_i` are the halvings `χ ∈ U_i ∖ 0`, with
  `U_i = (Σ_leaves L/2X)^⊥`. For distinct atoms, the intersection of their stars is the cone
  `|[join, top)|` when the join is below the top, and empty otherwise. BZ22 says "star of the
  join", which is a loose phrasing of the same thing.
  - The join of a set `A` of atoms is the top exactly when every `f_i` is full and `A` spans
    every `U_i`.
  - So the nerve is either a simplex or `⋃_i Δ_1 ∗ … ∗ K(U_i) ∗ … ∗ Δ_q`. Every fat full root
    has `dim U_i ≥ 2`, so no `K(U_i)` is empty.
  - Connectivity of the join is at least `Σ(d_i − 3) + 2(q − 1)`, then `Σ^{q−1}` gives
    `Σ d_i − 3`.
  - Finally `Σ 2^{d_i} ≤ 2^{Σ d_i}`, so the bound `log_2(m − μ_1) − 3` holds.
- *`K(U)` itself.* The covering is by hyperplane simplices. By the nerve lemma, then the
  crosscut theorem, it is the proper part of the subspace lattice, which Solomon–Tits makes a
  wedge of `S^{r−2}`.

**`Γ_X` finitely presented.**
- *Steinberg part.* Every relation involves at most four indices, and `F` has `k!` orbits on
  ordered `k`-tuples. The stabilizers `F^2` and `F^3` make `x_ab`, `δ_a` and `τ_a` well defined.
- *`K_2(Z)`.* It is generated by `w_12(1)^4 = {−1,−1}`, as in Milnor.
- *Diagonal signs.* The relations present `GL = E ⋊ ⟨δ_{d_0}⟩`: I checked the normal-form
  argument.
- *Translations.* The `τ`-relations match `M τ_c M^{-1} = τ_{Mc}`, and the `τ`'s generate a
  normal abelian subgroup that maps isomorphically onto `Z^(D)`.

**Halving stabilizer `Q`.** I re-derived every step.
- The commutator identities: `x_{d_0 i}(c) x_ik(t) x_{d_0 i}(−c) = x_{d_0 k}(ct) x_ik(t)`, and
  `x_{d_0 i}(c) x_{k d_0}(1) x_{d_0 i}(−c) = x_ki(−c) x_{k d_0}(1)`.
- For `ℓ = 2`, the image in `GL_n(F_2)` of the stabilizer of the row `e_{d_0}^T` is generated
  by the `x_ab(1)` with `a ≠ d_0`.
- `F_{d_0}` has finitely many orbits on the generators.

**Consistency test.** The germ-at-0 cocycle `ρ_0` is the analogue of Zaremsky's quasi-retraction
onto `Z ≀_S G`. Here it lands in `L = GL(Z[1/2]; D) ⋊ F`, which is finitely presented:
- `St(Z[1/2]; D) ⋊ F` is finitely presented by the same criterion;
- `K_2(Z[1/2]) = Z/2`, from the localization sequence and `K_1(F_2) = 1`;
- `SK_1(Z[1/2]) = 0`, by Bass–Milnor–Serre (BMS).

So the natural obstruction does not bite. The untwisted rank-1 analogue is `V_2(D_∞)`, a
contracting Nekrashevych group, which is also finitely presented.

## 2. Simplicity of `W`

The Bleak–Elliott–Hyde criterion (quoted in BZ22, proof of Theorem 4.5) needs vigor,
generation by small-support elements, and perfectness.
- *Vigor.* `DV ≤ W` is vigorous, and vigor passes to overgroups.
- *Generation.* `W = ⟨DV, γ on B⟩`. By induction every forest is a coordinate forest followed
  by structure maps, so `h = c_2^{-1} g c_1`.
- *Perfectness.* `c: Γ_X → W^ab`, `γ ↦ [γ on B]`, is a well-defined homomorphism: any two proper
  bricks are `DV`-equivalent by canonical maps.

**Error fixed (landed with this report).** Item (ii) said that every global `γ` fixes a
coordinate near 0 and that "the `F`-part of `γ` is the identity near 0". That is false: `x_0 ∈ F`
fixes no dyadic in `(0,1)`. Only generators are needed:
- `Γ_X` is generated by `x, x', δ, τ` together with `F_{[0,3/4]} ∪ F_{[1/4,1]}`.
- These two subgroups generate `F`, since `x_0 = a·(a^{-1}x_0)` with `a ∈ F_{[0,3/4]}` equal to
  `x_0` on `[0,1/2]`.
- Their elements fix `7/8`, respectively `1/8`.

Item (iii) is now applied to these generators, so `c(γ) = 2c(γ)`, `c = 0` and `W^ab = 0`.

## 3. `W_(P,l)` deltas (coordinator scope addition)

- **`l`-ary descending links.**
  - *Merges.* `l`-merges give the matching complex of the complete `l`-uniform hypergraph.
    Its connectivity grows linearly in `m` (Brown 1987, recalled, not read here). BZ22's
    induction closes with `ν_l(m) = ⌊(m−l)/(2l−1)⌋`, since `ν_l(m − lr) ≥ ν_l(m) − r`.
  - *Morse data.* Weights are `1 + k(l−1)`. Omitting `μ_1` and `μ_l` makes `VE_m` the right
    sublevel, and "fat" means weight at least `2l−1`. A merge involving anything other than
    singletons raises some `μ_k` with `k ≥ 2l−1`.
  - *Lemma 7.6.* Atoms are lines in `U_i ≤ F_l^(D)`. Solomon–Tits holds over `F_l`, and
    `Σ l^{d_i} ≤ l^{Σ d_i}`. Orbits of tuples of lines are finite in number, because `F_l` is
    finite and `SL_n(Z) → SL_n(F_l)` is onto.
- **Error in `s-integral-splitting-stabilizers-are-finitely-generated` (fixed and landed; the
  conclusion is unchanged).**
  - *The false claim.* The node said the level-`l` image of the kernel is generated by the
    images of `x_ab(1)` (`a ≠ d_0`) and of the diagonals.
  - *Why it fails.* `λ` (row `d_0 = λ e_{d_0}^T`) is multiplicative, and on those generators it
    only takes values in the image of `⟨−1, P⟩ ≤ F_l^×`.
  - *Counterexample.* Take `P = ∅` and `l = 5`. Then `[[2,5],[5,13]] ∈ SL_2(Z)` lies in the
    kernel with `λ = 2`.
  - *Fix.* Add one `m_λ ∈ SL_2(Z)` with `m_λ ≡ diag(λ, λ^{-1}) (mod l)` for each `λ ∈ F_l^×`.
    With these, the image is the whole stabilizer of the line intersected with `im GL_n(R)`,
    and `Q` is still finitely generated. For `l = 2` (`W` itself) nothing changes.
- **Abelianization.** For a generator `g` untouched at `d'` and `d''`:
  - `[g] = l·c(g)`, and `c(g) = l·c(g)`;
  - the class `c` is well defined, because brick counts modulo `l−1` agree for complements of
    proper bricks.
  - So `W^ab` is generated by finitely many elements of order dividing `l−1`. The `F`-generators
    fixing a dyadic generate `F`, as the node argues via `F'` and `F/F' = Z^2`.
  - This is consistent with `V_{l,1}^ab = Z/2` for odd `l`.
- **Matui 4.16 hypotheses (checked in the TeX).** Matui's conventions ask for an étale groupoid
  (second countable, locally compact, Hausdorff), essentially principal, with Cantor unit space,
  and Theorem 4.16 then assumes purely infinite and minimal. All hold:
  - *Hausdorff.* An affine map with coordinate permutation that fixes an open set is the
    identity on its piece: a nontrivial `f ∈ F` moves some free coordinate, and otherwise the
    fixed set is a proper affine subvariety. So `int Fix(g)` is a union of pieces, which is
    clopen.
  - *Essentially principal.* Germ groupoids are effective.
  - *Minimal.* `DV_l` orbits are dense.
  - *Purely infinite.* Every clopen set is properly infinite, via two sub-bricks per brick.
  - *`W = [[𝒢]]`.* `W` is closed under gluing.
  - So `D(W)` is simple, and finitely presented because it has finite index.
- **K-theory inputs.**
  - *BMS, read at source* (p. 60–62). For `O` of arithmetic type in `k` with a real embedding,
    `C_q = Γ_q/E_q = 1` for all `q ≠ 0` (Thm 3.6 with the Ch. II main theorem, `n ≥ 3`). This
    gives `SL_n(Z[1/P], q) = E_n(Z[1/P], q)`, and `SK_1(Z[1/P]) = 0` (take `q = O`).
  - *`K_2(Z[1/P])` finite.* Use the tame-symbol localization sequence
    `K_2(Z) → K_2(Z[1/P]) → ⊕_{p∈P} F_p^×`, with `K_2(Z) = Z/2`.
- **Six exponentials node.** I re-derived all steps.
  - *Steps 1–2.* The continuous extension to closures; open procyclic closures; the continuous
    map `φ` is `x ↦ x^λ` on an open `U_1`, with `λ ≠ 0`.
  - *Step 3.* Only `p_0..p_4 ∈ U_1` is needed; the node's "`k ≤ 5`" is harmless.
  - *Step 4.* The degenerate cases `λ ∈ Q`, `1, λ, λ^2` dependent, and `λ^3 ∈ Q` all
    contradict unique factorization.
  - *Step 5.* It yields six rational values `exp_l(λ^{i+3j} y)` from independent `(1, λ, λ^2)`
    and `(y, λ^3 y)`, all in the domain of convergence.
  - *Status.* This is correct given the `l`-adic six exponentials theorem (Serre 1965/66).

## Trust surface (not re-read at source)

1. Vaserstein–Suslin (and Tits) relative generation, for `n ≥ 3`: `E_n(R,I)` is generated by the
   `x_ji(c) x_ij(t) x_ji(−c)`. It is standard; the `n = 3`, `R = Z` case has its own node.
2. Nerve lemma (Björner), Rota's crosscut theorem, and Solomon–Tits.
3. The connectivity of the `l`-uniform hypergraph matching complex (Brown 1987; for `l = 2`,
   Björner–Lovász–Vrećica–Živaljević).
4. Serre's `l`-adic six exponentials theorem.
5. Nekrashevych finite presentation, used only in the consistency test.
6. Tate/Milnor for `K_2(Z) = Z/2`.

No priority check was done for either group.
