# Paradoxical groupoid families beyond transformation groupoids (part 2)

Lane `un-boundary-families`, 2026-09-13. Unreviewed. This part covers:
- groupoids that are not transformation groupoids: Nekrashevych groupoids of self-similar actions, products of Cuntz
  groupoids (rank-2 graph algebras), and Katsura triples;
- a firewall: the Grigorchuk group.

Part 1 treats Cantor transformation groupoids.

## 0. Interface corollary

**Theorem G.** Let `𝒢` be a Hausdorff ample groupoid whose unit space is compact and infinite, and suppose `𝒢` is
effective and minimal. Let `q` be a prime power and `A = A_(F_q)(𝒢)`. Suppose:
- `A` is finitely generated as a ring;
- `A` contains `s, t` with `ts = 1` and `A(1 - st)A = A`, e.g. a unital copy of `L_(F_q)(1, m)` with `m >= 2`.

Then for `N >= 3`, `S_N = EL_N(A)/Z(EL_N(A))` is an infinite finitely generated simple group with property (T).
Every homomorphism from `S_N`, or from `EL_n(A)` for `n >= 2`, to an MF group is trivial.

*Proof.*
- `steinberg-elementary-groups-are-simple-mod-centre` (reviewed PASS) gives simplicity modulo centre, and (T) because
  `F_q` is finite and `A` is finitely generated.
- `full-defect-ring-non-mf-at-rank-two` gives triviality of MF quotients.
- For a Leavitt copy with generators `s_i, t_i`: `t_i s_j = δ_ij` and `Σ s_i t_i = 1`. Take `s = s_1` and `t = t_1`.
  Then `1 - s_1 t_1 = Σ_(i>=2) s_i t_i` and `t_2 (1 - s_1 t_1) s_2 = 1`, as in the printed Cor l.1016. QED

## 1. Verbatim imports (TeX sources fetched on MSI, 2026-09-13)

**1.1 Exel–Pardo, arXiv:1409.1107, "Self-similar graphs, a unified treatment of Katsura and Nekrashevych
C*-algebras".**
- Standing Hypothesis (l.700): "Throughout this work we shall let $G$ be a countable discrete group, $E$ be a finite graph
  with no sources, $\auto $ be an action of $G$ on $E$, and" (a one-cocycle `φ`, l.706ff).
- Definition EssFree (l.1342): "We will say that $(\Data )$ is pseudo free if, whenever $(g,\ed ) \in G\times E^1$, is such
  that $g\ed = \ed $, and $\varphi (g,\ed )=1$, then $g=1$."
- Proposition EssFreePath (l.1351): "Suppose that $(\Data )$ is pseudo free and that a finite path $\alpha $ of nonzero
  length is strongly fixed for some $g$ in $G$. Then $g=1$."
- Theorem MainHausdorff (l.3347): "Assuming that $(\Data )$ satisfies \ref{StandingHyp}, the following are equivalent:
  (a) for every $g$ in $G$, there are at most finitely many minimal strongly fixed paths for $g$, (b) $\GpdGE $ is
  Hausdorff."
- Theorem CharacMinimal (l.3557): "Given $(G,E,\varphi )$ satisfying \ref{StandingHyp}, one has that the following are
  equivalent: (i) the standard action of $\SGE $ on $E^\infty $ defined in \ref{ActionOfSGE} is irreducible, (ii)
  $\GpdGE $ is minimal, (iii) $E$ is weakly $G$-transitive."
- Katsura triples: Theorems KatsuHausdorff (l.4584), KatsuraMinimal (l.4595: minimal iff `A` irreducible) and
  KatsuraEssPrinc (l.4607: essentially principal iff every circuit has an entry and the stated `B`-condition holds).

**1.2 Kumjian–Pask algebras.**
- Aranda Pino–Clark–an Huef–Raeburn, arXiv:1106.4361, Theorem simplicity (l.931): "Suppose that $\Lambda$ is a
  row-finite $k$-graph without sources, and that $R$ is a commutative ring with $1$. Then $\KP_R(\L)$ is simple if and
  only if $R$ is a field and $\L$ is aperiodic and cofinal."
- Clark–Pangalela, arXiv:1512.06547, Proposition KP-is-isomorphic-to-Steinberg-algebras (l.1689): "Let $\Lambda $ be a
  finitely aligned $k$-graph and $\mathcal{G}_{\Lambda }$ be its boundary-path groupoid as defined in Example
  \ref{groupouid-Glambda}. Let $R$ be a commutative ring with $1$. Then there is an isomorphism
  $\pi _{T}:\operatorname{KP}_{R}\left( \Lambda \right) \rightarrow A_{R}\left( \mathcal{G}_{\Lambda }\right) $ such
  that $\pi _{T}\left( s_{\lambda }\right) =1_{Z_{\Lambda }\left( \lambda \ast _{s}s\left( \lambda \right) \right) }$
  and $\pi _{T}\left( s_{\mu ^{\ast }}\right) =1_{Z_{\Lambda }\left( s\left( \mu \right) \ast _{s}\mu \right) }$ for
  $\lambda ,u\in \Lambda $."

**1.3 Clark–Exel–Pardo–Sims–Starling, arXiv:1806.04362, "Simplicity of algebras associated to non-Hausdorff
groupoids".**
- Theorem grigsimple (l.2282): "Let $G$ be the Grigorchuk group, let $(G,X)$ be its self-similar action, and let $\ggx$
  be the associated groupoid. Then (1) For any field $\KK$ of characteristic zero, $A_\KK(\ggx)$ is simple, and (2)
  $\ogx$ is simple."
- Corollary grigZ2notsimple (l.2432): "Let $G$ be the Grigorchuk group, let $(G,X)$ be its self-similar action, and let
  $\ggx$ be the associated groupoid. Then $\s_{\Z_2}(\ggx)$ is nonzero, and hence the Steinberg algebra $A_{\Z_{2}}(\ggx)$
  is not simple."
- The groupoid is not Hausdorff: Lemma compactopennotregularopen exhibits a compact open set that is not regular open.

## 2. Family O: the odometer's Nekrashevych groupoid

Let `X = {0, 1}`, and let `G = Z = <a>` act self-similarly with `a·0 = 1`, `φ(a, 0) = 1`, `a·1 = 0` and
`φ(a, 1) = a`. In Exel–Pardo's setting, `E` has one vertex and two loops.

- **Pseudo free.** `a^n` fixes a letter iff `n` is even, and `φ(a^(2k), x) = a^k` for both letters. So `a^n·x = x`
  with `φ = 1` forces `n = 0`. By EssFreePath, no path of nonzero length is strongly fixed by `g != 1`, so for `g != 1`
  there are no minimal strongly fixed paths. For `g = 1` the only minimal strongly fixed path is the vertex. By
  MainHausdorff, `𝒢_(G,E)` is Hausdorff.
- **Minimal.** With one vertex, `E` is weakly `G`-transitive, and CharacMinimal (iii)⇒(ii) applies.
- **Effective.** `𝒢_(G,E)` is the groupoid of germs of the inverse semigroup action on `E^∞`. A germ inside the
  interior of the isotropy is represented by an element fixing a neighbourhood pointwise, and is therefore a unit germ.
- **Finitely generated, with a Leavitt copy.** Generators are `s_x` and `t_x` (`x ∈ X`) and the indicator of the germs
  of `a^(±1)`. `s_x`, `t_x` satisfy the Leavitt relations of `L(1,2)` (un-paradox F2).
- The unit space `{0,1}^ℕ` is compact and infinite.

Theorem G applies: `EL_N(A_(F_q)(𝒢_odometer))/Z` is an infinite fg simple Kazhdan group with no nontrivial MF quotient.
The same argument covers every pseudo-free self-similar action of a finitely generated group with `|X| >= 2` in
Exel–Pardo's one-vertex setting.

## 3. Family Π: products of two Cuntz groupoids (product rank-2 graphs)

Let `𝒢_m` be the Cuntz groupoid on `Ω_m = {1..m}^ℕ`, with arrows `(αz, |α| - |β|, βz)`, and put
`L_k(1,m) = A_k(𝒢_m)` (`leavitt-path-algebras-are-steinberg-algebras`).
- **`𝒢_m` is minimal and effective.**
  - Minimal: `(αy, |α|, y)` moves any `y` into the cylinder `Z(α)`.
  - Effective: on a basic bisection `Z(α, β)` with `|α| != |β|`, the isotropy points `αz = βz` determine `z` uniquely,
    so there is no interior. With `|α| = |β|` and `α != β` there are no isotropy points.
- **Products.** For Hausdorff ample `𝒢`, `ℋ`:
  - `𝒢 × ℋ` is Hausdorff ample.
  - Orbits are products, so minimality passes to the product.
  - An open subset of the isotropy contains a basic `U × V` inside `Iso(𝒢) × Iso(ℋ)`, forcing `U` and `V` into the
    unit spaces, so effectiveness passes too.
- **Tensor product.** `f ⊗ g ↦ ((γ, η) ↦ f(γ)g(η))` is an isomorphism `A_k(𝒢) ⊗_k A_k(ℋ) ≅ A_k(𝒢 × ℋ)`.
  - Multiplicative: convolution factorizes.
  - Surjective: a compact open set in the product is a finite disjoint union of products of compact open sets.
  - Injective: take `f_i` linearly independent and evaluate at each `η`.

So `R_(m,n) = L_(F_q)(1,m) ⊗ L_(F_q)(1,n) = A_(F_q)(𝒢_m × 𝒢_n)`. It is finitely generated by the `2m + 2n` Leavitt
generators and contains `L_(F_q)(1,m) ⊗ 1`. Theorem G gives that `EL_N(R_(m,n))/Z` is an infinite fg simple Kazhdan
group with no nontrivial MF quotient, for all `m, n >= 2`.

Recalled, not imported: `R_(m,n)` is the Kumjian–Pask algebra of the product 2-graph `Λ_m × Λ_n` (one vertex). That
2-graph is cofinal (one vertex) and aperiodic (an infinite path `(ω, η)` with neither coordinate eventually periodic has
`σ^p x != σ^q x` for `p != q`), which is consistent with ACaHR Theorem simplicity.

## 4. Firewall: the Grigorchuk group

The Grigorchuk groupoid is not Hausdorff (CEPSS Lemma compactopennotregularopen), and `A_(F_2)(𝒢_Grig)` is not simple
(Corollary grigZ2notsimple). So the reviewed simplicity theorem does not apply over `F_2`. A nonzero proper ideal `I`
gives the normal congruence subgroup `EL_N(A, I)`, so simplicity of `EL_N/Z` is not claimed and is expected to fail. In
characteristic 0 the algebra is simple (Theorem grigsimple), but `A_K` over an infinite field is not finitely
generated, so EJZ gives no (T).

Conclusion: the amenable self-similar group of intermediate growth gives no simple Kazhdan group in this framework over
`F_2`. The case of odd characteristic is not decided here.

## 5. Katsura triples (remark, no node)

Under KatsuHausdorff, KatsuraMinimal and KatsuraEssPrinc (§1.1), the Katsura groupoid is Hausdorff, minimal and
essentially principal. Essentially principal implies effective for Hausdorff étale groupoids: an open bisection inside
the isotropy that contains a non-unit also contains a point with trivial isotropy.

With a properly infinite unit and finite generation, Theorem G applies. Checking those two ring conditions for a
given `(A, B)` is left to the case at hand.

## 6. Separating the families (open)

All the groups `S_N` constructed in parts 1–2:
- contain every finite group (`SL_(Nn)(F_q) ≤ S_N` for all `n`);
- are simple;
- have no MF quotient.

The usual invariants therefore do not separate them. The open claim `boundary-kazhdan-families-pairwise-non-isomorphic`
records attempts:
- Schur multipliers `H_2(S_N)` via `K_2(R)` in the stable range;
- ring-recovery theorems for isomorphisms of elementary groups over noncommutative rings;
- `K_1(R)` separating the unit groups `GL_N(R)` through the printed Thm l.1218, where `R` is purely infinite simple.
