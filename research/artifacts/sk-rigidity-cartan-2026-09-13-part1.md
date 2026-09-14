# Cartan subalgebras of LC(X,F_2)⋊Z: reduction to groupoid models, and the ring invariants (part 1)

Lane sk-rigidity-cartan, 2026-09-13. Every result here is established with a complete proof and UNREVIEWED; review is
requested from sk-verify-5. The main open question, Cartan uniqueness, stays OPEN.

## 0. Setting
- `X ⊆ A^Z` is an infinite minimal subshift with shift `T`. So `T` has no periodic points and acts freely.
- `R_X = LC(X,F_2) ⋊_T Z` and `D_X = LC(X,F_2) ⊆ R_X`.
- `𝒢_X = Z ⋉ X` is the transformation groupoid, with arrows `(T^n x, n, x)`. It is ample, Hausdorff and principal,
  hence effective, and its algebra `A_{F_2}(𝒢_X)` is `R_X` with diagonal `D_X`. That identification is the verbatim
  "cross-product" sentence quoted in `subshift-crossed-product-growth-complexity-citation`.
- `G_X = EL_3(R_X)` and `L_X = GL_3(D_X)`, as in `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`
  (Theorem A).
- An **algebraic Cartan subalgebra** of `R_X` is a `B ⊆ R_X` such that `(R_X,B)` is an algebraic Cartan pair (`def:ACP`
  of ACCCLMRSS, imported in `algebraic-cartan-pairs-are-effective-groupoid-steinberg-algebras`). The torsion condition is
  automatic over the field `F_2`.

## 1. Twists over F_2 are trivial
Let `(Σ,i,q)` be a discrete `F_2`-twist over an ample Hausdorff groupoid `G`, so `T = F_2^× = {1}`.
- By (DT1) of the source (verbatim in its l.270–284), `i({x}×T) = q^{-1}(x)`, so `q^{-1}(G^(0)) = Σ^(0)`.
- `q` restricts to a homeomorphism of unit spaces, so `q(σ) = q(τ)` forces `s(σ) = s(τ)`.
- Then `στ^{-1}` is defined, and `q(στ^{-1})` is a unit, so `στ^{-1} ∈ Σ^(0)` and `σ = τ`. So `q` is a bijective
  groupoid homomorphism.
- By (DT2), with `T = {1}`, each `q|` over a bisection `B_α` has a continuous inverse `P_α`. So `q` is a homeomorphism,
  and `Σ ≅ G` as topological groupoids.
- The twisted Steinberg algebra is defined in `def:A_R(G;Sigma)`, source l.383–388, verbatim: "$f \in C(\Sigma,R)$ is
  \emph{$R^\times$-contravariant} if $f(t \cdot \sigma) = t^{-1}f(\sigma)$ for all $t \in R^\times$ and $\sigma \in
  \Sigma$ [...] $A_R(G;\Sigma) \coloneqq \{ f \in C(\Sigma,R)\,:\, \text{$f$ is $R^\times$-contravariant and
  $q(\supp(f))$ is compact} \}$".
  - For `R^× = {1}` the contravariance condition is vacuous.
  - So composition with `q^{-1}` is an isomorphism `A_{F_2}(G;Σ) ≅ A_{F_2}(G)`.
  - It carries `A_{F_2}(G^(0); q^{-1}(G^(0)))` onto the diagonal `D(G) = LC(G^(0),F_2)`.

Consequence. Combining the imported statements (1)–(4) with §1:
- every algebraic Cartan pair `(A,B)` over `F_2` is `(A_{F_2}(G), D(G))` for an effective ample Hausdorff groupoid `G`;
- conversely, every effective ample Hausdorff `G` gives an algebraic Cartan pair `(A_{F_2}(G), D(G))`.

## 2. Theorem C: reduction of Cartan uniqueness to groupoid-model rigidity
**Theorem C.** Let `X` be an infinite minimal subshift.
1. `D_X` is an algebraic Cartan subalgebra of `R_X`.
2. For every algebraic Cartan subalgebra `B ⊆ R_X`, there are an effective, minimal ample Hausdorff groupoid `G_B` with
   Cantor unit space and a ring isomorphism `R_X → A_{F_2}(G_B)` taking `B` onto `D(G_B)`.
3. The following are equivalent:
   - (a) every algebraic Cartan subalgebra of `R_X` is `β(D_X)` for a ring automorphism `β` of `R_X`;
   - (b) every effective ample Hausdorff groupoid `G` with `A_{F_2}(G) ≅ R_X` as rings is isomorphic to `𝒢_X`.
4. If (a) holds, then for every infinite minimal subshift `Y` with `R_Y ≅ R_X` as rings, `(Y,S)` and `(X,T)` are flip
   conjugate.
5. Suppose (a) holds for `Y`, and every group isomorphism `α: G_X → G_Y` has `α(L_X) = GL_3(B)` for some algebraic
   Cartan subalgebra `B ⊆ R_Y`. Then `G_X ≅ G_Y` implies that `X` and `Y` are flip conjugate.

**Proof of 1.** `𝒢_X` is effective ample Hausdorff. By §1 and `prop:effectiveACPprincipalADP`, `(A_{F_2}(𝒢_X), D(𝒢_X))`
is an algebraic Cartan pair, and it is `(R_X, D_X)`.

**Proof of 2.**
- `lem:C=>Q` makes `(R_X,B)` quasi-Cartan. `thm:main` gives a twist `Σ_B → G_B` and an isomorphism
  `R_X ≅ A_{F_2}(G_B;Σ_B)` taking `B` onto the diagonal.
- `prop:Hausdorff` makes `G_B` Hausdorff, and `prop:effective`(a) makes it effective. §1 removes the twist.
- *Compact unit space.* `B` is maximal commutative, so it contains the centre, and `1 ∈ B`. So `G_B^(0)`, the Stone
  space of the idempotents of `B`, is compact. `R_X` is countable, so it is metrizable.
- *Minimal.*
  - Let `U ⊆ G_B^(0)` be open and invariant with `∅ ≠ U ≠ G_B^(0)`. Put `I_U` = the span of the `1_S`, for compact
    open bisections `S` with `s(S) ⊆ U`.
  - Left multiplication keeps sources inside `U`. Right multiplication moves sources inside the orbit of `U`, which is
    `U`. So `I_U` is a two-sided ideal.
  - It contains `1_V` for a nonempty compact open `V ⊆ U`, so it is nonzero.
  - Every element of `I_U` vanishes at the units outside `U`, but `1 = 1_{G_B^(0)}` does not, so `I_U` is proper.
  - This contradicts simplicity of `R_X` (`minimal-subshift-algebra-is-simple-lef-ring`).
- *No isolated points.*
  - Suppose `x` is isolated and put `e = 1_{{x}} ∈ B`.
  - The isotropy group `G_x^x = r^{-1}(x) ∩ s^{-1}(x)` is open, hence in the interior of the isotropy, hence trivial
    because `G_B` is effective. So `e·A_{F_2}(G_B)·e = F_2·e`, and `e` is a minimal idempotent of the simple unital ring
    `R_X`.
  - Then `eR_X` is a minimal right ideal, so the socle of `R_X` is a nonzero two-sided ideal, hence all of `R_X`.
  - A unital ring equal to its socle is semisimple Artinian. By Wedderburn, `R_X = M_n(F_2)`, since `eR_Xe = F_2`.
  - This contradicts `dim R_X = ∞`.

**Proof of 3.**
- *(b) ⇒ (a).* Let `B` be algebraic Cartan and `Φ: R_X → A_{F_2}(G_B)` as in 2.
  - (b) gives `ρ: 𝒢_X ≅ G_B`, inducing a diagonal-preserving isomorphism `Ψ: R_X = A_{F_2}(𝒢_X) → A_{F_2}(G_B)`.
  - `β = Φ^{-1}Ψ` is a ring automorphism of `R_X` with `β(D_X) = Φ^{-1}(D(G_B)) = B`.
- *(a) ⇒ (b).* Let `G` be effective ample Hausdorff and `Φ: A_{F_2}(G) → R_X` a ring isomorphism.
  - `Φ` is `F_2`-linear, since `F_2` is the prime field.
  - By §1 and `prop:effectiveACPprincipalADP`, `(A_{F_2}(G), D(G))` is an algebraic Cartan pair. Each condition of
    `def:ACP` is expressed through sums, products and linear maps, so `(R_X, Φ(D(G)))` is one too.
  - (a) gives `β` with `β(D_X) = Φ(D(G))`. So `Φ^{-1}β: A_{F_2}(𝒢_X) → A_{F_2}(G)` is a diagonal-preserving ring
    isomorphism.
  - Since `𝒢_X` is effective, `diagonal-preserving-isomorphisms-reconstruct-effective-groupoids` (with `R = F_2`, which
    is indecomposable) gives `G ≅ 𝒢_X`.

**Proof of 4.** `𝒢_Y` is effective ample Hausdorff with `A_{F_2}(𝒢_Y) = R_Y ≅ R_X`, so (b) gives `ρ: 𝒢_Y ≅ 𝒢_X`.
- `ρ` carries compact open bisections with full source and range to such bisections, so it induces an isomorphism of
  their groups `[[𝒢_Y]] ≅ [[𝒢_X]]`.
- For a transformation groupoid this group is the topological full group. A compact open full bisection covers
  finitely many sets `{(T^n x, n, x) : x ∈ U_n}`, so its homeomorphism has a continuous cocycle. So `[[S]] ≅ [[T]]`.
- `topological-full-groups-determine-flip-conjugacy` (Giordano–Putnam–Skau; Bezuglyi–Medynets) gives flip conjugacy.

**Proof of 5.** Given `α` with `α(L_X) = GL_3(B)`, (a) for `Y` gives `β` with `B = β(D_Y)`.
- `β` induces an automorphism `EL_3(β)` of `G_Y`, since it maps elementary matrices to elementary matrices, with
  `EL_3(β)(L_Y) = GL_3(β(D_Y)) = GL_3(B)`.
- `α' = EL_3(β)^{-1}∘α: G_X → G_Y` is an isomorphism with `α'(L_X) = L_Y`.
- Theorem A gives flip conjugacy. ∎

## 3. Theorem G (ring invariants)
Statement and proof: `subshift-ring-isomorphism-preserves-soe-class-and-growth` and its `-proof` route.
- `R_X ≅ R_Y` gives strong orbit equivalence (Theorem R), and `n·p_X(n) ≈ n·p_Y(n)` with explicit constants
  (Nekrashevych, `pr:shiftgrowth`).
- So zero entropy and `limsup log p(n)/log n` are ring invariants, and `GKdim R_X = 1 + limsup log p_X(n)/log n`.
- Scope: Boyle–Handelman (Pacific J. Math. 164 (1994), abstract) put homeomorphisms of every entropy inside one strong
  orbit equivalence class. Whether two expansive ones of zero and positive entropy share a class is not checked here.

## 4. Model tests
- **Periodic `X` (a finite orbit): hypotheses fail as they should.** `𝒢_X` has isolated points with isotropy `pZ`, so it
  is not effective. `D_X` is not maximal commutative, since `u^p` commutes with it, and `R_X` is not simple.
  Statements 1–2 of Theorem C fail there, consistent with their use of freeness and minimality.
- **Fibonacci subshift.** All hypotheses hold.
- **Inner conjugates.** Take a nonempty clopen `U` with `U ∩ TU = ∅`.
  - `(e_U u)^2 = e_U e_{TU} u^2 = 0`, so `w = 1 + e_U u` is a unit with `w^{-1} = w`.
  - For clopen `V`, using `u e_V = e_{TV} u`: `w e_V w^{-1} = e_V + (e_{U∩V} + e_{U∩TV}) u + e_{U∩TV∩TU} u^2`. The last
    term is `0`.
  - For `V = U` this is `e_U + e_U u`, which has a nonzero `u`-coefficient and so is not in `D_X`.
  - So `wD_Xw^{-1} ≠ D_X`. It is again an algebraic Cartan subalgebra, since pair conditions transport along
    automorphisms.
  - So uniqueness can only hold up to automorphism, which is how Theorem C(a) is stated.
- **Flip.** `u ↦ u^{-1}` is an automorphism `R_X ≅ R_{X,T^{-1}}` fixing the diagonal. This matches "flip" in 4.
- **C*-analogue.** Giordano–Putnam–Skau: `C(X)⋊Z ≅ C(Y)⋊Z` for strongly orbit equivalent systems that are not flip
  conjugate, so non-conjugate C*-Cartans exist. Statement (a) is the purely algebraic content that the C*-algebra loses.

## 5. What remains
Cartan uniqueness (`subshift-crossed-product-algebraic-cartans-are-conjugate`) is OPEN. By Theorem C it is equivalent to
groupoid-model rigidity (b). Firewalls:
- **F-K.** Every model `G` of `R_X` has the same ordered `K_0` and unit, so any K-theoretic invariant is at most strong
  orbit equivalence.
- **F-G.** Growth only detects the class of `n·p(n)`, so it cannot separate two models whose complexities have equal
  growth.
- **F-min.** Every model is minimal and effective with Cantor unit space (Theorem C.2). "Nondegeneracy" invariants give
  nothing.
- **F-inner.** Cartans are genuinely non-unique as subsets (§4), so any proof must build the automorphism `β`, not show
  `B = D_X`.
Sharpest decider: find a ring isomorphism `R_X ≅ R_Y` between strongly orbit equivalent, non-flip-conjugate subshifts
of equal complexity growth, or rule out a non-transformation-groupoid model of `R_X`.
