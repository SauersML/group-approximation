# Virtual sections of Aut(F_n) → Out(F_n): what cohomology and trees give

Lane `bh-aut-out-virtual-section`, 2026-09-12. Target: decide whether
`π: Aut(F_n) → Out(F_n)` splits over a finite-index subgroup for `n ≥ 3`.
By `outer-covering-lifts-are-virtual-sections`, a section would give
`out-free-groups-virtually-embed-in-aut-free-groups` with `m = n`, and so
Boone--Higman for `Out(F_n)`.

**Outcome.** Not decided. Two results are proved below.
1. **No rational cohomology obstruction.** The abelianized extension is
   killed by `n − 1`. So `π^*` is injective on rational cohomology with any
   coefficients pulled back from `Out(F_n)`, and no cohomological or transfer
   argument of that kind can exclude a virtual section. Any exclusion has to be
   nonabelian, as in Chen--Salter.
2. **Side choice.** A section restricted to a finite-index FA subgroup of the
   automorphisms of one factor of a rank-one free splitting fixes a vertex of
   the Bass--Serre tree. Either it is conjugate to the standard lift, or it
   fixes exactly one vertex of the big factor. This is the free-group analogue
   of the "puncture on one side" step of Mess and Chen--Salter.

## Literature status

- **arXiv API.** Queries on 2026-09-12 for `abs:"Out(F_n)" AND abs:split` and
  `abs:"virtually split" AND (abs:automorphism OR abs:outer)` returned nothing
  on this question. Further queries hit HTTP 429, and WebSearch is exhausted,
  so the search is not exhaustive.
- **Nearest relative.** The hits closest in shape are the Laudenbach sequence
  results (Brendle--Broaddus--Putman arXiv:2012.01529; Robinson Arrieta
  arXiv:2310.13527). They split a *different* extension, `Mod(#S²×S¹) → Out(F_n)`
  by sphere twists, and say nothing about `Aut(F_n) → Out(F_n)`.
- **Chen--Salter method.** Read from the ar5iv HTML of arXiv:1804.11235; the
  source PDF was not re-read here. They show separating twists lift to twists
  about a curve on one side of the puncture (their Lemma 2.16). They then push
  the section to the handle-pushing subgroup `π1(UTΣ_p)` and contradict with a
  diagonal-class computation that yields a nonzero multiple of the Euler
  characteristic. The free-group partial-conjugation subgroup is a free group
  with no central extension, so that final step has no direct analogue.

## 1. The abelianized extension is killed by n − 1

Write `H = H_1(F_n; Z)` with basis `t_i = [x_i]`, and put `Z[H]` for the
Laurent ring. `Aut(F_n)` acts on `H` through `ρ: Aut(F_n) → GL_n(Z)`, and inner
automorphisms act trivially, so `H` is an `Out(F_n)`-module.

**Fox Jacobian.** For `φ ∈ Aut(F_n)` let `M(φ)_{ki} = ∂φ(x_k)/∂x_i ∈ Z[F_n]`,
and `M̄(φ)` its image in `Z[H]`. The chain rule
`∂φ(w)/∂x_i = Σ_k φ(∂w/∂x_k)·∂φ(x_k)/∂x_i`, applied to `w = ψ(x_j)`, gives

    M̄(φψ) = φ_*(M̄(ψ)) · M̄(φ).

Determinants live in the commutative ring `Z[H]`, whose units are `±H`
(trivial units of a Laurent polynomial ring). Write `det M̄(φ) = ε(φ)·h(φ)` with
`ε(φ) = ±1` and `h(φ) ∈ H` (additive). Then

    h(φψ) = h(φ) + φ_*·h(ψ),

so `h: Aut(F_n) → H` is a crossed homomorphism.

**Value on inner automorphisms.** Let `φ = ι_g`, with `ι_g(x) = g x g^{-1}`. Then

    ∂(g x_k g^{-1})/∂x_i = ∂_i g + g δ_{ki} − g x_k g^{-1} ∂_i g .

Abelianized, with `t = [g]`, this is the matrix `t·I + u v^T`, where
`u_k = 1 − t_k` and `v_i = ∂̄_i g`. The fundamental formula
`g − 1 = Σ_i ∂_i g (x_i − 1)` gives `Σ_i v_i (1 − t_i) = 1 − t`, so

    det(t·I + u v^T) = t^{n−1}(t + v^T u) = t^{n−1}(t + 1 − t) = t^{n−1}.

Hence `ε(ι_g) = 1` and `h(ι_g) = (n − 1)[g]`.

**Consequence for the extension class.** `F_n` is centreless for `n ≥ 2`, so
`Inn(F_n) ≅ F_n`. `[F_n, F_n]` is characteristic, so it is normal in
`Aut(F_n)`, and

    1 → H → E := Aut(F_n)/[Inn, Inn] → Out(F_n) → 1

is an extension with class `c ∈ H²(Out(F_n); H)`. The restriction of `h` to
`Inn` is a homomorphism, so `h` kills `[Inn, Inn]` and descends to a crossed
homomorphism `h̄: E → H` with `h̄|_H = (n − 1)·id`. So `(n − 1)·c = 0`, and
`c ⊗ Q = 0`.

**Injectivity of π^*.** Let `M` be any `Q[Out(F_n)]`-module, viewed as an
`Aut(F_n)`-module on which `Inn` acts trivially. The Lyndon--Hochschild--Serre
spectral sequence of `1 → F_n → Aut(F_n) → Out(F_n) → 1` has two rows, since
`cd F_n = 1`: `E_2^{p,0} = H^p(Out; M)` and `E_2^{p,1} = H^p(Out; Hom(H, M))`.
- **Only d_2.** The only differential is `d_2: E_2^{p,1} → E_2^{p+2,0}`, and
  `ker(π^*: H^k(Out; M) → H^k(Aut; M)) = im d_2`.
- **Comparison.** The map of extensions `Aut(F_n) → E` is `F_n → H` on
  kernels. It induces isomorphisms on rows 0 and 1 of the `E_2` pages, so the
  two `d_2`s agree.
- **d_2 for abelian kernel.** For an abelian kernel with trivial action on `M`,
  `d_2` is cup product with the extension class followed by evaluation
  `H ⊗ Hom(H, M) → M`. This is the standard Hochschild--Serre description, cited
  and not re-read from source.
- **Conclusion.** `c ⊗ Q = 0` gives `d_2 = 0`, so `π^*` is injective in every
  degree.
- **Alternative argument.** The Becker--Gottlieb/Dold transfer for the
  fibration `BF_n → BAut(F_n) → BOut(F_n)` gives `τ∘π^* = χ(F_n)·id = (1 − n)·id`
  directly. Also not re-read.

**Why this kills the method.** Suppose `s: Γ → Aut(F_n)` is a section over a
finite-index `Γ`, and let `x ∈ H^k(Out; M)`. Then
`res_Γ(x) = s^*(π^* x)|_{π^{-1}(Γ)}`, and `res_Γ` is injective by transfer. So
a virtual section forces `π^*` to be injective, and `π^*` is always injective.
No argument of the form "a rational class dies in `Aut(F_n)`" can exist, for any
coefficient module pulled back from `Out(F_n)`. An obstruction must use
nonabelian structure, coefficients nontrivial on `F_n`, or torsion classes. The
integral class `c`, of order dividing `n − 1`, is the only abelian candidate. It
could die on a finite-index subgroup, and that was not decided.

This parallels the surface case. Morita's crossed homomorphism
`Mod(Σ_{g,*}) → H` restricts to `(2 − 2g)`·abelianization on `π1`, and
Chen--Salter need genuinely nonabelian input.

## 2. Side choice for finite-index FA factor subgroups

**Setup.**
- Let `F_n = ⟨p⟩ ∗ B` with `rank B = n − 1 ≥ 2`, and let `T` be its Bass--Serre
  tree. Its vertices are the cosets `x⟨p⟩` and `xB`, and its edges are the
  elements of `F_n`.
- Let `J_B ≤ Out(F_n)` be the image of `β ↦ [id_⟨p⟩ ∗ β]`, `β ∈ Aut(B)`.
  **This map is injective.** If `id ∗ β = ι_x`, then `x` centralizes `p` and
  normalizes `B`, so `x ∈ ⟨p⟩ ∩ B = 1`.
- Every `φ ∈ π^{-1}(J_B)` has the form `ι_y(id ∗ β)` and acts on `T` by
  `x⟨p⟩ ↦ φ(x)y⟨p⟩`, `xB ↦ φ(x)yB`, `x ↦ φ(x)y`. These formulas are
  well defined because `φ(p^m) = y p^m y^{-1}` and `φ(b) = y β(b) y^{-1}`. The
  action preserves types, so there are no inversions.

**Lemma.** Let `Γ ≤ Out(F_n)` and `s: Γ → Aut(F_n)` be a section. Suppose
`Λ := Γ ∩ J_B` has finite index in `J_B`, and has property FA and finite
abelianization. Then exactly one of the following holds.
- **(S) Standard.** Some `x ∈ F_n` gives `s(λ) = ι_x (id ∗ β_λ) ι_x^{-1}` for
  all `λ ∈ Λ`. The fixed tree of `s(Λ)` is then the star of the vertex `x⟨p⟩`.
- **(N) One big vertex.** The fixed tree of `s(Λ)` is a single vertex `xB`.
  After conjugating by `ι_x`, `s(λ) = ι_{y(λ)}(id ∗ β_λ)` with `y: Λ → B` a
  cocycle. This gives a homomorphism `ρ(λ) = ι_{y(λ)} β_λ ∈ Aut(B)` lifting
  `λ ↦ [β_λ] ∈ Out(B)`, and `s(λ)(p) = y(λ) p y(λ)^{-1}`.

**Proof.**
1. **Fixed vertex.** FA gives a fixed point, and since there are no
   inversions it is a vertex.
2. **A fixed ⟨p⟩-vertex gives (S).** If the fixed vertex is `x⟨p⟩`, conjugate
   by `ι_x^{-1}` to fix `⟨p⟩`. Then `y⟨p⟩ = ⟨p⟩`, so `y(λ) ∈ ⟨p⟩`, and
   `λ ↦ y(λ)` is a homomorphism `Λ → ⟨p⟩ ≅ Z`. It is trivial by finite
   abelianization, so `s(λ) = id ∗ β_λ`.
3. **Fixed tree in case (S).** The standard lift fixes `⟨p⟩` and every
   neighbour `p^m B`.
   - A neighbour `p^m b⟨p⟩` of `p^m B`, with `b ∈ B ∖ 1`, is fixed exactly
     when `b^{-1} β_λ(b) ∈ B ∩ ⟨p⟩ = 1` for all `λ`.
   - `Λ` has finite index in `J_B`, so the `β_λ` form a finite-index subgroup
     of `Aut(B)`. It contains `ι_{c^k}` for every `c ∈ B` and some fixed
     `k ≥ 1`. So `b` would commute with every `c^k`, which is impossible
     because `rank B ≥ 2`.
   - Fixed sets are subtrees, so the fixed tree is exactly the star of `⟨p⟩`.
4. **Otherwise (N).** If no `⟨p⟩`-vertex is fixed, the fixed tree contains no
   edge, so it is one `B`-vertex. Conjugating it to `B` forces `y(λ) ∈ B`, and
   `y` is a cocycle because `s` is a homomorphism. ∎

**Correction (review-swarm6-groups-2026-09-12 §2).** The first version of the
Lemma did not require `Λ` to have finite index in `J_B`, and was then false.
- If `Γ = 1`, then `s(Λ)` fixes all of `T`, which is neither a star nor a
  single vertex.
- Take `rank B ≥ 3` with basis `b_1, b_2, b_3, …`, and let `β` swap `b_1, b_2`
  and fix the rest. Put `Γ = ⟨[id ∗ β]⟩ ≅ Z/2` with `s([id ∗ β]) = id ∗ β`.
  The fixed tree contains `pB` and `b_3⟨p⟩`, which are at distance 3.

Finite index is used only in step 3.

**When FA holds.** `Aut(F_m)` has property (T) for `m ≥ 4`, by Nitsche for
`m = 4` (`aut-f4-has-property-t`) and by Kaluba--Nowak--Ozawa and
Kaluba--Kielak--Nowak for larger `m`, as recorded in
`research/artifacts/aut-f4-property-t-status-2026-09-12.md`. (T) passes to
finite index and implies FA and finite abelianization. For finite-index `Γ`,
`Λ` has finite index in `J_B ≅ Aut(F_{n−1})`. So for `n ≥ 5` all three
hypotheses hold for every finite-index `Γ`.

**Where this stops.** A contradiction needs the side choices of different
splittings to be incompatible under `Γ`, as Chen--Salter get from their Euler
class computation. In case (N), `ρ` restricted to `Λ ∩ Inn(B)` is a homomorphism
into `Inn(B)`. If it kills a finite-index subgroup of `Inn(B)`, it gives a
virtual section of `Aut(B) → Out(B)` over `ρ(Λ)`, which is the same problem one
rank down. Neither case was ruled out.
