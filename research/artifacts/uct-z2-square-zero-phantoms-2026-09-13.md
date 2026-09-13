# Square-zero Z/2-phantoms: equivalent forms and firewalls

Lane ex3-uct-square-zero-phantom, 2026-09-13. All derivations are **unreviewed**.
Inputs are established repo nodes, named where used, plus standard facts (S1)–(S6), which were not re-read.

## 0. Question and why it matters

- `G = Z/2` with generator `σ`. `KK^G` is separable `G`-C\*-algebras, and `⊗` is the minimal tensor
  product with the diagonal action (Kasparov external product).
- A **phantom** is a `D` with `Res D ≃_KK 0` and `D ⋊ G ≃_KK 0`
  (`zp-detection-equals-meyer-nadareishvili-sufficiency`). It is **square-zero** if
  `D ⊗ D ≃_(KK^G) 0`.
- **Source.** The square-zero Attempt on `kazhdan-group-algebra-tate-part-has-no-phantom`
  (lane ex3-uct-tate-diagonal, 213d74c6bb): if (P1) holds for `Γ` and for `Γ × Γ`, the Tate phantom `Φ`
  of `C*_r(Γ)` satisfies `Φ ⊗ Φ ≃ 0`. So "no nonzero phantom is square-zero" would convert (P1) for `Γ`
  and `Γ × Γ` into (P2) for `Γ`.
- **Nuclear dynamical form.** Every nuclear `D` with `Res D ≃ 0` is `KK^G`-equivalent to a pointwise
  outer `(O_2, α)` (item 3 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`). Then `D ⊗ D` is
  `(O_2 ⊗ O_2, α ⊗ α)`.

## 1. Standard inputs (not re-read)

- (S1) Kasparov external product `KK^G(A,B) × KK^G(C,E) → KK^G(A ⊗ C, B ⊗ E)` (minimal tensor,
  diagonal action), and the trivial-action functor `τ : KK → KK^G`.
- (S2) Takai duality for finite abelian `G`: `(A ⋊ G) ⋊ Ĝ ≅ A ⊗ K(ℓ²G)` with `α ⊗ Ad λ`, which is
  exterior equivalent to `α ⊗ id`. So `D ≃_(KK^G) (D ⋊ G) ⋊ Ĝ`.
- (S3) Green–Takai subgroup duality: for a finite abelian `K` acting on `C` and a subgroup `L ≤ K̂`,
  `(C ⋊ K) ⋊_(γ̂|L) L` is Morita equivalent to `C ⋊_(γ|L^⊥) L^⊥`, where
  `L^⊥ = {k ∈ K : λ(k) = 1 for all λ ∈ L}`.
- (S4) Crossed products by finite groups commute with exterior tensor products:
  `(A ⊗ B) ⋊ (G × H) ≅ (A ⋊ G) ⊗ (B ⋊ H)`.
- (S5) If `α` is an outer automorphism of a simple unital C\*-algebra and `β` is any automorphism of a
  simple unital C\*-algebra, then `α ⊗ β` is outer (Kishimoto-type fact).
- (S6) Kirchberg–Phillips: a unital Kirchberg algebra that is KK-contractible is isomorphic to `O_2`.

## 2. Theorem S

Let `D` be a phantom.

1. **Categorical form.** `D ⊗ D ≃ 0` iff `(D ⊗ D) ⋊ G ≃_KK 0`.
2. **Self-duality.** `D̂ := D ⋊ G`, with the dual action, is a phantom. Moreover
   `(D ⊗ D) ⋊ G` is Morita equivalent to `(D̂ ⊗ D̂) ⋊ Ĝ`, so `D` is square-zero iff `D̂` is.
3. **Dynamical form.** Let `D = (O_2, α)` with `α` pointwise outer and `O_2 ⋊_α G ≃_KK 0`.
   - (a) `α ⊗ α` is strongly approximately inner.
   - (b) The following are equivalent:
     - `D ⊗ D ≃_(KK^G) 0`;
     - `α ⊗ α` has the Rokhlin property;
     - `(O_2 ⊗ O_2) ⋊_(α⊗α) G ≅ O_2`;
     - `2[1] = 0` in `K_0(F^(α⊗α))`, where `F = (O_2 ⊗ O_2)_∞ ∩ (O_2 ⊗ O_2)'`;
     - `O_3` embeds unitally into `F^(α⊗α)`.
4. **Calibration.** For every pointwise outer `α : G ↷ O_2`, `α ⊗ id_(O_2)` has the Rokhlin property.
   So the Rokhlin property does not descend from a tensor product to a factor. Any proof that phantoms
   are not square-zero has to use that *both* factors carry `α`.

### Proof of 1

- By items 1 and 6 of `zp-restriction-trivial-splits-cellular-plus-phantom`,
  `θ_(D⊗D) = θ_D ⊗ θ_D = (−1)(−1) = 1`.
- By item 2 there, `(D ⊗ D) ⋊ G ≃_KK 0` iff `1 − θ_(D⊗D) = 0` is invertible in
  `KK^G(D ⊗ D, D ⊗ D)`. That holds iff this ring is zero, that is, iff `D ⊗ D ≃ 0`.

### Proof of 2

- **D̂ is a phantom.** `Res D̂ = D ⋊ G ≃ 0`, and `D̂ ⋊ Ĝ ≅ D ⊗ K(ℓ²G) ≃_KK Res D ≃ 0` by (S2).
- **Write D as a dual.** Put `B = D̂` with action `β`. By (S2), `D ≃_(KK^G) B ⋊_β Ĝ` with the dual
  action. By (S4), the `G × G`-algebra `D ⊠ D` (actions `σ ⊗ 1` and `1 ⊗ σ`) is, up to
  stabilization, `(B ⊠ B) ⋊ (Ĝ × Ĝ)` with the dual action of `G × G = (Ĝ × Ĝ)^`.
- **Restrict to the diagonal.** Restricting to `Δ_G ≤ G × G` gives exactly `α ⊗ α` on `D ⊗ D`.
- **Apply Green–Takai.** Take (S3) with `K = Ĝ × Ĝ`, `C = B ⊗ B` and `L = Δ_G`. Then
  `L^⊥ = {(χ, χ') : χ(g) χ'(g) = 1 for all g}`, which equals `{(χ, χ̄)} = Δ_Ĝ` because `χ̄ = χ` on
  `Z/2`. So `(D ⊗ D) ⋊_(α⊗α) G ~_M (B ⊗ B) ⋊_(β⊗β) Ĝ = (D̂ ⊗ D̂) ⋊ Ĝ`.
- **Conclude.** Morita equivalence preserves KK-contractibility. Apply part 1 to `D` and to `D̂`.

### Proof of 3(a)

- By item 2(a) of `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion` (Step C of its proof route),
  there are unitaries `w_n ∈ O_2` with `‖σ(w_n) + w_n‖ → 0` and `w_n* a w_n → σ(a)` for all `a`.
- Put `β = α ⊗ α` and `u_n = w_n ⊗ w_n`. Then
  `β(u_n) − u_n = (σw_n + w_n) ⊗ σw_n − w_n ⊗ (σw_n + w_n)`.
  Expanding: `σw⊗σw + w⊗σw − w⊗σw − w⊗w`. So `‖β(u_n) − u_n‖ ≤ 2‖σ(w_n) + w_n‖ → 0`.
- `v_n = (u_n + β(u_n))/2` is `β`-invariant with `‖v_n − u_n‖ → 0`. For large `n`,
  `z_n = v_n |v_n|^(−1)` is a `β`-invariant unitary with `‖z_n − u_n‖ → 0`.
- `u_n* (a ⊗ b) u_n = w_n* a w_n ⊗ w_n* b w_n → σ(a) ⊗ σ(b)`. By density and `‖z_n − u_n‖ → 0`,
  `Ad(z_n*) → β` pointwise.
- So `β` is a pointwise limit of inner automorphisms by invariant unitaries: it is strongly
  approximately inner. This is the dynamical reading of `θ_(D⊗D) = 1`.

### Proof of 3(b)

- `β = α ⊗ α` is pointwise outer on `O_2 ⊗ O_2 ≅ O_2` by (S5).
- **KK^G-contractible ⟺ Rokhlin.** Item 2 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`.
- **⟺ crossed product is O_2.** By part 1, `D ⊗ D ≃ 0` iff `(O_2 ⊗ O_2) ⋊_β G ≃_KK 0`. This crossed
  product is a unital Kirchberg algebra because `β` is outer, so by (S6) this is iff it is `≅ O_2`.
- **Rokhlin ⟹ 2[1] = 0.** If `β` is Rokhlin, its crossed product is contractible, and item 2(b) of
  `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion` gives `2[1] = 0` and `O_3 ⊆ F^β` unitally.
- **2[1] = 0 ⟹ Rokhlin.** Item 1 of that node (no crossed-product hypothesis) makes `2[1] = 0`
  equivalent to `β̂` being strongly approximately inner. Item 3(b) of
  `z2-odd-commutator-below-half-forces-commuting-towers` then gives the Rokhlin property for `β`.
- **O_3.** `O_3 ⊆ F^β` unitally iff `2[1] = 0`, by item 1 of the O_2 node.

### Proof of 4

- `τ(O_2) ≃_(KK^G) 0`, since `O_2 ≃_KK 0` and `τ` is a functor (S1).
- The external product with `id_D` gives `D ⊗ τ(O_2) ≃ 0`.
- `α ⊗ id_(O_2)` is pointwise outer by (S5), on `O_2 ⊗ O_2 ≅ O_2`. Item 2 of
  `outer-actions-on-o2-kk-g-contractible-iff-rokhlin` gives the Rokhlin property.

### Model tests

- **The Rokhlin model** `R = id ⊗ μ_G` is the zero object and is trivially square-zero. Consistent.
- **The trivial action on O_2** is not outer. `τ(O_2) ⊗ τ(O_2) ≃ 0`, but `id ⊗ id` is not Rokhlin.
  So outerness cannot be dropped from 3(b) or from 4.
- **An inner symmetry** `Ad(s)`, with `s` a self-adjoint unitary in `O_2`, has
  `Ad(s) ⊗ Ad(s) = Ad(s ⊗ s)`. That is strongly approximately inner, as 3(a) predicts, and never
  Rokhlin. Again it is not outer.
- **Self-duality.** The Rokhlin model is dual to an approximately representable action (Izumi). Both
  are zero objects, so part 2 is consistent there.

## 3. Firewalls for the open claim `z2-o2-phantoms-are-not-square-zero`

- **F1. Formal tensor-triangular arguments.**
  - On the `Res`-contractible layer, phantoms are the `θ = −1` part and tensor squares land in
    `θ = +1` (item 6 of the splitting node). Formally a phantom is an odd object in a `Z/2`-graded
    world.
  - A nonzero odd object with zero square is consistent with every formal relation available here:
    `1 + χ = 1 + θ = 0`, `2` invertible, multiplicativity of `θ`.
  - Recalled analog, not imported: the Brown–Comenetz dual of the sphere satisfies `I ∧ I ≃ *`.
  - So a proof needs analytic input.
- **F2. Retraction.** For every phantom, `j = id ⊗ 1 : D → D ⊗ D` is zero in `KK^G` (item 1 of
  `o2-contractible-crossed-product-inner-half-flip-mcduff`). So `id_D` never factors through `D ⊗ D`
  along `j`, and no "multiplication" `D ⊗ D → D` retracting `j` exists.
- **F3. Descent.** Part 4: `α ⊗ β` can be Rokhlin while `α` is not. The descent must use `β = α`.
- **F4. Relative McDuff extension.**
  - By item 3 of the half-flip node, `α` is Rokhlin iff there is a unital equivariant \*-homomorphism
    `Ψ : (O_2 ⊗ O_2, α ⊗ α) → ((O_2)_∞, α_∞)` with `Ψ(a ⊗ 1) = a`. Here `Ψ(1 ⊗ b)` is the McDuff map
    into `A_∞ ∩ A'`, and conversely a McDuff map `ψ` gives `Ψ(a ⊗ b) = a ψ(b)`.
  - Under square-zero, the source `(O_2 ⊗ O_2, α ⊗ α)` is conjugate to the Rokhlin model `R`
    (item 2 of the KK^G node).
  - So the question becomes a *relative existence* problem: extend the constant inclusion, given on
    the subalgebra `O_2 ⊗ 1` of `R`, to all of `R`. The `KK^G`-obstruction vanishes by F2. Existence
    theorems of Gabe–Szabó type prescribe KK^G-classes, not restrictions to a subalgebra, so they do
    not apply as stated. The route stops here.
- **F5. Construction side.** A square-zero phantom is in particular a phantom, so it would answer
  Barlak–Li II, Remark 4.14(2), negatively for outer order-2 actions (item 4 of the KK^G node). The
  repo has no candidate.
- **F6. A sufficient condition for square-zero (the Z/4 square root).**
  - Let `F` be the flip on `O_2 ⊗ O_2`, and `γ = (α ⊗ 1) ∘ F`.
  - `F (α ⊗ 1) F = 1 ⊗ α`, so `γ² = (α ⊗ 1)(1 ⊗ α) = α ⊗ α` and `γ⁴ = id`. So `γ` generates a
    `Z/4`-action whose square is the diagonal action.
  - If `γ` is Rokhlin, its restriction `α ⊗ α` is Rokhlin, and `D` is square-zero.
  - `γ` is the multiplicative induction of `D` from `Z/2` to `Z/4` (Nishikawa–Petrosyan equivariant
    power functor; recalled, not imported). No converse is claimed.

## 4. Consequences for the Tate diagonal (P2)

- **Only the categorical form applies.** `Φ` comes from `C*_r(Γ)`, which is exact but not nuclear.
  The `O_2` realization in part 3 does not apply to `Φ`. What (P2) needs is the categorical statement,
  for all separable algebras with the minimal tensor product.
- **(P1) for Γ × Γ is outside the stated claim.** The square-zero reduction needs (P1) for `Γ × Γ`.
  That group is not hyperbolic, so it lies outside
  `kazhdan-tate-crossed-product-inclusion-is-kk-equivalence` as written.
- **Detection implies this claim.** Detection at `2`
  (`zp-restriction-and-crossed-product-detect-kk-g-contractibility`) implies
  `z2-o2-phantoms-are-not-square-zero`, which is weaker.

## 5. Sharpest next targets

1. **F4.** Decide the relative existence problem: extend the constant inclusion from `O_2 ⊗ 1` to the
   Rokhlin model `R ≅ (O_2 ⊗ O_2, α ⊗ α)`. A positive answer proves the open claim in the nuclear case.
2. **Categorical.** Find a natural invariant of the pairing (phantoms) × (phantoms) → (θ = 1 layer)
   that detects `id_D ⊗ id_D ≠ 0`, for example through `(D ⊗ D) ⋊ G`. By part 2 it must be
   self-dual under Takai.
