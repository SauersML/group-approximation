# sk-orthogonality-o part 2: Frobenius bicommutants prove (O), (O′) and the Singer identities (2026-09-14)

Lane sk-orthogonality-o. Notation as in `research/artifacts/sk-orthogonality-o-2026-09-14-part1.md` §0. Everything here
is UNREVIEWED. Imports:
- O1 = `subshift-gl3-index-kernel-is-elementary-group` (unreviewed), used for both `X` and `Y`: every element of
  finite order of `GL_3(R)` lies in `EL_3(R)`;
- C2 of `subshift-elementary-group-rigid-supports-are-mutual-centralizers` (PASS);
- the first-return corner isomorphism `e_VR_Xe_V ≅ LC(V,F_2)⋊_{T_V}Z`, flagged in sk-normalizer-recognition part 1
  (standard, not source-checked), so `Z(e_VR_Xe_V) = F_2e_V` and `e_VR_Xe_V` is simple.

**Lemma Z (square-zero commutants).** Let `S` be a simple ring with centre `F` and let `f` be an idempotent with
`f ≠ 0, 1`. If `x ∈ S` commutes with `fS(1−f)` and `(1−f)Sf`, then `x ∈ F`.

*Proof.* Write `x` in Peirce blocks.
- From `xn = nx` for `n ∈ fS(1−f)`: `x_{(1−f)f}·fS(1−f) = 0`. Fullness of `1−f` gives `x_{(1−f)f} = 0`. Symmetrically
  `x_{f(1−f)} = 0`.
- Then `x_{ff}n = nx_{(1−f)(1−f)}` and `x_{(1−f)(1−f)}m = mx_{ff}` for `m ∈ (1−f)Sf`. Since `fSf = fS(1−f)Sf`,
  `x_{ff}` is central in `fSf`, so `x_{ff} = λf` with `λ ∈ F`. Likewise `x_{(1−f)(1−f)} = λ′(1−f)`.
- `λn = λ′n` for all such `n`, so `λ = λ′`. ∎

## 1. The X-side bicommutant

**Lemma X.** Assume O1 for `X`. For every nonempty clopen `V`, `C_{G_X}(C_{G_X}(F21_V)) = Q_V`.

*Proof.*
- `Q_V` commutes with `C_{G_X}(F21_V)`. Indeed, `F21_V` acts on `M_X = R_X³` with isotypic parts `e_VM_X` (type `3`)
  and `e_{X∖V}M_X` (trivial), and `End_{F21}(3) = F_2`. So every `g ∈ C_{G_X}(F21_V)` is `rI_3` on `e_VM_X`, with
  `r ∈ (e_VR_Xe_V)^×`, and arbitrary on `e_{X∖V}M_X`.
- Conversely, let `x ∈ CC(F21_V)`.
  - `x` commutes with `G_{X∖V} ⊆ C(F21_V)`, so `x ∈ G_V` by C2.
  - For orthogonal nonzero idempotents `f + f′ = e_V` of `R_V := e_VR_Xe_V` and `n ∈ fR_Vf′`, the element
    `(e_V + n)I_3 ⊕ I` has order 2. So it lies in `G_X` by O1, and it commutes with `F21_V`.
  - So every entry of `x − I` commutes with `fR_Vf′` and `f′R_Vf`. By Lemma Z it lies in `F_2e_V`. So `x ∈ Q_V`. ∎

## 2. Theorem C: the Y-side bicommutant is one natural block

Let `T_t` (`t ∈ {1,2,3,3*}`) be the isotypic idempotents of `K_V = α(F21_V)` on `M = R_Y³`. They lie in
`span_{F_2}K_V`. Write `M_t = T_tM`, so that `M_3 ≅ 3 ⊗ P_3`, `M_{3*} ≅ 3* ⊗ P_{3*}` and `M_2 ≅ 2 ⊗_{F_4} P_2`.

**Theorem C.** Assume O1 for `X` and `Y`. For every nonempty clopen `V` there is exactly one `t_V ∈ {3, 3*}` with
`M_{t_V} ≠ 0`, and `M_2 = 0`. Moreover:
- `α(Q_V)` acts trivially on `Fix(K_V) = M_1`;
- `α(Q_V)` acts on `M_{t_V} = t_V ⊗ P` as `ψ_V(q) ⊗ id_P`, for an isomorphism `ψ_V: Q → GL(t_V)` extending the
  `F21`-representation `t_V`.

*Proof.*
- By Lemma X, `CC_{G_Y}(K_V) = α(Q_V)` has order 168.
- Every `x ∈ C_{G_Y}(K_V)` commutes with each `T_t`, since they lie in the span of `K_V`.
  - On `M_3`, `x ∈ End_{F21⊗R_Y^op}(3⊗P_3) = id ⊗ End(P_3)`.
  - Likewise on `M_{3*}`, and on `M_2` it is `F_4`-linear.
- So for `a ∈ GL_3(F_2)` the element `g_3(a) := (a ⊗ id)` on `M_3`, identity elsewhere, commutes with
  `C_{G_Y}(K_V)`. It is `R_Y`-linear and of finite order, so it lies in `G_Y` (O1). So `g_3(a) ∈ CC_{G_Y}(K_V)`. The
  same holds for `g_{3*}(a)`, and for `g_2(ω)`, which is multiplication by `ω ∈ F_4^×` on `M_2`.
- `α(c_V) ≠ I` acts trivially on `M_1 ⊕ M_2`, so `M_3 ⊕ M_{3*} ≠ 0`. If both `M_3, M_{3*} ≠ 0`, or if `M_2 ≠ 0`, then
  `CC_{G_Y}(K_V)` contains `GL_3(2)²` or `GL_3(2) × C_3`, which has order greater than 168. So exactly one `t_V`
  occurs and `M_2 = 0`.
- Now `g_{t_V}(GL_3(2)) ⊆ CC_{G_Y}(K_V)`, and both have order 168, so they are equal. That is the displayed form, and
  `ψ_V|_{F21} = ρ_{t_V}` because `K_V ⊆ α(Q_V)` acts as `ρ_{t_V} ⊗ id`. ∎

## 3. Consequences

**Lemma S3.** `3 ⊗ 3` is not a semisimple `F_2GL_3(2)`-module, and neither is `3* ⊗ 3*`.

*Proof.*
- The symmetric tensors `Sym ⊆ 3⊗3` have dimension 6 and contain `Λ = span{v⊗w + w⊗v} ≅ Λ²(3) ≅ 3*`. The map
  `v ↦ v⊗v mod Λ` is additive and gives `Sym/Λ ≅ 3`.
- If `Sym = Λ ⊕ L` for a submodule `L`, then `s: 3 → L` with `s(v) ≡ v⊗v` defines an equivariant quadratic map
  `q(v) = s(v) + v⊗v ∈ Λ` whose polarization is `v⊗w + w⊗v`.
- `q(e_1)` is fixed by `Stab(e_1) = {[[1,b^t],[0,A]]}`, which has no nonzero fixed vector on `3*`. So `q(e_1) = 0`, and
  by transitivity `q = 0`. Then the polarization vanishes, a contradiction.
- `3*⊗3*` is the image of `3⊗3` under the graph automorphism. ∎

**Corollary O.** Assume O1. Then `S_VS_W = 0` for disjoint clopen `V, W`.

*Proof.*
- `α(Q_W)` commutes with `α(Q_V)` and `K_V`, so it preserves `M_{t_V}(V) = t_V ⊗ P` and acts as `id ⊗ σ`.
- So the joint piece `N = S_VS_WM` is a `Q × Q`-module `t_V ⊠ t_W ⊗ P_N` (Theorem C at `V` and at `W`).
- The diagonal `α(Q_{V⊔W})` acts on `N` as `(t_V ⊗ t_W) ⊗ id`. By Theorem C at `V⊔W`, `M` is a semisimple
  `α(Q_{V⊔W})`-module with constituents `1` and `t_{V⊔W}`, and so is its submodule `N`.
- But `3⊗3` and `3*⊗3*` are not semisimple (Lemma S3), and `3⊗3* ≅ 1 ⊕ 8` contains `8`. So `N = 0`. ∎

**Corollary O′.** Assume O1. Then `S_X = I`.

*Proof.*
- By Corollary O and Proposition F item 1 (additivity), `S_X = S_V + S_{X∖V}`. So `E := I − S_X ≤ I − S_V` for every `V`.
- `α(Q_V)` is trivial on `(I−S_V)M ⊇ EM` (Theorem C). It commutes with `S_V` and `S_{X∖V}`, so it preserves `S_XM`.
- So `α(L_X)`, which is generated by the `α(Q_V)`, is block diagonal for `M = EM ⊕ S_XM` and trivial on `EM`.
- For `n ∈ EM_3(R_Y)E` with `n² = 0`, the element `I + n` commutes with `α(L_X)`, and it lies in `G_Y` by O1. But
  `C_{G_Y}(α(L_X)) = α(C_{G_X}(L_X)) = 1`, so `n = 0`.
- If `E ≠ 0`, Theorem DP splits `E` into two nonzero orthogonal idempotents `f, f′`, and simplicity gives
  `0 ≠ fM_3f′ ∋ n` with `n² = 0`. So `E = 0`. ∎

**Corollary T (constant orientation).** `t_V = t_X` for every nonempty clopen `V`.

*Proof.* By Corollaries O and O′, `S_VM = Fix(K_{X∖V})`. `α(Q_{X∖V})` is trivial there (Theorem C), so `α(Q_X)` acts on
`S_VM` as `α(Q_V)`, of type `t_V`. By Theorem C at `X`, only `t_X` occurs. ∎

## 4. Theorem D

**Theorem D.** Assume O1. Let `X, Y` be infinite minimal subshifts. Then every isomorphism `α: G_X → G_Y` is
standard, possibly after composing with the graph automorphism `γ_X`. So `G_X ≅ G_Y` implies that `X` and `Y` are
strongly orbit equivalent.

*Proof.*
- If `t_X = 3*`, replace `α` by `α∘γ_X`. Then `ψ_V` is inner-type, so `K_V` has type `3` on `S_VM`.
- By Theorem C (no type 2) and Corollary T, `K_V` acts on `S_VM` with type `3` only. That is (Sing_V) (Lemma 0 of
  part 1), for every `V`.
- (O′) is Corollary O′.
- Theorem A (`singer-identities-make-subshift-el3-isos-standard`) gives standardness and strong orbit equivalence. ∎

This answers the question in `simple_kazhdan_sofic_group.tex` (§4, "Does `G_X ≅ G_Y` imply that `X` and `Y` are
strongly orbit equivalent?"), conditional on O1. It proves `subshift-el3-isomorphisms-are-standard-over-f2` and (Rec′)
under the same condition.

**Model tests.**
- `α = id`: `t_V = 3`, `P = e_VR`, `Fix(K_V) = e_{X∖V}M`.
- `α = inn(d)`, `d = diag(u,1,1)`: `Fix(K_V) = d·e_{X∖V}M`, the natural block is `d·e_VM`, and `t_V = 3`; (O) and (O′)
  hold.
- `α = γ_X`: `t_V = 3*` for all `V`.
- **Petechuk's product case** (`R = R_1 × R_2`, identity on one factor and graph automorphism on the other): Lemma X
  fails there. `R` is not simple, `Z(R) ≠ F_2`, and `CC(F21)` contains both orientations, which is exactly where the
  counting of Theorem C would break.
- **Where each hypothesis is used.**
  - O1 on `X` in Lemma X;
  - O1 on `Y` for `g_t(a) ∈ G_Y` and in Corollary O′;
  - simplicity of `R_Y` in Lemma Z and Corollary O′;
  - `Z(R_Y) = F_2` in Lemma Z.

**Credit.**
- The support idempotents `S_V`, Lemma D and Proposition F are sk-normalizer-recognition's.
- The index kernel theorem is sk-free-10's; Theorem R and Theorem P are sk-iso-rigidity's; the rigid supports are
  sk-rigidity-intrinsic's.
- The double-centralizer counting and Lemma S3 are standard modular representation theory (the non-split symmetric
  square in characteristic 2). No literature search on automorphisms of `E_3` over crossed products was made beyond
  main's graph.
