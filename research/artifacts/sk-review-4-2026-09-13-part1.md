# SK review 4, part 1: the RF embedding theorem, and the note's proof over finitely generated groups

Lane `sk-verify-4`, 2026-09-13. Second independent review. I re-derived every step on paper before reading
sk-verify-3's verdicts (`sk-review-3-2026-09-13-part3.md` §A); where both reviews exist, the verdicts agree.
Sources read on main at tip 9d88f1dcda:
- nodes landed in 3bcc003284 and e3d0976807;
- `research/artifacts/sk-universal-embedding-a-rf-embedding-2026-09-13.md`;
- `research/artifacts/sk-general-actions-a-finite-subshift-limits-2026-09-13.md`;
- the reviewed inputs `rf-toeplitz-subshifts-over-residually-finite-groups`,
  `residually-finite-group-toeplitz-elementary-groups-lef-kazhdan`,
  `minimal-effective-steinberg-algebras-have-scalar-centre` and `perfect-unit-subgroups-elementary-proof`.

## 0. Verdicts

| Claim | Route | Verdict |
|---|---|---|
| `rf-groups-embed-in-simple-kazhdan-lef-groups` | `-proof` | PASS (concurs with sk-verify-3) |
| `rf-groups-lie-in-derived-subgroups-of-rf-groups` | `-proof` | PASS (concurs) |
| `ore-even-permutations-are-commutators` | `-citation` | PASS as import; metadata Crossref-verified, scan not re-read |
| `rf-toeplitz-subshifts-act-freely` | `-proof` | PASS (concurs) |
| `shift-unit-of-subshift-crossed-product-is-not-elementary` | `-proof` | PASS (concurs) |
| `finite-model-subshift-elementary-groups-simple-kazhdan-lef` (Theorem G) | `-proof` | PASS (first review) |
| `free-subshift-with-finite-models-forces-rf-group` (Proposition N) | `-proof` | PASS (first review) |
| `rf-groups-have-free-minimal-subshifts-with-finite-models` (Proposition E) | `-proof` | PASS (first review) |

No FAIL and no GAP. §1–§8 record the checks and three wording notes.

## 1. Shift unit is not elementary (Proposition 1)
- The orbit representation respects `ufu^(-1) = f∘T^(-1)`: `ufu^(-1)δ_t = f(T^(t-1)x)δ_t = (f∘T^(-1))δ_t`.
- Bounded propagation makes `Pa(1−P)` and `(1−P)aP` finite rank. `Pa^(-1)P·PaP = P − Pa^(-1)(1−P)aP`, and symmetrically, so
  `PaP` is invertible modulo finite rank, with finite-dimensional kernel and cokernel.
- The algebraic index over a field is additive under composition and invariant under finite-rank perturbation.
  With `PabP = PaP·PbP + Pa(1−P)bP`, `ind` is a homomorphism `GL_n(R) → Z`.
- `P` commutes with the matrix units, so `(P rE_ij P)^2 = P r P r E_ij E_ij P = 0`, and `ind(e_ij(r)) = 0`.
- The unilateral shift has index `−1`.

PASS. Only a nonempty `X` is used.

## 2. Ore 1951 Theorem 1
- Crossref (checked today): O. Ore, *Some remarks on commutators*, Proc. Amer. Math. Soc. 2 (1951), no. 2,
  307–314, doi 10.1090/S0002-9939-1951-0040298-4.
- The quoted statement, "every element of A_n is a commutator of Σ_n", is the standard attribution of this paper.
- The AMS landing page returned 403 to my fetch, so I did not re-read the scan.

PASS as import. The claim is used only for finite sets `Ω_n`.

## 3. Lemma 2 (overgroup of commutators)
- **RF case.**
  - Left multiplication on `Γ/Γ_n × {1,2}` is two copies of one permutation, so it is even.
  - `ρ = (λ_n)` is injective: the kernel of the action on `Γ/Γ_n` is `Γ_n`, and `∩Γ_n = 1`.
  - Ore in each coordinate gives `ρ(s) = [a_s,b_s]` exactly, in every coordinate.
  - `Δ ≤ ∏ Sym(Ω_n)` is residually finite because the coordinate projections separate points.
  - `ρ(S) ⊆ [Δ,Δ]` gives `ρ(Γ) ≤ [Δ,Δ]`. `Δ` is infinite if `Γ` is.
- **LEF case.**
  - Partial models on growing balls give an injective homomorphism into `∏_ω F_n`.
  - The doubled regular representations are even and injective.
  - Representatives `a_(s,n), b_(s,n)` are chosen per coordinate, so `ρ(s) = [a_s,b_s]` holds in the ultraproduct.
  - A f.g. subgroup of an algebraic ultraproduct of finite groups is LEF: finitely many products and inequalities hold in
    ω-almost every coordinate.

PASS.

## 4. Lemma 3 (freeness at every point)
Checked against the construction of Theorem T:
- (F1) `x` is constant on every `Δ_m`-coset except the hole `C_m`, by induction, since `Δ_m`-cosets refine
  `Δ_(m−1)`-cosets.
- (F2) Inside `C_m` there is a `1`-coset and a `0`-coset of `Δ_(m+1)`, because `d_(m+1) ≥ 3`.
- For `y = lim g_k·x`, fix the residue `g_kΔ_(m+1)` along a subsequence. By normality this fixes `g_kC_m`, `g_kE_1` and
  `g_kE_0`. So `D_m(y)` exists and is unique, nested and equivariant.
- `g·y = y` forces `c^(-1)gc ∈ Δ_m`, so `g ∈ Δ_m` for all `m`, so `g = e`.

PASS.

## 5. Theorem E (the embedding)
- **Finite Γ.** Replace it by `Γ × Z`.
- **Envelope.** Corollary T with `q = 2`, `N = 3` over `Δ` (reviewed PASS twice) gives `EL_3(R)/Z` infinite, f.g., simple,
  Kazhdan and LEF.
- **Centre.** Minimal and topologically free makes the transformation groupoid minimal and effective, so
  `Z(R) = F_2`. A central element of `EL_3(R)` commutes with `e_ij(1)`, so it is `cI`; commuting with `e_ij(r)` puts
  `c ∈ Z(R)^× = {1}`. The route cites the centre node for this step. The one-line passage from `Z(R)` to
  `Z(EL_3(R))` is not written out; it is routine.
- **Whitehead.** I multiplied out `e_12(c)e_21(−c^(-1))e_12(c) = [[0,c],[−c^(-1),0]]`, then `w(c)w(−1) = diag(c,c^(-1))`, and
  `diag(a,a^(-1))diag(b,b^(-1))diag((ba)^(-1),ba) = diag([a,b],1)`.
- **Embedding.** `δ ↦ u_δ` is injective. `ψ(γ) = diag(u_(ρ(γ)),1,1)` is a homomorphism, and it lies in `E_3(R)` because
  `ρ(γ)` is a product of commutators in `Δ`.
- **Self-contained proof over Δ (artifact §4, Proposition 5).**
  - The tower product rule and both absorption formulas hold.
  - `Δ_M ∩ F^(-1)F = {e}` separates the supports of the `P_g`, by normality of `Δ_M`.
  - `D(f)δ_(hΔ_M) = f(h·p)δ` is well defined because `p` is `Δ_M`-invariant.

PASS.

## 6. Theorem G (the note's proof over a f.g. group)
- **Step 1.**
  - `u_γe_au_γ^(-1)` is the indicator of `{z : z(γ^(-1)) = a}`, for the action `(γx)(h) = x(hγ)`.
  - Cylinders span `LC`.
  - `S` is symmetric, so `u_t^(-1)` is among the generators. EJZ gives (T).
- **Step 2.**
  - `e_Ure_U = e_U` for a small clopen `U`, using freeness at the chosen point; translates cover `X` by minimality.
  - A central `r` has `f_γ = 0` for `γ ≠ e`: `(e_V − e_(γV))(x) = 1` when `x ∈ V`, `γ^(-1)x ∉ V`. `f_e` is invariant, hence
    constant.
- **Step 3.**
  - `P_γD_Y(f)P_γ^(-1)δ_z = f(γ^(-1)z)δ_z = D_Y(f∘γ^(-1))δ_z`, provided `F` contains the window of `f` and its shift
    `Fγ^(-1)`, as stated.
  - The compactness fact gives no fixed points of `g ∈ E^(-1)E \ {e}` on `Y`, so the `γz`, `γ ∈ E`, are distinct. The
    coefficient of `δ_(z')` isolates `f_(γ_0)`.
- **Step 4.**
  - `E_(γδ)E_(γ'δ') = δ_(δγ')E_(γδ')`, since `γW ∩ γδ^(-1)γ'W' ⊆ γδ^(-1)(δU ∩ γ'U)`.
  - Absorption: left by `σ` moves the first index, and right by `τ` gives `τ^(-1)δ`.
- **Step 5.**
  - A partition with `C ∩ γC = ∅` for `γ ∈ B_(2w+2) \ {e}` exists by freeness at every point and compactness, and
    refines the letter partition.
  - The subring argument needs the roots `e_C` and `e_Cu_t`, `t ∈ S` symmetric.
  - `B' = B_1 ∪ B_wB_1 ∪ B_w^(-1)B_1 = B_(w+1)`, and `γC`, `γ ∈ B_(w+1)`, are disjoint because `γ^(-1)δ ∈ B_(2w+2)`.
  - The rest is the note's extraction verbatim: `d = n|B_(w+1)| ≥ 3`, the display for transvections inside one column,
    the level ideal with `R` simple.

PASS.

## 7. Proposition N (finite models force residual finiteness)
- Freeness makes the clopen sets `{x(h) ≠ x(hγ)}` cover `X`; take a finite subcover indexed by `F`.
- Every `y` in a finite model on `F ∪ Fγ` agrees there with some `x`, so `γy ≠ y`. `Γ → Sym(Y)` does not kill `γ`.
- The action `(γx)(h) = x(hγ)` is a left action.

PASS.

## 8. Proposition E (nested-hole Toeplitz subshift)
- **Key identity.** `x(hk) = x(h)` for `h ∉ K_n`, `k ∈ K_n`: `hk` has the same level `ℓ(h) < n` and the same
  `K_(ℓ(h)+1)`-coset.
- **(a) Finite models.**
  - A window `Fσ` meets `K_n` at most once, by normality.
  - `y_b` is `K_n`-invariant.
  - The two inclusions of pattern sets hold because `h_0σk` runs over `K_n`.
- **(b) Minimality.** The return sets contain cosets `σK_n`, `σK_(m+1)`, or `σκ_1K_(n+1)`, all syndetic. An almost periodic
  point has a minimal orbit closure.
- **(c) Freeness.**
  - `m = ℓ(σ^(-1)γσ) = ℓ(γ)` by normality, so `m`, `n` and `T` depend only on `γ`.
  - At most one of the two special cosets equals `g^(-1)K_(m+1)`.
  - For the other, `ρg` lies in a different level-`m` coset, so `x(ρg) ≠ x(ρ)`.
  - `n > m` gives `K_n ⊆ K_(m+1)`, so `κK_(m+1)σ^(-1)` is a union of `K_n`-cosets and meets `T`.
  - Limits over the finite `T` give `γz ≠ z` for all `z ∈ X`.

PASS.

**Wording notes (no status change).**
1. In the node `rf-groups-have-free-minimal-subshifts-with-finite-models`, the summary "For `γ ∉ K_n`, let `m` be the level of
   `σ^(-1)γσ`" would read better as "the level of `γ`": the levels agree by normality.
2. The route `rf-groups-embed-in-simple-kazhdan-lef-groups-proof`, step 3, could add one clause, "so central matrices are
   scalar", before citing the centre node.
3. Theorem G, Step 3, silently uses that `Y` is invariant under the listed `γ`. It is, since `Y` is a subshift.

## 9. For the note
- Theorem E and Theorem G are both ready as corollary material.
- Theorem G contains the note's theorem (`Γ = Z`, return words).
- Theorem E needs Kionke–Schesler credit for the version without (T), as recorded on the claim node.
