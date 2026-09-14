# SK review 7, part 1: the density patch and the topological-freeness equivalence

Lane `sk-verify-7`, 2026-09-13. Phase 1 of my brief (ROSTER-F): review the density patch together with sk-strong-4's
equivalence. I derived every step on paper before reading the owners' justifications. sk-verify-4's parts 1–3 on main
do not cover these nodes (they sit at lines 15–16 of its queue), so this is the first review.

Sources on main (tip 123a65eae0):
- `tower-simplicity-holds-for-topologically-free-actions` and its route `tower-simplicity-topologically-free-proof`
  (sk-lef-embedding-e, f21f2493bc, merge f2a36ec309);
- `clopen-towers-at-every-scale-iff-topologically-free` and `binary-el-simple-iff-minimal-topologically-free`, each with
  its `-proof` route (sk-strong-4, c1d34598c8);
- `research/artifacts/sk-strong-4-boundaries-2026-09-13-part1.md` (Lemmas 1, 2, 2′; Propositions 3–5; Theorems 6–7;
  Corollary 8);
- `research/artifacts/sk-lef-embedding-e-proposal-2026-09-13.md` (§1 patch text, §2 corollary text).

## 0. Verdicts

| Node / text | Verdict |
|---|---|
| `clopen-towers-at-every-scale-iff-topologically-free` (+ `-proof`) | PASS |
| `binary-el-simple-iff-minimal-topologically-free` (+ `-proof`) | PASS (backward direction conditional only on the reviewed Steinberg criterion import) |
| `tower-simplicity-holds-for-topologically-free-actions` | PASS + scope repair R1, applied |
| `tower-simplicity-topologically-free-proof` | PASS + typo repair R2, applied |
| sk-lef-embedding-e proposal §1 (patch text for the note) | PASS as mathematics; wording notes W1–W3 |
| sk-lef-embedding-e proposal §2 (corollary text) | PASS as mathematics; compression notes W4–W5 |

No FAIL, no GAP in the mathematics.

## 1. The tower lemma (sk-strong-4 Lemma 1, Lemma 2, Lemma 2′)
- **(1)⇒(2).** `Fix(γ)` is closed because `X` is Hausdorff. A finite union of closed sets with empty interior has empty
  interior, so no Baire argument is needed here. For `x ∈ U \ Y`, zero-dimensionality gives disjoint clopen
  `A_γ ∋ x`, `B_γ ∋ γx`, and `V = U′ ∩ ⋂(A_γ ∩ γ^{-1}B_γ)` is clopen and contains `x`. `V ⊆ A_γ` and `γV ⊆ B_γ` give
  `γV ∩ V = ∅`. Checked.
- **(2)⇒(1).** An `F = {γ_0}`-free nonempty `V ⊆ Fix(γ_0)` would satisfy `γ_0V = V`. Checked.
- **Lemma 2 and 2′.** Atoms of `𝒫` are clopen, so `W ∩ P` is open. A nonzero locally constant `h` has `{h ≠ 0}` nonempty
  open, and `γ^{-1}{h ≠ 0}` contains an admissible `V` with `γV ⊆ {h ≠ 0}`. Checked.
- The remark that the `U = X` form is strictly weaker is correct: take `Γ = Δ × N`, `N` finite acting trivially.

## 2. The noncommuting root (Proposition 3) and the tower group (Propositions 4–5)
- **Commutation criterion.** `(g·rE_{ij})_{pq} = g_{pi} r δ_{jq}` and `(rE_{ij}·g)_{pq} = δ_{pi} r g_{jq}`, so `g`
  commutes with `e_{ij}(r)` iff `g_{pi}r = 0` (`p ≠ i`), `rg_{jq} = 0` (`q ≠ j`) and `g_{ii}r = rg_{jj}`. Checked.
- **Off-diagonal.** `g_{pi}e_V = Σ_γ f_γ e_{γV}u_γ`, uniqueness of coefficients, then Lemma 2′. The first condition alone,
  over all columns `i`, makes `g` diagonal. Checked.
- **Diagonal.** For `γ ∈ B \ {e}`, `γ ∈ B^{-1}B` because `e ∈ B`, so `γV ∩ V = ∅` and both sides of
  `f_γ e_{γV} = e_V h_γ` vanish. Lemma 2′ (with `γ` and with `e`) kills `f_γ` and `h_γ`, and Lemma 2 identifies the
  constant coefficients. Checked.
- **Unit.** If `cb = 1` then `c b_e = 1`, so `c` is nowhere zero, and over `F_2`, `c = 1`. Checked. The trivial centre
  follows.
- **Product rule.** `u_{αβ^{-1}}e_{α′V} = (e_{α′V}∘βα^{-1})u_{αβ^{-1}} = e_{αβ^{-1}α′V}u_{αβ^{-1}}`, and
  `e_{αV}e_{αβ^{-1}α′V} = e_{α(V ∩ β^{-1}α′V)}`, which is zero unless `β = α′`, because `β^{-1}α′ ∈ B^{-1}B`. Checked.
  Injectivity: equal group index with `α ≠ α′` forces disjoint supports `αV`, `α′V`. `ε_{αβ} ≠ 0` needs `V ≠ ∅`, which
  holds because `h ≠ I_n`.
- **Same-block transvections.** `[e_{pp′}(ε_{αβ}), e_{p′p}(ε_{ββ})] = I + ε_{αβ}ε_{ββ}E_{pp} = I + ε_{αβ}E_{pp}`, using
  `ε_{ββ}ε_{αβ} = 0` for `α ≠ β`. Checked.
- **Proposition 5.** `(fu_α)e_V(f′u_β) = f e_{αV}(f′∘α^{-1})u_{αβ}`. `f` is constant on `αV` because `f∘α` is constant
  on `V`, and `f′∘α^{-1}` is constant on `αV` because `f′` is constant on `V` (the case `α = e`). So the product is 0 or
  `ε_{α,β^{-1}}` with `β^{-1} ∈ B` by symmetry. `h^{-1} = h` over `F_2`, `k − I = (ghg^{-1} − h)h`,
  `k^{-1} − I = h(ghg^{-1} − h)`, and `ψ` is injective and multiplicative, so `k ∈ H`. Checked.

## 3. Theorems 6 and 7
- **Theorem 6.** `GL_d(F_2) = PSL_d(F_2)` is simple for `d = n|B| ≥ 3`. The level `J` is a two-sided ideal by the two
  commutator identities with `l ∉ {p,q}`. `⋃_γ γV` is open, nonempty and invariant, so it equals `X` by minimality, and
  compactness gives the finite cover. Checked. No freeness and no infiniteness are used; finite `X` is covered correctly.
- **Theorem 7 (⇒).** The transformation groupoid `Γ ⋉ X` is Hausdorff and ample. It is effective iff the action is
  topologically free, and minimal iff the action is. Its Steinberg algebra is `R`. The reviewed criterion
  `steinberg-algebra-simple-iff-minimal-effective` gives an ideal `0 ≠ I ≠ R`. `EL_n(R,I)` is normal and nontrivial,
  and proper because `EL_n(R) → EL_n(R/I)` is onto and `e_{12}(1) ≠ I_n` in `R/I`. Checked; conditional only on those
  imports.
- **Corollary 8.** A dense free orbit meets any open subset of `Fix(γ)`, which would give a nontrivial stabilizer on
  that orbit. Checked.

## 4. sk-lef-embedding-e's node and route
- **Route steps 1–5.** These agree with Propositions 3–5 and Theorem 6 for `n ≥ 3` and `L` finitely generated, with word
  balls in place of `B`. Step 1 uses Baire for all of `L`; only the finitely many `ℓ ∈ B_{2w}` are needed, but the
  statement as written is correct. Checked.
- **R2 (typo, applied).** Step 3 printed `ε_(ab) ε_(a′b′) = e_(aV) e_(ab^(-1)a′V) u_(ab′^(-1))`. The group index is
  `u_(ab^(-1)a′b′^(-1))`, which becomes `ab′^(-1)` only when `b = a′`; when `b ≠ a′` the product is zero. No verdict
  change.
- **R1 (scope, applied to the claim).** The claim stated that `EL_n(R)` is "an infinite, finitely generated simple
  group" for every finitely generated `L` acting on a Cantor set. Finite generation of `EL_n(R)` needs `R` finitely
  generated: for the odometer `Z`-action, `R` is not finitely generated, so neither is `EL_n(R)`
  (`crossed-product-el-kazhdan-iff-finite-field-and-subshift`, PASS in sk-review-5 part 1). The route already says "`G`
  is finitely generated when `R` is". The claim now reads "infinite and simple, and finitely generated when `R` is (for
  example when `Z` is a subshift over `L`)". The lamplighter host has `R` finitely generated, so the downstream use is
  unaffected.

## 5. Reconciliation with sk-lef-embedding-c's remark
sk-lef-embedding-c's review says the tower argument "cannot be substituted, since the constant configurations are fixed
by every shift, so no clopen partition into ball-separated pieces exists". That is true of the PARTITION form: no
partition of `2^Δ` into small sets exists. The density form reviewed here never partitions `X`. It only needs small sets
inside every nonempty open set, and those exist under topological freeness (Lemma 1). So the remark and this PASS are
consistent, and the manuscript's own tower proof does apply to the lamplighter host.

## 6. The manuscript texts (sk-lef-embedding-e proposal)
**§1 patch (Z case, length neutral): PASS.** Wording notes for the editor:
- **W1.** The paragraph starting "Some $h=e_{ij}(e_V)$ with $V$ small does not commute with $g$. Indeed …" never states
  its contrapositive hypothesis. Add "If $g$ commuted with every such $h$, then …" before "So $g$ is diagonal".
- **W2.** Letter clash: `j` is the matrix index in `g_{jj}` and also the exponent in `\sum_jc_ju^j` and "coefficients at
  $j\ne0$". Use `m` for exponents.
- **W3.** "the coefficients at $0$ agree on every small $V$" needs "hence everywhere, since every nonempty clopen set
  contains a small one". One clause.
- Only the first commutation condition is needed for diagonality. The mirrored statement for `e_V c` is not needed,
  because the diagonal identity is used for both orders of `i, j`. The text is correct as it stands.

**§2 corollary: PASS as mathematics.** The lamplighter chain already has three PASSes (sk-verify-3 part 6,
sk-lef-embedding-c, sk-verify-4 part 2). Compression notes:
- **W4.** "a nontrivial shift moves every configuration that differs at two coordinates it exchanges" is imprecise for
  shifts that are not involutions, and it ignores the lamp part `f` of `ℓ = (δ,f)`. Better: "for `ℓ = (δ,f)` with
  `δ ≠ 1`, every cylinder contains configurations with `x(h) ≠ x(δ^{-1}h)` for some `h` outside the cylinder's window
  and `supp f`, and `ℓ` moves them".
- **W5.** "these models embed $R$ in an ultraproduct" needs the injectivity reason: the map is unital and `R` is simple.
  Simplicity of `R` follows from simplicity of `EL_3(R)`, since a proper nonzero ideal `I` gives the proper normal
  subgroup `EL_3(R,I)` (Theorem 7 ⇒). One clause.
- Checked: doubled regular representations are even; Ore gives commutators in `Alt` coordinatewise; a f.g. subgroup of
  an algebraic ultraproduct of finite groups is LEF; `[L,L] ⊇ [Δ,Δ] ⊇ Γ`; `ℓ ↦ diag(u_ℓ,1,1)` is a homomorphism and
  lands in `EL_3` on `[L,L]` by the Whitehead identity. The false map `diag(a,a^{-1},1)` is not used.

## 7. Scope of this review
Not re-read at source: the Steinberg simplicity criterion, the transformation-groupoid identification (both reviewed
PASS on main), and Ore 1951. No literature search for novelty; that belongs to sk-lit-novelty-2.
