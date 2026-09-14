# sk-orthogonality-o: plan (2026-09-14)

Lane sk-orthogonality-o (wave 12). Targets: the hypotheses (O) and (O′) of
`frobenius-support-idempotents-give-boolean-realization`, then the step (A2) from there to (Rec′),
`subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer`. This is a plan artifact. The facts in §2 are
checked by hand here and will be written with full proofs in part 1, unreviewed until a verifier PASS.

## 1. Setting

- `X, Y` infinite minimal subshifts, `R_Y = LC(Y,F_2) ⋊ Z`, `G_Y = EL_3(R_Y)`, `M = R_Y^3`, `α: G_X → G_Y` an
  isomorphism.
- `Q = GL_3(F_2)`, `F21 = ⟨c, s⟩ ≤ Q` with `c` a Singer cycle (characteristic polynomial `x³+x+1`) and `s` of order 3.
  `q_V ∈ L_X` is `q` on `V` and `I` off `V`. `K_V = α(F21_V)`, `S_V = I + Σ_{k∈K_V} k`.
- `F_2[F21] = F_2 × F_4 × M_3(F_2) × M_3(F_2)` is semisimple (21 is odd). Its simple modules are `1`, `2` (through
  `F21 → C_3`), `3` (natural, `c ↦ ζ` with `ζ³+ζ+1 = 0`) and `3*`. So `M` splits into `K_V`-isotypic parts, and
  `S_V M` is the sum of the `2`, `3`, `3*` parts.
- `F_2[Q]` has simple modules `1, 3, 3*` (principal block) and the Steinberg module `8` (defect zero, projective).

## 2. Facts found while planning

- **F1 (correction).** `8|_{F21} = 2 ⊕ 3 ⊕ 3*`. On the classes `1, 3A, 7A, 7B` of `F21` the Brauer character of `8` is
  `(8, −1, 1, 1)`, and `⟨8|_{F21}, 1⟩ = (8 − 14 + 6)/21 = 0`. So the Steinberg module has NO `F21`-fixed vector. The
  sentence "`1` and `8` do" in §2 of `research/artifacts/sk-normalizer-recognition-plan-2026-09-14.md` is wrong for `8`:
  `[M, α(F21_V)]` may contain Steinberg pieces, and they must be excluded separately.
- **F2 (correction).** `R_Y^×` is not `[[T]]` and is not amenable.
  - For disjoint clopen `V, W` with `V ∩ TW ≠ ∅`, `n = e_V u e_W = e_{V∩TW}u` is nonzero with `n² = 0`. So `1 + n` is
    a unit, and it is outside `[[T]]`: its coefficients at `u^0` and `u^1` have overlapping supports.
  - For pairwise equivalent disjoint clopen `V_1, V_2, V_3`, `R_Y^×` contains `GL_3` of the corner `e_{V_1}R_Ye_{V_1}`,
    so it contains simple Kazhdan groups.
  - So the "type distinction" step of that plan (GL_1-type corners are amenable) does not work.
- **F3 (from sk-free-10 O1, unreviewed).** `G_Y = ker(ind)`. So `G_Y` is normal in `GL_3(R_Y)`, the normalizer
  `N_Y` in (Rec′) is all of `GL_3(R_Y)`, and every element of finite order of `GL_3(R_Y)` lies in `G_Y`. In
  particular, for every idempotent `E`, the Peirce radical `I + E·M_3(R_Y)·(I−E)` lies in `G_Y`.
- **F4.** `Ext¹_{F_2Q}(3,3) = 0 = Ext¹_{F_2Q}(3*,3*)`.
  - `3 ⊗ 3* = End(3) = F_2·I ⊕ sl_3`, since the trace splits (3 is odd).
  - `sl_3` has Brauer character `(9,0,2,2) − (1,1,1,1) = (8,−1,1,1)`, the character of `8`, which is simple. So
    `3 ⊗ 3* ≅ 1 ⊕ 8`.
  - `Ext¹(3,3) = H¹(Q, 1) ⊕ H¹(Q, 8) = Hom(Q,F_2) ⊕ 0 = 0`, since `Q` is perfect and `8` is projective.
- **F5 (types on joint pieces).** For disjoint `V, W`, the commuting groups `K_V × K_W` split `M` into pieces of type
  `(t, t′)`. The diagonal `K_{V⊔W}` acts on a piece as `t ⊗ t′` restricted to the diagonal `F21`:
  - `(3,3) → 3 ⊕ 3* ⊕ 3*` (Brauer value at `7A`: `α² = ᾱ − 1`, where `α = (−1+√−7)/2`);
  - `(3,3*) → 1 ⊕ 2 ⊕ 3 ⊕ 3*` (by F1 and F4);
  - `(2,3) → 3 ⊕ 3`;
  - `(2,2) → 1 ⊕ 1 ⊕ 2`.

## 3. Reduction A: everything follows from a Singer identity

**(Sing_V).** `α(c_V)³ + α(c_V) = S_V`. Equivalently, `K_V` acts on `S_VM` with type `3` only (no `2`, no `3*`). On the
X-side `c_V³ + c_V = e_V I`.

**Reduction A (to be proved in part 1).**
1. (Sing_V) and (Sing_W) for disjoint `V, W`, together with (Sing_{V⊔W}), give (O) for `(V, W)`: the piece
   `S_VS_WM` has type `(3,3)`, and by F5 it would put `3*` into `[M, K_{V⊔W}]`.
2. (Sing_X) and (O′) give `M ≅ 3 ⊗ P` as an `F_2[Q_X] ⊗ R_Y^op`-module, with `P = Hom_{Q_X}(3, M)` projective.
   - Every finite-dimensional `Q_X`-submodule has composition factors in `{1, 3, 3*, 8}`.
   - Restriction to `F21_X` excludes `1` by (O′), and excludes `3*` and `8` by (Sing_X) and F1.
   - F4 makes such modules semisimple.
3. `3[P] = 3[R_Y]` in `K_0(R_Y)`, which is torsion-free, so `[P] = [R_Y]`. With cancellation (import C below),
   `P ≅ R_Y`. So there is `k ∈ GL_3(R_Y)` with `k^{-1}α(q_X)k = q` for all `q ∈ Q_X`.
4. `k^{-1}S_Vk` commutes with `k^{-1}K_Vk` and `k^{-1}K_{X∖V}k`, so it commutes with their diagonal, the constant
   `F21`, whose span is `M_3(F_2)`. So `k^{-1}S_Vk = b_V I` with `b_V` an idempotent of `R_Y`.
5. With (O) and (O′), Proposition F item 2 puts `k^{-1}α(q_V)k − I` in the `b_V`-corner and `k^{-1}α(q_{X∖V})k − I` in
   the `(1−b_V)`-corner. Their product is `q`, so `k^{-1}α(q_V)k = b_Vq + (1−b_V)I`.
6. So `α(L_X) = k·GL_3(𝔅′)·k^{-1}` with `𝔅′ = span{b_V} ≅ LC(X,F_2)`, and `k ∈ N_Y` by F3. This is (Rec′), provided
   `𝔅′` is maximal commutative (import Max below).

**Imports to check.**
- **(C)** `P ≅ R_Y`. `P` is a direct summand of `R_Y^3`. By Theorem DP of `sk-algebraic-putnam` part 2
  (`cantor-crossed-product-idempotents-similar-to-clopen-ones`), `P ≅ ⊕_i e_{W_i}R_Y` for clopen `W_1, W_2, W_3`.
  Then `Σ_i[1_{W_i}] = [1_Y]` in `K^0(Y,T)`. What remains is a division step: clopen sets with this class can be moved
  by `[[T]]` to a partition of `Y` (Glasner–Weiss type; to be checked). Theorem IC item 2 then gives `P ≅ e_YR_Y = R_Y`.
- **(Max)** `C_{R_Y}(𝔅′) = 𝔅′`.
  - By F3 and the trivial centralizer `C_{G_Y}(α(L_X)) = 1`, the algebra `C_{R_Y}(𝔅′)` has no nonzero nilpotent
    element, and its units of index 0 are trivial.
  - Units of nonzero index are not yet excluded.
- **Orientation.** (Sing_V) may hold with `x³+x²+1` on some clopen pieces (the graph twist). The mixed case is to be
  excluded as in Theorem R Step 4 (entry `psq`, simplicity of `R_Y`).

## 4. The obstruction and the attacks

By F5, the only pieces that are consistent with (Sing_X) on the diagonal are of type `(3,1)`, `(1,3)`, `(2,3)` and
`(3,2)`. So the whole problem is to kill:
- **type-2 pieces:** `α(c_V)` acts trivially on them and `α(s_V)` does not;
- **trivial pieces:** (O′);
- **`3*` and Steinberg pieces**, the orientation.

Attacks, in order:
1. **Torsion radicals (F3).**
   - Let `P_V = ε_1(α(c_V))`, the idempotent onto `Fix(α(c_V))`. Put `P_V′ = P_V − (I − S_V)`, the type-2 part.
   - If `P_V′ ≠ 0`, the Peirce radicals of `P_V′` are order-2 subgroups of `G_Y`, normalized by `K_V` and by
     `α(C_{G_X}(F21_V))`.
   - Pull them back to `G_X` and contradict the X-side structure: `C_{G_X}(F21_X) = {rI_3 : r ∈ R_X^×, ind_1(r) = 0}`,
     together with C2–C4 of `subshift-elementary-group-rigid-supports-are-mutual-centralizers`.
2. **Trivial centralizer against (O′).**
   - A trivial `Q_X`-factor at the top or bottom of the principal-block part gives invariant vectors or functionals.
   - The transvections `I + xφ` they produce are torsion, so they lie in `G_Y` by F3.
   - Pass to the limit over `L_X = ⋃ Q^𝒫` (the fixed modules decrease under refinement), and contradict
     `C_{G_Y}(α(L_X)) = 1`.
   - This kills the natural ⊕ trivial fake.
3. **Commuting spans (the named attack).**
   - On `S_VS_WM`, both `α(E3_V)` and `α(E3_W)` act faithfully and commute.
   - Compute `[α(e_12(a)), α(e_23(b))] = α(e_13(ab))` with `a ∈ e_VR_Xe_W` and `b ∈ e_WR_Xe_V`, compressed to the joint
     pieces, and look for a nonzero `psq`-type entry, as in Theorem R Step 4.
4. **One-shot GAP on MSI** to confirm F1, F4 and F5 (`Ext¹` via MeatAxe; the tensor decompositions).

## 5. Landing schedule

- Part 1: proofs of F1–F5 and Reduction A, queued for verification.
- Part 2: attacks 1–3.
- Every failure is recorded as `## Attempts` on the open node.
