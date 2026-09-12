# The two-root defect decides every Sylvester rank function on the Leavitt unit group algebra

Lane `w4-rankfn`, 2026-09-12. Supports:
- `leavitt-rank-functions-killing-two-root-defect-are-augmentation` (established on paper, verification
  requested from `w3-vf-linear`);
- the open claim `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`;
- the open target `binary-leavitt-units-carry-nonaugmentation-rank-function`.

Cited: [TRI] = `research/artifacts/el3-two-root-identities-2026-09-12.md`,
[RR] = `research/artifacts/el3-rank-ring-rigidity-2026-09-12.md`,
[DI] = `research/artifacts/binary-cyclic-corner-rank-function-dichotomy-2026-09-12.md`.

## 0. Setup

- `K` is a field of characteristic `p > 0`, `R = L_K(1,2)` and `Γ = R^x`.
- The three-leaf prefix code gives a ring isomorphism `M_3(R) ≅ R`, so `Γ ≅ GL_3(R)`, and
  `GL_3(R) = EL_3(R)` by `leavitt-gl-equals-el-and-perfect-unit-group` (every field). Fix this
  identification. `x_ab(r)` in `Γ` is the image of the elementary matrix.
- In `K[Γ]` put `N_ab = [x_ab(1)] - 1` and the *two-root defect* `D = N_23 N_12`.
- Sylvester matrix rank functions and the augmentation rank `rk_ε` are as in [DI] Section 1.
- In characteristic two, `N_12^2 = [x_12(2)] - 2[x_12(1)] + 1 = [1] + 1 = 0` exactly in `K[Γ]`.
- `π : K[Γ] -> R` is the evaluation. `π(D) = e_23 e_12 = 0` in `M_3(R)`, so `D` lies in `ker π`.

## 1. Theorem 1

**Theorem 1.** Let `rk` be a Sylvester matrix rank function on `K[Γ]`. Then `rk = rk_ε` iff
`rk(N_12^2) = 0` and `rk(D) = 0`. When `p = 2` the first condition always holds, so `rk = rk_ε` iff
`rk(D) = 0`.

*Proof.* If `rk = rk_ε`: both elements lie in the augmentation ideal, so their rank is `0`.

Conversely, suppose both ranks vanish.
1. **Quotient.** `I = {x : rk(x) = 0}` is a two-sided ideal, `rk` descends to a Sylvester matrix rank
   function `rk_B` on `B = K[Γ]/I`, and `rk_B(x) > 0` for `x != 0` ([DI] Remark 1.2). `B` is a
   `K`-algebra of characteristic `p`. The quotient map gives a group homomorphism
   `σ : EL_3(R) = Γ -> B^x`, and `σ(x_ab(1)) - 1` is the image of `N_ab`. So `N_12^2 = 0` and
   `N_23 N_12 = 0` hold in `B`.
2. **Matrix units.** [TRI] Theorem A is stated and proved for arbitrary unital rings. With `M = B` it
   gives pairwise orthogonal idempotents `p_i = N_ij N_ji` and `σ(x_ij(1)) = 1 + u_ij` with
   `u_ij in p_i B p_j`, `u_ij u_jk = u_ik` and `u_ij u_ji = p_i`.
3. **A unital ring homomorphism into the first corner.**
   - *`p = 2`.* [RR] Proposition 6 is stated for an arbitrary ring of characteristic two. It gives a
     unital ring homomorphism `C : R -> p_1 B p_1`.
   - *`p` odd.* [RR] Proposition 8 is stated for a rank ultraproduct, but its proof uses only:
     - [RR] Lemma 1 (`(1 + n)^p = 1 + n^p` in a ring of characteristic `p`);
     - exact commutation and commutator relations of `EL_3(R)`;
     - torus and Weyl elements of `SL_3(F_p) <= EL_3(R)`;
     - invertibility of `2 + D` for a nilpotent corner element `D`.
     All of these hold in `B`. The computation of [RR] Corollary 9 (additivity,
     `[1+X, 1+Y] = 1+XY` for block-supported `X`, `Y`, and `C(a) = ψ_12(a) u_21`) is ring algebra. So
     `C : R -> p_1 B p_1` exists again.
4. **The corner has no room.** Suppose `p_1 != 0`, so `r = rk_B(p_1) > 0`.
   - For matrices `X` over `p_1 B p_1`, `rk'(X) = rk_B(X)/r` is a Sylvester matrix rank function on the
     ring `p_1 B p_1` with unit `p_1`. Each axiom is an instance of the same axiom for `rk_B`, and
     `rk'(p_1) = 1`.
   - Pulling back along `C` gives a Sylvester matrix rank function `rk''` on `R`.
   - In `R`, `t_i s_i = 1` gives `rk''(s_i t_i) >= rk''(t_i s_i t_i s_i) = 1`. The idempotents
     `s_0 t_0` and `s_1 t_1` are orthogonal with sum `1`, so ([DI] 2.1)
     `1 = rk''(1) >= rk''(s_0 t_0) + rk''(s_1 t_1) = 2`. Contradiction. So `p_1 = 0`.
5. **Triviality.** [TRI] Theorem D.2 is ring algebra.
   - `p_1 = 0` gives `u_1j = p_1 u_1j = 0` and `u_i1 = u_i1 p_1 = 0`, so `u_ij = u_i1 u_1j = 0` and
     `σ(x_ij(1)) = 1` for all `i != j`.
   - `ker σ` is normal and contains `x_ij(a) = [x_ik(a), x_kj(1)]` for every `a`, hence every root
     element, hence `EL_3(R) = Γ`.
   - So `rk(1 - [g]) = 0` for every `g`, and [DI] Theorem 1.1(3) gives `rk = rk_ε`. QED

**Remarks.**
- No simplicity of `Γ` or of `R` is used; `Γ = EL_3(R)` replaces it.
- `reversed-root-pair-identity-forces-root-squares-to-vanish` (lane `w4-r4-adversary`, on paper) would
  make the first condition automatic in every characteristic. Theorem 1 does not use it.
- The proof uses characteristic `p` through exact unipotence. It says nothing over `Q` or `C`.

## 2. Consequences

**Corollary 2 (binary case).** For `K = F_2`, `rk != rk_ε` iff `rk(D) > 0`. With
`simple-group-rank-functions-are-augmentation-or-detecting` and simplicity of `R^x`, a Sylvester rank
function on `F_2[R^x]` detects every nontrivial element iff it gives the defect `D` positive rank.

**Corollary 3 (the target is one element's rank).** `binary-leavitt-units-carry-nonaugmentation-rank-function`
holds iff some Sylvester matrix rank function on `F_2[R^x]` has `rk(D) > 0`. Its negation is the open
claim `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`. Either binary averaging target
implies that negation ([DI] Corollary 1.3).

**Corollary 4 (the Sylvester gate implies the ultraproduct gate).** Suppose every Sylvester matrix rank
function on `F_2[R^x]` kills `D`.
- Let `M` be a rank ultraproduct over a field of characteristic two and `σ : R^x -> M^x` a
  homomorphism.
- The `F_2`-linear extension of `σ` is a ring homomorphism `F_2[R^x] -> M`. The normalized rank of `M`
  pulls back to a Sylvester matrix rank function, which kills `D`, so by Theorem 1 it is `rk_ε`.
- The rank of `M` is faithful, so `σ(g) = 1` for every `g`. Every characteristic-two rank model of
  `R^x` is trivial, `R^x` is not `F_2`-linear sofic, and `non-linear-sofic-group` follows (route
  `non-linear-sofic-via-sylvester-two-root-gate`).
- The converse needs every Sylvester rank function on `F_2[R^x]` to be a limit of matricial ones,
  which is not known.

**Corollary 5 (which gate tools transfer).** A gate argument proves the stronger Sylvester gate, and so
decides the target, when it uses only exact relations of `R^x`, ring identities in the model ring, and
the Sylvester axioms with faithfulness on elements.
- *Checked by this lane:* [TRI] Theorem A and Theorem D.2; [RR] Lemma 1, Proposition 6, Proposition 8
  and the computation of Corollary 9. Also `toeplitz-isometry-defects-have-total-rank-at-least-one`,
  which is stated for any unital ring with a Sylvester matrix rank function.
- *Not transferable as they stand:* arguments using images or range idempotents, Fitting
  decompositions, idempotent lifting, rounding to genuine representations, or matrix-level
  approximation. `B` need not be regular.

## 3. Non-matricial sources: an audit (sketches; no node depends on this section)

A counterexample to the open claim is a Sylvester rank function on `F_2[R^x]` giving `D` positive rank.
`D` lies in `ker π`.

**3.1 Rank completions of locally matricial algebras.** Von Neumann's continuous ring over `F_2` (the
rank completion of `∪_n M_(2^n)(F_2)`) and metric ultraproducts of matrix algebras are matricial.
- Every element is a rank limit of matrices.
- If `rk(ab - 1) <= δ` for matrices `a`, `b`, then `a` is within normalized rank `δ` of an invertible
  matrix: map `ker a` isomorphically onto a complement of `im a`.
- So a homomorphism of `Γ` into their units, keeping nontrivial elements at positive rank distance from
  `1`, gives an `F_2`-linear sofic approximation. Nothing beyond linear soficity.

**3.2 Følner compressions of permutation modules.** Let `Γ` act on a set `X` with Følner sets `F_n`.
- Compressing the permutation representation to `F_2^(F_n)` and taking ultralimits of normalized rank
  gives a Sylvester matrix rank function, because boundary terms have rank `o(|F_n|)`.
- Its approximants are partial permutation matrices, and `rank(P - 1)` is at most the number of moved
  points. So detecting `g` means `g` moves a proportion `κ > 0` of `F_n`.
- Diagonal powers `F_n^k` bring the fixed proportion down to `(1 - κ + o(1))^k`, which gives sofic
  approximations.
- For `R^x` this contradicts `openai-leavitt-unit-nonsofic`. The same holds for any construction whose
  approximants are partial permutation matrices.

**3.3 Modules through the evaluation.** Every `R`-module (`C(X, F_2)`, the modules on tail-equivalence
classes, `R` itself) acts through `π`.
- A rank function vanishing on `ker π` descends to `π(F_2[Γ]) = R`. The evaluation is onto: in
  `M_2(R) ≅ R`, `e_11(a) = e_12(a) e_21(1)` with `e_12(a) = x_12(a) - 1`
  (`research/artifacts/leavitt-ring-rank-approximability-collapse-2026-09-12.md`, Corollary 7).
- `R` has no Sylvester rank function ([DI] 2.1), so this source is dead.
- Theorem 1 sharpens it: the rank function must see the specific kernel element `D`.

**3.4 Diagonal tensor powers: an open handle.** For an `R`-module `W`, `[u] -> u (x) ... (x) u`
(`n` factors) represents `F_2[Γ]` on `W^(x)n`, not through `π`.
- For `W = C(X, F_2)`, `V <= Γ` acts on `C(X^n, F_2)` through the diagonal action on `X^n`.
- *Densities are dead:* a compression along almost-invariant pieces needs a `V`-almost-invariant
  density on `X^n`. A `V`-invariant probability measure on `X^n` would push forward to one on `X`,
  and none exists.
- *`D` is nonzero here.* For `n = 2` and `W = R^3`, write `x_ab(1) = 1 + e_ab`. Then `D` acts by
  `e_23 (x) e_12 + e_12 (x) e_23`, since every other cross term has a factor `e_23 e_12 = 0`. Compare
  the natural tensor dual model of `EL_3(F_2[t])` in [TRI] Section 4, where `D` is also nonzero.
- No rank function is known on this image, and no obstruction.

**3.5 Characteristic zero.** Over `C`, von Neumann dimension gives a detecting rank function on `C[Γ]`
for every group ([DI] 2.5, literature, not re-read).
- For an integral matrix, rank over `F_2` is at most rank over `Q`. So characteristic-zero ranks bound
  mod-two ranks of integral lifts from above only.
- Approximation theorems that would produce a limit need finite models.
- No transfer is known.

**What a construction must do.** Give `D in ker π` positive rank; use approximants that are not partial
permutations (3.2); use no densities for `V` (3.4); not factor through `R` (3.3).
