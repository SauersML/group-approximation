# EX review wave 2, part 14: the K1 defect-ideal chain (census priority A, 2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0. Census: part 11.

**Blobs** (rechecked at tip `f6aade2836`, lane ex2-k1-defect-ideal):
- `o2-quotient-extension-ideal-k1-injective-iff-algebra` and its `-proof`, at `e1e097e0a`;
- `toeplitz-defect-ideal-connected-iff-extension-k1-injective` and its `-proof`, at `261931f14`;
- `nonzero-fibre-projection-full-under-weak-omega-comparison` and its `-proof`, at `28a12381b`;
- artifacts `k1-defect-ideal-o2-quotient-lifting`, `-z-stable-quotients` and `-corona-converse` (2026-09-13), unchanged.

**Sources checked verbatim** on MSI (`/scratch.global/sauer354/ex/ex-verify2-analysis/`):
- **Jiang**, arXiv:math/9707228: Theorem 2, "Let A be a unital Z-stable C∗-algebra. Then the natural map µ : U(A)/U0(A) →
  K1(A) is an isomorphism", and Theorem 3.
- **Blanchard**, arXiv:0804.4624:
  - Proposition 4.2, "(i) T2 ∗C T2 is K1-injective ... (v) Any unital properly infinite C∗-algebra A is K1-injective";
  - Lemma 4.4, "K0(T2 ∗C T2) = Z and K1(T2 ∗C T2) = 0".
- **Ortega--Perera--Rørdam**, arXiv:0903.2917:
  - Proposition 4.5, quoted as on the route;
  - Proposition 4.8, "Let A be a separable C∗-algebra such that Cu(A) satisfies the weak ω-comparison property and such
    that A ⊗ K contains a full projection. Let B be a full hereditary sub-C∗-algebra of A ⊗ K. Then the following
    conditions are equivalent: (i) B is stable (ii) B has no non-zero unital quotient and no non-zero bounded
    2-quasitrace. (iii) B has property (S)";
  - Proposition 2.21;
  - p. 1, "C(∏ S²) does not have the Corona Factorization Property".

## 14.1 Verdicts

| claim | verdict |
|---|---|
| `z-stable-unital-algebras-are-k1-bijective` (import, established without a PASS) | PASS, Jiang Theorem 2 verbatim |
| `o2-quotient-extension-ideal-k1-injective-iff-algebra` | PASS |
| `toeplitz-defect-ideal-connected-iff-extension-k1-injective` | PASS |
| `nonzero-fibre-projection-full-under-weak-omega-comparison` | PASS |

No false establishment. LXI stays open. The chain makes LXI equivalent to connectivity of `U(I_f~)` and of `U(I_c~)`, and
sandwiches connectivity of `U(J~)` between LXI and LXI minus halving.

## 14.2 Re-derivations

- **Loops in `U(O_2)`.**
  - `C(T) ⊗ O_2` is unital and Z-stable with `K_1 = 0`, so `U` is connected by Jiang.
  - Correcting a path by the constants `c(ev(w_s))^*` keeps it in `U(1 + SO_2)`.
  - For Z-stable `Q` with `K_0(Q) = 0`, a based loop has `K_1`-class in `K_1(SQ) ≅ K_0(Q) = 0`, and the same argument
    applies.
- **Lifting lemma (Proposition 2).**
  - `γ = q∘w` is a based loop, hence a product of exponentials in `(SQ)~`.
  - Self-adjoint lifts exist, because `C_0(0,1) ⊗ −` is exact.
  - `ω = Π exp(ik_k)` has scalar endpoints equal to `γ_0 = 1`. So `ω_t^* w_t` runs from `1` to `u` inside `1 + I`.
- **Corollary 3 / 3'.**
  - (b) follows from the six-term sequence.
  - (c)(⟸): `[u] = 0` in `K_1(I)` gives `u ∈ U_0(B)`, hence `u ∈ U_0(I~)`.
  - (c)(⟹) is `k1-injectivity-extends-over-properly-infinite-quotients` (PASS in part 5 and in ex-review-analysis
    part 3). Re-checked: lift `q(u) ∈ U_0(Q)`, correct by `exp(2πia)` over a projection representing the index class,
    then use K1-injectivity of `I~`.
  - (d) holds since `K_1(I) ≅ K_1(B) = 0`.
  - Admissible quotients: `O_2 ⊗ D ≃_KK 0` for every unital `D`.
- **Applications.**
  - `φ_c` is onto, since `Σ_k (s_k ⊗ z)(s_k^* ⊗ 1) = 1 ⊗ z`.
  - `K_1(A_T) = 0` (Blanchard 4.4). So `U(I_c~)` and `U(I_f~)` are connected iff `A_T` is K1-injective, iff LXI by
    Blanchard 4.2 (i)⟺(v).
- **Lemma 4.**
  - `B_J/J ≅ T_2/ι_1^{-1}(J)`.
  - That ideal contains `p_3`, hence `K`, and misses `1`, because `A_T → O_2 ∗ T_2` kills `e`.
  - The ideals of `T_2` are `0`, `K` and `T_2`, so `B_J/J ≅ O_2`.
- **`K_*(J) = (Z, 0)`.**
  - `A_T/J = O_2 ∗ T_2`, and Germain's sequence gives `K_*(O_2 ∗ T_2) = 0`.
  - So the six-term sequence makes `K_0(J) → K_0(A_T) = Z` bijective and `K_1(J) = 0`.
- **Theorem 5.**
  - (c): LXI makes the unital properly infinite `B_J` K1-injective.
  - (d)(⟸), re-derived without the open route `lxi-from-halving-and-toeplitz-defect-ideal`:
    - halving makes `O_2 ∗ T_2` (unit class `0`) K1-injective, so `U((I_c/J)~)` is connected by Corollary 3';
    - lift a null path through exponentials and finish in `U(1 + J)`;
    - so `U(I_c~)` is connected, and LXI follows.
- **Remark 6.**
  - `ι_1(s_1), ι_1(s_2), ι_2(s_1), ι_2(s_2) ↦ r_1, r_2, r_3, r_2` defines a unital surjection onto `O_3` with
    `e ↦ r_3r_3^*`.
  - `ker π` is invariant under `M(J)`, so `π` extends unitally to `M(J) → O_3`.
  - A unital `O_2` there would force `[1] = 0` in `K_0(O_3) = Z/2`. So `J` also has a unital quotient and is not stable.
- **Proposition 1 (five forms of fullness).**
  - (a)⟹(b) uses fullness and proper infiniteness.
  - (b)⟹(c) and (d)⟹(c) use Kasparov stabilization. For (d)⟹(c), local sections plus compactness give a unit section of
    `F^N`.
  - (e)⟹(b): Gram--Schmidt with an `O(kε)` correction, and Bessel on the tails makes `V: δ_k ↦ η_k` adjointable.
- **Lemma 2.**
  - Ideals of `D_P` correspond to open `U ⊆ X` (Morita equivalence with `C(X)`).
  - A unital quotient is a finite-rank bundle `E` with `E ⊕ E ↪ E`, which is impossible.
  - The isometries `W_i = V_2^i V_1` give `nτ(x) ≤ ‖τ‖‖x‖` for any bounded 2-quasitrace.
- **Theorem 3.** OPR 4.8 applies with `A = C(X)`, full projection `1 ⊗ e_11`, and `B = D_P`.
- **Proposition 4.**
  - `π(J) ⊆ K(E)`, and `P_E` is properly infinite.
  - If `P_E` is full, `K(E)` is stable, so `K(E)~` is K1-injective, and `π_*K_1(J) = 0`.

## 14.3 Notes (no statement changes)

- **Sources not re-read here** (the artifacts flag both): OPR's CFP main theorem and Definition 2.18. The base
  `X = ∏ S²` in "Where a counterexample must live" is a remark, and OPR p. 1 supports it.
- **Graph gap.** `z-stable-unital-algebras-are-k1-bijective` was established with no review. It passes here.
