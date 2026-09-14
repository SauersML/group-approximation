# SK review 3, part 4: marked groups of subshift algebras, and ring rigidity

Lane `sk-verify-3`, 2026-09-13. Every step below was re-derived. Main read at tip `18375ec10e`.

## 1. `subshift-algebra-groups-embed-in-marked-groups` (sk-fp-sofic-b, queue item 6)

Route `subshift-algebra-groups-embed-in-marked-groups-proof`, `requires: []`. Artifact
`research/artifacts/sk-fp-sofic-b-z2-soficity-map-2026-09-13.md` §§2–3.
**Verdict: PASS** for items 1–5.

**Item 1 (cylinder words).**
- Each factor u_δ χ_(p(δ)) u_δ^(−1) with |δ| ≤ ρ is a product of at most 2ρ+1 marking coefficients, so χ_[p] is a product of l ≤ |F|(2ρ+1) coefficients.
- The nested commutators e_ij(s_1⋯s_l) = [e_ik(s_1), e_kj(s_2⋯s_l)] use n ≥ 3. Their lengths satisfy L(1) = 1 and L(l) = 2 + 2L(l−1), so L(l) = 3·2^(l−1) − 2, within the stated bound.
- e_12(r) is scalar only for r = 0, and χ_[p] vanishes on Y iff p ∉ L(Y).

PASS.

**Item 2 (window bound).**
- A product of at most r generators has entries that are sums of products of at most r coefficients. So every term is f u_γ with |γ| ≤ r, and f depends on B(r)-patterns.
- Restriction R_(A^Γ) → R_Y has kernel {Σ f_γ u_γ : f_γ|_Y = 0}.
- For P_Y, test each of the finitely many scalars λ ∈ F_q^×.

PASS.

**Item 3 (homeomorphism onto a closed image).**
- Injectivity comes from W_p.
- Continuity: equal B(r)-languages give equal relations of length ≤ r.
- Inverse continuity comes from the length bound on W_p.
- The image is closed because the map is a continuous injection from a compact space to a Hausdorff one.
- Containment:
  - (⇒) Restriction gives a marked epimorphism.
  - (⇐) p ∉ L(Y′) gives W_p = 1 in G_(Y′), hence in G_Y, hence p ∉ L(Y).

PASS.

**Item 4 (isolation).**
- (⇐) Let Ω be a minimal SFT with window K. A subshift Y with L_K(Y) = L_K(Ω) satisfies Y ⊆ Ω, and minimality gives Y = Ω.
- (⇒) If X is not SFT, then X^(F) ⊋ X, and X^(F) → X, because F′-patterns of X^(F) with F′ ⊆ F are restrictions of patterns in L_F(X).
- Scope note: finite subshifts over f.g. Γ are SFTs through the f.g. normal core of the stabilizer. This is not needed for the infinite case used.

PASS.

**Item 5 (finite subshifts).**
- LC(Γ/H,F_q) ⋊ Γ ≅ M_([Γ:H])(F_q[H]) is the induced-representation identity.
- For Γ = Z^d, F_q[H] is a Laurent polynomial domain, so G_Y is a f.g. linear group and residually finite (Malcev).
- Minimal Z-subshifts are limits of the orbit closures of the note's periodic words, whose (2k+1)-languages agree with that of X.

PASS.

**Consequence for the frontier.** For a free minimal Z²-SFT Ω, S_n(Ω) = P_Ω is isolated among the marked groups G_Y and P_Y. So `free-minimal-sft-el-sofic-via-subshift-marked-limits` is dead. This claim is established, so its `invalidates:` entry is sound.
