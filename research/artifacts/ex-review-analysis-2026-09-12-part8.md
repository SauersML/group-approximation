# EX review, analysis lanes, part 8 (2026-09-13)

Lane `ex-verify-analysis`. Verdict legend as in `ex-review-analysis-2026-09-12.md` §0. Main tip at
review time: `3e0b32d52`.

## 1.16 ex-k1-properly-infinite, remaining establishments

### `dd-toeplitz-algebra-is-properly-infinite` (412dd76324): PASS on the derivation

Re-derived.
- **Lemma 1.** On the full Fock space, l_k(θ)^* l_k(θ') = ⟨θ, θ'⟩ for θ, θ' in the C(X)-span of
  elementary tensors. Two such θ that are orthonormal in E^{⊗k} give isometries with orthogonal
  ranges, so T(E) is properly infinite.
- **Proposition 2.**
  - Put M_kl = Σ_j ⟨e_k, η_j⟩⟨η_j, e_l⟩ = (BB^*)_kl. Then 0 ≤ M ≤ 1 and tr M ≤ n, by Bessel.
  - ⟨V, V⟩ = Σ_{k,l ≤ N} (δ_kl − M_kl)² = N − 2 Σ_k M_kk + tr(M_I · conj(M_I)). The product of two
    positive semidefinite matrices has nonnegative trace, so ⟨V, V⟩ ≥ N − 2n = n + 1 for N = 3n + 1. The
    same holds for W.
  - |⟨V, W⟩| ≤ Σ |M_kl|² ≤ tr(M²) ≤ tr M ≤ n.
  - So the Gram--Schmidt remainder of W is ≥ (n + 1) − n²/(n + 1) = (2n + 1)/(n + 1) > 0.
  - The rescalings by continuous functions are module actions, so θ_1 and θ_2 stay in the span of
    elementary tensors.
- **Theorem 3.** E_DD = (1 − θ_{η,η})F'' with n = 1 needs 8 orthonormal sections, and constant sections
  supply them.
- **Trust surface.** Blanchard arXiv:1507.02535v1: the description of E_DD in the proof of
  Proposition 4.3, and the numbering of Question 5.4 and Remark 5.3 a'. I did not re-read these.
- **Scope.** The node correctly says this closes Blanchard's two explicit candidates for a refutation of
  LXI through BRR Theorem 5.5. It does not decide LXI.

### `euler-class-protection-fails-for-o2-self-similar-modules` (ca07feae67): PASS

Re-derived.
- E ≅ E ⊕ E gives Cuntz isometries S_1, S_2 in L(E). For a unit section ξ, the four S_i S_j ξ are
  orthonormal.
- The projections onto E_n converge strictly to 1. So at a late stage the compressed Gram matrix is
  uniformly within 1/2 of I, and Gram--Schmidt gives four orthonormal sections of E_n. Hence
  E_n ≅ θ⁴ ⊕ η with rank η = r_n − 2.
- **Whitney.** c(P_n) = c(θ² ⊕ P_n) = c(E_n) = c(η), and c_{r_n}(η) = 0.
- **Consequence.** Toms's trapped class multiplies by c_r(Q)², which vanishes once c_r(Q) = 0. So it
  cannot protect a witness in the O_2-multiplier reduction. Correct.

### `o2-free-circle-halving-homotopy`: correctly not established

- Its only route is `o2-free-circle-halving-homotopy-from-lxi`, which requires the OPEN LXI root.
- The body has Attempts, but its first line has no explicit "OPEN" marker. That is a wording point only.
- `properly-infinite-unital-algebra-not-k1-injective-exists` is OPEN, and its route requires the OPEN
  `o2-multiplier-ideal-with-non-k1-injective-unitization`.

## 2.1 Spot check of citation imports used by reviewed proofs

For each import, I checked that the citation route names a version, gives theorem numbers, quotes the
statements, and that its hypotheses match how the reviewed proofs use it. I did not re-read the
sources.

| import | numbers quoted verbatim | matches use |
|---|---|---|
| `rainone-type-semigroup-crossed-product-dichotomy-citation` | Definitions 4.6 and 4.8; Theorems 4.11, 4.13, 4.16, 4.21, 4.22; Corollary 4.14 | yes. Theorem 4.21's hypotheses are exactly what §1.11's simple-coefficient dichotomy supplies. The AF integer dichotomy avoids Rainone's unital blanket assumption by its own (P1)--(P4) |
| `opr-properly-infinite-multiple-splits-citation`, `opr-cfp-rr0-dichotomy-citation` | Theorem 4.3, Corollaries 4.4 and 5.16, Theorems 5.8(ii) and 5.14, Corollary 5.9 | yes |
| `ara-goodearl-tame-refinement-monoids-separative-citation` | Definition 2.1, Theorem 2.3, Examples 2.2 | yes |
| `natarajan-vidick-games-pcp-amplification-error-citation` | abstract item (2), §4.2 eqs. (1)--(3), Remark 5, Lemma 6 eqs. (6), (7), (9) | yes. It correctly invalidates `games-qpcp-from-tensor-power-amplified-xx-zz` |
| `bgw-trivial-coefficient-agreement-is-open-citation` | Appendix A pp. 39--40, and the withdrawn main-text passage | yes |
| `small-set-expansion-hypothesis-implies-ugc-citation` | Raghavendra--Steurer Conjectures 1.2 and 1.3, Theorem 1.4; RST Corollary 3.3 | yes |
| `affine-ug-easy-on-globally-hypercontractive-graphs-citation` | Bafna--Minzer Definition 1.4, Theorems 1.5--1.8 | yes |
| `nlts-hamiltonians-from-good-qldpc-codes-citation` | ABN Theorem 1 and Property 1 | yes. The Panteleev--Kalachev theorem number is honestly flagged as not read from the PDF |
| `commuting-hamiltonians-on-small-set-expanders-in-np-citation` | Aharonov--Eldar Theorems 1 and 2 | yes |
| `product-states-approximate-high-degree-2-local-citation` | Brandão--Harrow Theorem 3, Corollaries 4 and 5 | yes. The degree threshold arithmetic is correct |

**Note, outside EX scope.** `vigdorovich-linear-selflessness-citation` (landed 08-30 by an earlier
campaign) gives arXiv:2602.10616v3 Theorem 1.1 with no quoted statement and no source-read record. It
enters §1.7's `selfless-projection-traces-equal-k0-trace-image` only for class 4 (linear groups with
trivial amenable radical). Classes 1--3, and every result reviewed here, are independent of it.
