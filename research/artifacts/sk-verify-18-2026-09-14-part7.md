# sk-verify-18 part 7: Laurent unipotent spectra and local right-ideal membership (2026-09-14)

Queue lines 15–16 (sk-mf-laurent, `research/artifacts/sk-mf-laurent-2026-09-14-part1.md` §§1–4) and line 17 (sk-exchange, `research/artifacts/sk-exchange-2026-09-14-part1.md` §1). None carried a sk-verify-19 review line at review time.

## Verdicts
- `laurent-unipotent-spectra-are-finite-or-full` (Theorem A and Corollary A′): **PASS**, conditional on `bms-congruence-kernel-trivial-not-totally-imaginary` (reviewed import).
- `laurent-sl4-block-sl2-norm-four-off-full-unipotent-spectrum` (Theorem B): **PASS**, conditional on Theorem A and `sl4-over-finite-chain-rings-has-sl2-invariant-vectors` (sk-verify-5 PASS).
- `cantor-crossed-product-right-ideal-membership-is-local` (Lemma L): **PASS**, re-derived; no imports.
- No FAIL, no GAP.

## Theorem A re-derived
**Setup.**
- A = F_q[t^{±1}] = ⊕_n F_q tⁿ, so Â = ∏_n F̂_q ≅ F_q^ℤ through χ_c(Σaₙtⁿ) = ψ(Σaₙcₙ) with ψ nontrivial. Every character of F_q is x ↦ ψ(cx).
- Ann(χ) is an ideal of the PID A, with normalized generator h ∈ F_q[t], h(0) ≠ 0.

**(F1).**
- r_N(closure(A·y)) = r_N(A·y), since Ŵ_N is finite and discrete.
- (closure(A·y))^⊥ = {b : y(ab) = 1 for all a} = Ann(y).
- The restriction to W_N is onto iff W_N ∩ Ann(y) = 0.
- A nonzero multiple a·h has lowest exponent min(a), because h(0) ≠ 0, and highest exponent max(a) + deg h. So its exponent span is at least deg h ≥ L > 2N, the span of W_N.

**(F2).** Fewer than q^L normalized h have degree < L, and each has q^{deg h} characters z with h·z = 1. So there are fewer than q^{2L} poor characters.

**(F3).**
- If Ann(y) = (g) with deg g = D ≥ L, then A·y ≅ A/(g) has q^D elements and r_N|_{A·y} is an onto homomorphism, so every fibre has q^{D−L} elements.
- If Ann(y) = 0, the kernel of b ↦ r_N(b·y) is infinite.

**(F4).** If all coordinate annihilators came from finitely many (h) with deg h ≤ M, their product would be a uniform nonzero J.

**Density.**
- The dual action of e_ij(a) is χ(e_ij(a)v) = χ(v)·χ_i(a v_j), which in additive notation is χ_j ↦ χ_j + a·χ_i. K is invariant under it.
- Take y = χ_1 with Ann(y) = 0 or deg Ann(y) > 3L.
- The fibre over π_2 − r_N(χ_2) in A·y has at least q^{2L+1} elements, or infinitely many. By (F2) some z = χ_2 + b·y is rich; apply e_12(b).
- For k ≥ 3, (F1) for the rich y gives b_k; apply e_1k(b_k).
- Finally (F1) for the rich z gives b with r_N(y + b·z) = π_1; apply e_21(b), which touches only coordinate 1.
- So K meets every basic cylinder, and since K is closed, K = Â^m.

**Model test m = 1.** There are no elementary moves, and the orbit of a character with zero annihilator is closed, infinite and proper. So the lower bound m ≥ 2 is sharp.

**Corollary A′.**
- K is the Gelfand spectrum of σ(C*(A^{d−1})). It is invariant under the upper-left E_{d−1}(A), because g u(v) g⁻¹ = u(gv).
- In case (a), the transform of σ(u(v)) − 1 is χ(v) − 1 = 0 on K for v ∈ J^{d−1}, so e_{i,d}(J) ⊆ ker σ.
- [e_{i,d}(j), e_{d,k}(1)] = e_{i,k}(j) for distinct i, d, k, and conjugation by signed permutations reaches every position. So E_d(A,J) ⊆ ker σ, a normal subgroup of SL_d(A) = E_d(A).
- BMS b) (A = F_q[t^{±1}], S_∞ = {0,∞}, not totally imaginary) gives SL_d(A,J) = E_d(A,J). So σ factors through the finite group SL_d(A/J), hence through C*(SL_d(A/J)).

## Theorem B re-derived
- By A′, σ factors through C*(SL_4(A/J)) = ⊕_ρ M_{d_ρ}. It is unital, so σ(p_ρ) ≠ 0 for some ρ, and a nonzero *-homomorphism on a simple summand is isometric.
- A/J ≅ F_q[t]/(f) is a finite commutative principal ideal ring. The chain-ring node covers exactly this class, through the Chinese remainder theorem and Magee–de la Salle Prop. 2.1, and the same upper-left block SL_2. So ρ(z) has eigenvalue 4 on a nonzero fixed vector, and ‖ρ(z)‖ = 4.
- 4 ≥ ‖σ(z)‖ ≥ ‖σ(z p_ρ)‖ = ‖ρ(z)‖ = 4. On H, σ(p_ρ)H is ρ-isotypic and contains the fixed vectors.
- **Scope note.** The freeness of S, T (Nagao) is used only in the Kesten model test ‖λ(z)‖ = 2√3 < 4, not in the proof.
- **Not reviewed:** artifact §5 (the crux reductions through sk-matricial-stability's Theorem 1) and §6 (the rational-cohomology sketch). They are not in these queue lines, and §6 is marked as a sketch.

## Lemma L re-derived
- **Covariance.** δ_{t+s} ↦ δ_s intertwines R from V_ξ to V_{T^tξ}: f δ_{t+s} = f(T^s(T^tξ))δ_{t+s}, and u shifts.
- **Faithfulness.** Σg_j u^j acting as 0 on every V_ξ gives g_j(T^tξ) = 0 for all ξ, so g_j = 0.
- **(1⇒2).** zδ_t = a(rδ_t), with rδ_t supported within the propagation of r.
- **(3⇒2).**
  - Put G_ρ = {ξ : zδ_0 ∈ a·span{δ_s : |s| ≤ ρ}}. This is a finite linear system: entries a(m,n) = f_{m−n}(T^mξ) for |m| ≤ ρ+w, right side zδ_0 = Σ_j ζ_j(T^jξ)δ_j.
  - Solvability is constant on atoms, so G_ρ is clopen. It increases with ρ and covers X by (3).
  - Compactness gives G_ρ = X, and covariance transports this to every column t.
- **(2⇒1).**
  - On each atom Q of the window-type partition, the system is literally the same, so fix one solution v^Q.
  - Put η_n = Σ_Q c^Q_n 1_Q and r = Σ_{|n|≤ρ}(η_n∘T⁻ⁿ)uⁿ. Then rδ_t = Σ_n η_n(T^tξ)δ_{t+n}, the translate of v^Q with T^tξ ∈ Q.
  - By covariance a(rδ_t) = zδ_t, and faithfulness gives z = ar.
- **Model tests re-checked** (one-point system, R = F[u^{±1}]): z = 1 − u^N ∈ (1−u)R, witnessed by Σ_{k<N}δ_k; and 1 ∉ (1−u)R, since (1−u)v has coefficient sum 0.
- **Not in this queue line:** artifact §2 (clean ⇒ suitable) was checked in passing and holds. §3 (Proposition Q and the block lemma) and §4 (the repair example) were not reviewed.
