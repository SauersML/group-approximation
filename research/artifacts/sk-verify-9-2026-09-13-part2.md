# sk-verify-9: independent review of Theorem 2 and of the finite-simple-limit headline (2026-09-13), part 2

Continues `research/artifacts/sk-verify-9-2026-09-13.md`, which holds the verdict table, Theorem 2 and fixes F1–F4. This part covers the headline, fixes F5–F6 and the free simplification S1.

## 3. The headline: finite simple approximants

### 3.1 View models (sk-strong-8 §1–2; sk-strong-6 route), re-derived
- **Setup.**
  - Δ is finitely generated, infinite and LEF, with S symmetric.
  - φ_n: Δ → Q_n has φ_n(e) = e and is injective and multiplicative on B_r for large n.
  - Q_n = ⟨φ_n(S)⟩, which contains φ_n(B_{r_n}) by induction on word length.
  - Y_n = F_2^{Q_n} and N_n = 2^{|Q_n|} → ∞, since |Q_n| ≥ |B_r|.
  - L_n = Z/2≀Q_n acts on Y_n by (q·y)(p) = y(q^{-1}p) and c·y = y+c.
  - ψ_n(cδ) = (φ_n)_*c · φ_n(δ).
- **(b) ψ_n is multiplicative on a fixed ball for large n.**
  - (cδ)(c′δ′) = (c+δc′)δδ′.
  - (φ_n)_*(δc′) = Σ_{h∈supp c′} 1_{φ_n(δh)} = φ_n(δ)·(φ_n)_*c′, once φ_n is multiplicative on those pairs.
  - (φ_n)_*(c+c″) = (φ_n)_*c + (φ_n)_*c″, by injectivity on the supports (F_2-cancellation). ✓
- **(★) The seen configuration moves as L moves points.** Put x_y = y∘φ_n ∈ 2^Δ.
  - For s: (φ_n(s)^{-1}·y)(φ_n h) = y(φ_n(s)φ_n(h)) = x_y(sh) = (s^{-1}x_y)(h).
  - For a: (y+1_e)(φ_n h) = x_y(h) + [h = e] = (a x_y)(h), using φ_n(e) = e and injectivity on W∪{e}.
  - For words, induct with (b). The window for ℓ_1ℓ_2 is the window of ℓ_2 enlarged by the coordinates ℓ_1 depends on, and it stays fixed as n grows. ✓
- **(c) Covariance.** U_n(ψ_nℓ)D_n(f)U_n(ψ_nℓ)^{-1}δ_y = f(x_{ψ_n(ℓ)^{-1}y})δ_y = f(ℓ^{-1}x_y)δ_y = D_n(f∘ℓ^{-1})δ_y. ✓
  - So Φ_n(Σf_ℓu_ℓ) = ΣD_n(f_ℓ)U_n(ψ_nℓ) is additive, multiplicative and unital on fixed pairs for large n.
- **sk-strong-6's convention** for x ↦ δx+f is y ↦ y∘L_{ψ_n(δ)^{-1}} + Σ_{h∈supp f} 1_{ψ_n(h)}. The attached configuration at h is y(ψ_n(δ^{-1}h)) + f(h) = (δx_y+f)(h). ✓ These are the same models.

### 3.2 Surjectivity (sk-strong-8 Lemma 3; sk-strong-6 (iii))
- **Permutations.** Products of the U_n(φ_n s) give every U_n(q), q ∈ Q_n.
- **Diagonal units.** U_n(q)D_n(p)U_n(q)^{-1}δ_y = (q^{-1}·y)(e)δ_y = y(q)δ_y. The evaluations y ↦ y(q) separate the points of Y_n, so products of these diagonal matrices and of I minus them give every E_{y,y}.
- **Translations.** U_n(q)U_n(a)U_n(q)^{-1} is the translation T_{1_q}. These generate every T_c, and T_{y+y′}E_{y′,y′} = E_{y,y′}.
- **Conclusion.** ρ_n: F → M_{N_n}(F_2) is onto, and EL_3(M_N(F_2)) = SL_{3N}(F_2): transvections between blocks are e_ij(E_ab), and those inside a block are commutators. ✓
  - So the approximants are the finite simple groups SL_{3·2^{|Q_n|}}(F_2).
- **Agreement.** For fixed w ∈ F and large n, ρ_n(w) = Φ_n(π(w)). It is exact on t_s, t_a and t_p, and holds on t_s′ once φ_n(s^{-1}) = φ_n(s)^{-1}. ✓

### 3.3 Rev3's E_n models cannot give simple approximants
- **The models.** On E_n = F_2^{Q′_n}×Q′_n (rev3 l.315–327):
  - the attached configuration of (c,q) is h ↦ c(qψ_n(h));
  - σ_ℓ(c,q) = (c + Σ_{h∈supp f} 1_{q′ψ_n(h)}, q′), with q′ = qψ_n(δ^{-1}).
- **A commuting action.** Put τ_g(c,q) = (c∘L_{g^{-1}}, gq), where (c∘L_{g^{-1}})(p) = c(g^{-1}p).
  - τ_gσ_ℓ = σ_ℓτ_g, because 1_p∘L_{g^{-1}} = 1_{gp}.
  - τ_g preserves the attached configuration, so it commutes with every D_n(f).
- **Consequence.** For g ≠ e, τ_g is a non-scalar permutation matrix. So the generated algebra lies in a proper commutant and is not M_{|E_n|}(F_2).
- **Scope.** These models are correct for LEF, where a ring homomorphism is all 1.7 needs. The headline needs the view models, which are the quotient of E_n by τ.

### 3.4 Marked convergence on a fixed marking
- **Marking.** H is marked by e_ij(π(t)) for the letters t ∈ {t_s, t_s′ (s ∈ S), t_a, t_p}. This generates H, since 1 = u_su_s^{-1}.
- **Words.** For a word W in the marking, the entries of W − I_3 are elements of F of degree ≤ |W|.
  - If W = 1 in H, then π(entries) = 0, so ρ_n(entries) = Φ_n(0) = 0 for large n.
  - If W ≠ 1 in H, then ρ_n(W) ≠ I for large n, by S1 below or by sk-strong-8 Lemma 2.
  - Lemma 2 re-derived: witness coordinates separate the finitely many ℓx, and the far witnesses exist because Δ is infinite. In the column at y, the coefficient in the row ψ_n(ℓ_0)y, which is distinct from the other rows, is f_{ℓ_0}(ℓ_0x_y) = 1.
- **Conclusion.** Each radius involves finitely many words, so the marked groups converge along the whole sequence. ✓

### 3.5 Expansion: GAP F5 (the conclusion is true; the step as written is not)
- **Where.**
  - sk-strong-8 Theorem A item 2 and §3 step 1: "H and each SL_{3N_n}(F_2) are marked quotients of Λ = EL_3(F), with compatible markings".
  - sk-strong-6's route: "quotients of EL_3(F) with compatible generators e_ij(t) … The uniform Kazhdan constant of EL_3(F) makes their Cayley graphs a family of expanders".
- **Problem.** Both mark Λ by the e_ij(t) for letters t, and these do not generate Λ. They lie in the kernel of EL_3(F) → SL_3(F_2) induced by the augmentation F → F_2, and e_ij(1) does not. So "(Λ, marking) is a Kazhdan pair" is not available as written. Rev3 §1 had the same gap and fixed it (sk-panel-referee-5 B1).
- **Repair (verified).**
  - Σ = {e_ij(1)} ∪ {e_ij(t)} generates Λ, which has (T) by EJZ.
  - H and every approximant are quotients of Λ, so the Cayley graphs for the images of Σ have a uniform spectral gap (Margulis).
  - In H, e_ij(1) = [e_ik(u_s), e_kj(u_s^{-1})] with k ∉ {i,j}.
  - In the approximants, e_ij(I) = [e_ik(ρ_n t_s), e_kj(ρ_n t_s′)]: exactly in sk-strong-8, which sets ρ_n(t_s′) = U_n(φ_n s)^{-1}, and for large n in sk-strong-6, with S symmetric.
  - So the images of e_ij(1) are words of length 4 in the markings, and the Cayley graphs for the markings form an expander family. ✓

### 3.6 Theorem B (the characterization)
- **(i) ⇒ (ii), overgroup** (rev3 l.282–293, re-derived):
  - Γ embeds in ∏_ω Q_n, and the doubled regular actions are even;
  - by Ore every even permutation is a commutator, and Δ_0, a countable subgroup of an algebraic ultraproduct of finite groups, is LEF;
  - Δ = Δ_0×Z is infinite, finitely generated and LEF, with Γ ≤ [Δ_0,Δ_0]×1 = [Δ,Δ].
- **(i) ⇒ (ii), Whitehead embedding** (re-derived over F_2):
  - e_12(c)e_21(c^{-1})e_12(c) = [[0,c],[c^{-1},0]], since 1+cc^{-1} = 0; times w(1) = [[0,1],[1,0]] this gives diag(c,c^{-1});
  - diag(a,a^{-1},1)diag(b,b^{-1},1)diag((ba)^{-1},ba,1) = diag(aba^{-1}b^{-1},1,1);
  - so ℓ ↦ diag(u_ℓ,1,1) is a homomorphism L → GL_3(R) that maps [L,L] into H.
- **(i) ⇒ (ii), conclusion.** With 3.1–3.5, H is a marked limit of finite simple expanders.
- **(ii) ⇒ (i).** Balls of H inject into approximants, preserving products that stay inside the ball, and f.g. subgroups of LEF groups are LEF. ✓
- sk-strong-8's "if Γ is finite, replace it by Γ×Z" is harmless but unnecessary, since Δ = Δ_0×Z is already infinite.

## 4. Fixes F5–F6, verbatim

**F5a (sk-strong-8 artifact §3, proof of Theorem A, step 1).**
- Before: "So H and each SL_{3N_n}(F_2) are marked quotients of Λ = EL_3(F), with compatible markings."
- After: "So H and each SL_{3N_n}(F_2) are quotients of Λ = EL_3(F), and Λ is generated by Σ = {e_ij(1), e_ij(t)}. In H and in every approximant, e_ij(1) = [e_ik(t_s), e_kj(t_s′)] for k ∉ {i,j}."
- Append to step 3: "The images of e_ij(1) are words of length 4 in the markings, so the Cayley graphs for the markings e_ij(ρ_n(t)) also form an expander family."

**F5b (sk-strong-6 route, "Convergence and expansion").** Replace "with compatible generators `e_ij(t)`" by "with compatible generators `e_ij(1)` and `e_ij(t)`; `e_ij(1) = [e_ik(t_s), e_kj(t_(s^(-1)))]` in both quotients for large `n`".

**F5′ (note text: rev4, or sk-strong-6 (a2)).** "the argument of Section~1 shows" imports rev3's transfer through $\sum_ae_a=1$, which has no analogue for the lamplighter letters. Either mark the host by $e_{ij}(1)$ as well, or add "and $e_{ij}(1)=[e_{ik}(u_s),e_{kj}(u_s^{-1})]$ in both quotients".

**F6 (sk-strong-8 artifact §4).**
- Replace "Right translation (c,q) ↦ (c∘R_g, qg) commutes with the letters" by "Left translation (c,q) ↦ (c∘L_{g^{-1}}, gq), with (c∘L_{g^{-1}})(p) = c(g^{-1}p), commutes with the letters".
- The right translation does not preserve the attached configuration. The conclusion, a proper commutant, stands (§3.3).

## 5. Free simplification S1 (verified)
- **Statement.** Once simplicity is proved, nonvanishing on ring elements is not needed for marked convergence.
- **Proof.**
  - For every nonprincipal ultrafilter ω the models define a unital ring homomorphism R → ∏_ω M_{N_n}(F_2), and 1.7 makes G → ∏_ω GL_{3N_n}(F_2) injective.
  - So a nontrivial word W has ρ_n(W) ≠ I for ω-almost all n, for every ω, and so for all but finitely many n.
  - N_n → ∞ follows as well: along a subsequence with N_n bounded, G would embed in a finite group.
- **Deletable:** rev3 l.158–160 (the Z-case), sk-strong-8 Lemma 2, and sk-strong-6 step (ii).

**Suggested single statement for rev4.** The mathematics is verified here; the wording is unreviewed as note text.
- **Hypothesis.** Replace Theorem 2's ring homomorphism by "maps $\Phi_k\colon R\to M_{N_k}(\F_2)$ that are additive, multiplicative and unital on each fixed pair of elements for large $k$, and whose values on a finite generating set of $R$ generate $M_{N_k}(\F_2)$ as a ring".
- **Extra conclusion.** Beyond 1.1–1.7: $\EL_n(R)$ is the limit, in the space of marked groups, of the finite simple groups $\SL_{nN_k}(\F_2)$. Their Cayley graphs for these generators form expanders, with $e_{ij}(1)$ transferred as in F5.
- **Proof:** 1.7 for every ω, plus 3.4 and 3.5.
- **Instances.** Both satisfy it: ρ_ℓ is onto in the Z-case (rev3 l.166–168), and the view models are onto (3.2).
- **Gain.** Theorem 1 and the headline host come under one statement, with no nonvanishing lemma.
