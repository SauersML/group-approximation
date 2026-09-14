# When does a free minimal subshift give a LEF Kazhdan simple group? The converse side (part 1 of 2)

Lane `sk-general-actions-b` (SK swarm), 2026-09-13. Written proofs, UNREVIEWED (review queued with sk-referee-1).
Part 2 covers the answer for Z^d (rotation codings) and the manuscript proposal.

## 0. Setting, what main already has, and what this part adds

**Setting.**
- Γ is finitely generated, with finite symmetric generating set S and word balls B_r. A is a finite alphabet.
- X ⊆ A^Γ is a subshift with shift (g·x)(h) = x(g^{-1}h), on which Γ acts freely and minimally.
- k is a field, R_X = LC(X,k) ⋊ Γ, and G_N = EL_N(R_X).
- L_W(X) = {x|_W : x ∈ X}.

**Already on main (ids; mostly unreviewed):**
- The note's simplicity and (T) arguments work for every such X. G_N/Z is infinite, simple and Kazhdan, and finitely generated when k is finite (`steinberg-elementary-groups-are-simple-mod-centre`, EJZ). §4 checks that the tower proof of the note needs only freeness.
- **LEF chain.**
  - X is RF (Kerr–Nowak) ⟺ X is window-periodic (`rf-subshifts-are-periodic-window-approximable`).
  - RF ⟹ R_X is exactly matricial ⟹ every f.g. subgroup of GL_N(R_X) is LEF (`residually-finite-actions-give-matricial-crossed-products`).
  - LEF G_N for one N ≥ 4 ⟹ exactly matricial over finite fields (`lef-el-groups-force-exactly-matricial-simple-ring`) ⟹ X carries an invariant measure (`matricial-steinberg-algebras-have-invariant-measures`).
- For virtually free Γ, measure ⟺ RF ⟺ matricial ⟺ LEF (`virtually-free-cantor-elementary-group-lef-iff-invariant-measure`).
- For Z², Labbé's shift is measured and not RF, and whether its crossed product is matricial is OPEN (`labbe-wang-shift-crossed-product-is-exactly-matricial`).

**This part adds:**
- (A) `free-rf-actions-force-residually-finite-groups`: a free RF action forces Γ to be RF. So window-periodic free subshifts, and with them the RF route to LEF Kazhdan simple groups, exist exactly over RF groups.
- (B) `window-lef-subshifts-give-matricial-crossed-products`: partial finite models that are exact on windows ("window-LEF") give matricial crossed products. This is the right hypothesis for LEF acting groups that are not RF. For finitely presented Γ it coincides with window periodicity.
- (C) The group-level map, where Z is special.
  - `free-minimal-subshifts-all-rf-iff-virtually-cyclic` (OPEN). Every free minimal subshift over Γ is RF iff Γ is virtually cyclic. (⇐) is proved. (⇒) is proved for every non-RF Γ and every Γ with a weakly aperiodic SFT, so it follows from the Carroll–Penland conjecture.
  - `free-minimal-subshift-el-groups-all-lef-iff-virtually-cyclic` (OPEN). (⇐) is proved. (⇒) is proved for non-LEF Γ and for Γ ⊇ F_2. For amenable LEF groups such as Z² it is decided by the Labbé ring.

## 1. Lemma A: free RF actions force residually finite groups

**Lemma A.** Let a countable group Γ act continuously and freely on a compact metric space (X,d), and suppose the action is RF in the sense of Kerr–Nowak (Ma, arXiv:2209.00580, `defn: residually finite action`, quoted verbatim in `un-rf-beyond-free-2026-09-13-part1.md` §0). Then Γ is residually finite.

*Proof.*
1. Let g ≠ e. The map x ↦ d(gx,x) is continuous and positive, since the action is free, so δ = min_x d(gx,x) > 0 by compactness.
2. Apply residual finiteness with F = {g} and ε = δ/2. This gives a finite nonempty E ⊆ X and a genuine action β : Γ → Sym(E) with d(gz, β(g)z) < ε for all z ∈ E.
3. For z ∈ E, d(β(g)z, z) ≥ d(gz, z) − d(gz, β(g)z) > δ − δ/2 > 0. So β(g) ≠ id.
4. So ker β is a finite-index normal subgroup avoiding g. ∎

**Consequences.**
1. Over a f.g. group that is not RF, no free subshift is window-periodic (Proposition S). Examples: BS(2,3); Higman's group; Thom's f.g. Kazhdan LEF group that is not RF; derived topological full groups of minimal Z-subshifts, which are infinite, simple, and so not RF.
2. `rf-toeplitz-subshifts-over-residually-finite-groups` reaches exactly the RF groups.
3. For an LEF acting group that is not RF, genuine finite models do not exist, and the matricial route must use partial models (§2).

## 2. Theorem B: window-LEF subshifts give matricial crossed products

**Definition.** A subshift X ⊆ A^Γ is *window-LEF* if for every r ≥ 1 there are:
- a finite nonempty set E and a colouring c : E → A;
- permutations β(s) ∈ Sym(E) for s ∈ B_{4r}, with β(e) = id and β(st) = β(s)β(t) whenever s, t, st ∈ B_{4r};

such that, writing c_z(λ) = c(β(λ^{-1})z) for λ ∈ B_r, we have {c_z : z ∈ E} = L_{B_r}(X).

If Γ acts on E by a genuine action, this is window periodicity restricted to balls. So window-periodic ⟹ window-LEF.

**Theorem B.** Let X ⊆ A^Γ be a free window-LEF subshift and k a field.
1. Γ is LEF.
2. R_X embeds unitally and injectively in ∏_ω M_{N_n}(k), where N_n = |E_n| are the sizes of the models.
3. If k = F_q, every finitely generated subgroup of every GL_M(R_X) is LEF.
4. If Γ is finitely presented, then X is window-LEF ⟺ X is window-periodic ⟺ X is RF (Proposition S).

*Proof.*

**Two identities.** Fix a model at radius r.
- (I1) For g, λ with λ, gλ ∈ B_r (so g ∈ B_{2r}), c_{β(g)z}(gλ) = c(β(λ^{-1}g^{-1})β(g)z) = c(β(λ^{-1})z) = c_z(λ). The middle step uses the partial-homomorphism rule with s = λ^{-1}g^{-1}, t = g and st = λ^{-1}, all in B_{4r}.
- (I2) β(g^{-1}) = β(g)^{-1} for g ∈ B_{2r}.

**Local freeness.**
- For s ≠ e, freeness and compactness give a finite V_s ⊆ Γ such that x|_{V_s} ≠ (s^{-1}·x)|_{V_s} for every x ∈ X.
- Fix ρ, and let r ≥ 2ρ exceed the radius of every V_s with s ∈ B_{2ρ}∖{e}.
- Suppose β(s)z = z with s ∈ B_{2ρ}∖{e}. By (I1), c_z(sλ) = c_z(λ) for λ ∈ V_s. Pick x ∈ X with x|_{B_r} = c_z. Then x(sλ) = x(λ), that is (s^{-1}·x)|_{V_s} = x|_{V_s}, a contradiction.
- So β(s) has no fixed point for s ∈ B_{2ρ}∖{e}.

**Item 1.** By (I2) and local freeness, β(s) = β(t) with s,t ∈ B_ρ forces β(s^{-1}t) = id, so s = t. So β|_{B_ρ} is injective, and it preserves the products that stay in B_ρ. So Γ is LEF.

**The model map.** Let a ∈ R_X. Choose ρ so that a = Σ_{g ∈ B_ρ} f_g u_g, where each f_g depends only on coordinates in B_ρ: f_g(x) = F_g(x|_{B_ρ}). On k^E put
- D(f)δ_z = F(c_z|_{W_f}) δ_z,
- P_g δ_z = δ_{β(g)z},
- φ_r(a) = Σ_g D(f_g) P_g.

D(f) is well defined because c_z|_{W_f} ∈ L_{W_f}(X), since every c_z is a pattern of X.

**Relations.** Let a finite list 𝓛 ⊆ R_X be given, together with the sums and products of pairs from 𝓛. Choose ρ bounding all supports and windows involved, and r ≥ 4ρ larger than the freeness radius above.
- D is multiplicative and additive on functions, pointwise. D(1) = id and P_e = id.
- P_g P_h = P_{gh} for g, h, gh ∈ B_{2ρ} (partial-homomorphism rule).
- Conjugation. Write u_g f u_g^{-1} = f∘α(g^{-1}), where (f∘α(g^{-1}))(x) = F((g^{-1}·x)|_{W_f}) depends on the window gW_f ⊆ B_{2ρ}. Then P_g D(f) P_g^{-1} δ_{β(g)z} = F(c_z|_{W_f}) δ_{β(g)z}. By (I1), (g^{-1}·c_{β(g)z})(λ) = c_{β(g)z}(gλ) = c_z(λ) on W_f, so this equals D(f∘α(g^{-1})) δ_{β(g)z}.
- So (f u_g)(h u_k) = f·(h∘α(g^{-1})) u_{gk} is carried to D(f)P_g D(h) P_k = D(f·h∘α(g^{-1})) P_{gk}.
- So φ_r preserves every listed sum and product.

**Injectivity.** Let a = Σ_{g ∈ B_ρ} f_g u_g ≠ 0.
- Pick g_0 with f_{g_0} ≠ 0 and x ∈ X with f_{g_0}(x) ≠ 0.
- Pick z with c_z = x|_{B_r}, and put z' = β(g_0^{-1})z.
- The g_0-term of φ_r(a)δ_{z'} is F_{g_0}(c_z)δ_z ≠ 0.
- Every other term lands at β(g)z' = β(g g_0^{-1})z ≠ z, by local freeness with s = g g_0^{-1} ∈ B_{2ρ}∖{e}.
- So φ_r(a) ≠ 0.

**Item 2.** Take r_n → ∞ and set φ(a) = (φ_{r_n}(a))_n, with an arbitrary value for the finitely many small n. Each relation among finitely many elements holds for all large n, so φ is a unital ring homomorphism into ∏_ω M_{|E_n|}(k). By injectivity at each large n, φ is injective.

**Item 3.**
- M_M(∏_ω M_N(F_q)) = ∏_ω M_{MN}(F_q), and a unital ring embedding preserves invertibility. So GL_M(R_X) ↪ ∏_ω GL_{M N_n}(F_q).
- A countable subgroup H of an algebraic ultraproduct ∏_ω Q_n of finite groups is LEF. For a finite F ⊆ H, the finitely many products and inequalities hold in Q_n for ω-most n.

**Item 4.**
- Let Γ = ⟨S | ℛ⟩, with relators of length ≤ ℓ, and take r ≥ ℓ.
- For a relator s_1⋯s_ℓ, all prefixes lie in B_r. Repeated use of the partial-homomorphism rule gives β(s_1)⋯β(s_ℓ) = β(e) = id. So β|_S extends to a genuine homomorphism β' : Γ → Sym(E).
- By induction on word length, β' = β on B_r.
- Put y_z(λ) = c(β'(λ^{-1})z) for all λ ∈ Γ. Then y_{β'(g)z} = g·y_z, and y_z|_{B_r} = c_z.
- Every window of y_z is a window c_{z'} of X. So O = {y_z} is a finite invariant subset of the window SFT that covers L_{B_r}(X). That is window periodicity. The converse holds trivially, and Proposition S gives RF. ∎

**Model tests.**
- Γ = Z: every infinite minimal subshift is window-periodic (return words), so it is window-LEF.
- Labbé's shift over Z² is not window-LEF. Z² is finitely presented, so window-LEF would mean window-periodic, and it lies in an SFT without periodic points.
- The hypothesis bites for LEF groups that are not RF: by Lemma A no free subshift over them is window-periodic, while window-LEF is still possible. Whether free minimal window-LEF subshifts exist over every f.g. LEF group is not settled here. It is the natural source of LEF Kazhdan simple groups containing a prescribed LEF group, which is lane sk-universal-embedding-b's target.
- **Candidate, unverified:** the action of a derived topological full group [[T]]' on its minimal Z-subshift is only topologically free. Grigorchuk–Medynets periodic approximations look like window-LEF models, and the injectivity argument above can be adapted to topologically free actions.

## 3. The group-level map: which acting groups make every free minimal subshift work?

**Proposition C (⇐).** If Γ is f.g. and virtually cyclic, then every free minimal subshift X over Γ is RF. So R_X is exactly matricial, and EL_N(LC(X,F_q)⋊Γ)/Z is infinite, simple, Kazhdan and LEF for all N ≥ 3.

*Proof.*
1. Γ has a normal subgroup N ≅ Z of finite index: take the normal core of a finite-index infinite cyclic subgroup.
2. With t a generator of N, a weak* limit μ_0 of (1/n) Σ_{j<n} t^j_* δ_x is N-invariant (Krylov–Bogolyubov). Then μ = |Γ/N|^{-1} Σ_{gN} g_*μ_0 is well defined and Γ-invariant.
3. By minimality μ has full support. N is a free subgroup of finite index, so `virtually-free-group-measure-actions-are-rf` (reviewed PASS) makes the action RF.
4. The rest follows from `residually-finite-actions-give-matricial-crossed-products` and `steinberg-elementary-groups-are-simple-mod-centre`. ∎

**Proposition D ((⇒) for RF).** Let Γ be f.g. and infinite. Suppose that (i) Γ is not RF, or (ii) Γ has a *weakly aperiodic* SFT, meaning a nonempty SFT with no finite orbit. Then some free minimal subshift over Γ is not RF.

*Proof.*
- **Free minimal subshifts exist.** `gjs-countable-groups-have-free-minimal-subflows` gives a free minimal W ⊆ 2^Γ.
- **Case (i).** W is not RF by Lemma A.
- **Case (ii).** Let Y be weakly aperiodic, and let M ⊆ Y × W be a minimal subset.
  - The projection of M onto W is onto, by minimality of W. An extension of a free action is free, so M is free.
  - M is minimal and infinite, so it is perfect, and it is a subshift over A × {0,1}.
  - Its image in Y is a nonempty closed invariant subset without isolated points and with no finite orbit.
  - So M is an extension of such a subset, hence not RF (`extensions-of-aperiodic-sfts-are-not-residually-finite-actions`, item 2). ∎

**Lifting lemma.** If a subgroup H ≤ Γ has a weakly aperiodic SFT Y, so does Γ.

*Proof.*
- Put Y_Γ = {x ∈ A^Γ : (g^{-1}·x)|_H ∈ Y for all g ∈ Γ}. It is an SFT over Γ with the same forbidden windows as Y.
- **Nonempty.** Choose left coset representatives t, and set x(th) = y(h) for a fixed y ∈ Y. For g = t h_0 this gives (g^{-1}·x)|_H = h_0^{-1}·y ∈ Y.
- **No finite orbit.** If x ∈ Y_Γ had a finite Γ-orbit, then Stab(x) ∩ H would have finite index in H and fix x|_H ∈ Y. So x|_H would have a finite H-orbit, a contradiction. ∎

**Status.**
- Carroll–Penland conjecture (arXiv:1502.03195; bounded check, one web search, abstract level): a f.g. group admits a weakly aperiodic SFT iff it is not virtually Z.
- Proposition D shows that the conjecture implies (⇒) of `free-minimal-subshifts-all-rf-iff-virtually-cyclic`.
- Known cases of the conjecture, recalled and not read from the PDFs:
  - Z² (Berger);
  - free groups (Piantadosi);
  - lamplighters (Cohen, arXiv:1710.03707);
  - one-ended hyperbolic groups (Cohen–Goodman-Strauss–Rieck, arXiv:1706.01387, strongly aperiodic);
  - virtually nilpotent groups that are not virtually Z (Carroll–Penland);
  - Baumslag–Solitar groups (Aubrun–Kari).
- With the lifting lemma, every group containing one of these has a weakly aperiodic SFT.

**Proposition E (LEF variant).** Say Γ has (∀LEF) if for every free minimal subshift X over Γ, EL_N(LC(X,F_q)⋊Γ) is LEF for all N ≥ 3.
- If Γ is virtually cyclic, Γ has (∀LEF) (Proposition C).
- If Γ is not LEF, Γ fails (∀LEF). Every such EL_N/Z contains Γ (`crossed-product-group-embeds-in-projective-elementary-group`).
- If Γ ⊇ F_2, Γ fails (∀LEF).
  - `f2-groups-have-paradoxical-free-minimal-subshifts` gives a free minimal subshift with no invariant measure.
  - So R_X is not matricial (`matricial-steinberg-algebras-have-invariant-measures`), and EL_N is not LEF for N ≥ 4 (`lef-el-groups-force-exactly-matricial-simple-ring`).
  - These groups even have no MF quotient from rank 2n (`no-invariant-measure-steinberg-elementary-no-mf-quotient`, reviewed PASS).
- **Open: amenable LEF groups that are not virtually cyclic, e.g. Z².** There the failure of RF is known (Proposition D), and what is missing is "not RF ⟹ not matricial". For Z² that is exactly the Labbé decider `labbe-wang-shift-crossed-product-is-not-exactly-matricial`.
- **Non-amenable groups without F_2** (free Burnside groups, Golod–Shafarevich groups). Tarski's theorem gives a paradoxical decomposition of Γ, and the construction of `f2-groups-have-paradoxical-free-minimal-subshifts` goes through verbatim with finitely many pieces. That would give (⇒) for every non-amenable Γ. The Tarski import has NOT been verified from a source here (sketch only).

## 4. The tower proof over Γ uses only freeness (checklist against the note)

Line numbers refer to `$SK/manuscript-disk-1646.tex`. Replace the powers u^a by u_g, and |a| ≤ m by g ∈ B_m.
- **l.78-82.** For Z, minimality plus infiniteness gives freeness. For general Γ, freeness must be assumed. Compactness then gives clopen partitions with C ∩ gC = ∅ for g ∈ B_L∖{e}.
- **l.105-116** (R simple, centre F_2, Z(G) = 1). The same argument works:
  - multiply by u_{g^{-1}};
  - choose U with U ∩ gU = ∅ for g in the support;
  - separate x from g^{-1}x, which is where freeness is used;
  - invariance plus minimality makes f_e constant.
- **l.157-173** (towers). E_{ab}(W) = e_{aW} u_{ab^{-1}} for a, b ∈ B_m.
  - Product: E_{ab}(W)E_{cd}(W') = e_{aW} e_{ab^{-1}cW'} u_{ab^{-1}cd^{-1}}. This vanishes for b ≠ c, because b^{-1}c ∈ B_{2m}∖{e}, and equals E_{ad}(W∩W') for b = c.
  - So B_m(U) ≅ M_{|B_m|}(LC(U,F_2)).
  - Absorption: f u_i E_{ab}(W) = E_{ia,b}(W_1), and E_{ab}(W) f' u_j = E_{a, j^{-1}b}(W_2).
- **l.175-227.**
  - Take h = e_{ij}(s) with s ∈ {e_C, e_C u_t : C ∈ 𝒫, t ∈ S}. Then e_C u_t = E_{e,t^{-1}}(C) ∈ B_1(C), so no translate of C is needed.
  - Commuting with every such h again forces g ∈ Z(G) = {1}.
  - k − I ∈ M_3(B_{w+1}(C)) and d = 3|B_{w+1}| ≥ 6, so GL_d(F_2) is simple. The rest is verbatim.
- **Conclusion.** For every f.g. Γ and every free minimal subshift X ⊆ A^Γ, EL_3(LC(X,F_2)⋊Γ) is infinite, f.g., simple and Kazhdan with the note's proof. It is LEF whenever X is window-LEF (Theorem B).

## 5. Firewalls

- **"LEF ⟺ exact permutation models" is not established for general Γ.** A LEF EL_N (N ≥ 4) gives exact *matricial* models. At finite scale these only need commuting idempotents at nearby sites, with no global configuration. So the permutation form of the converse is the quantum-to-classical question (`labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`). This lane does not claim it.
- **Rank 3.** The converse steps LEF ⟹ matricial need N ≥ 4. Proposition E's (⇒) for Γ ⊇ F_2 is stated through N = 4. The failure for non-LEF Γ holds at every N ≥ 3.
