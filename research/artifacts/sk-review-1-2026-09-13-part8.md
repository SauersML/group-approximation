# sk-review-1, part 8: sk-open-1 — ideals of aperiodic subshift rings and the subsystem sandwich

- **Reviewer:** lane sk-referee-1, a Claude Code agent. Not a human review.
- **Scope:** queue entries 26 and 27. Entry 28 was withdrawn by its owner, as a duplicate of `subshift-elementary-group-simple-iff-infinite-minimal`.
- **Main tip at review:** 49cd8e4197. Every step was re-derived by hand.

## 1. `aperiodic-subshift-ring-ideals-are-invariant-open-sets` + `-proof`: PASS

**U is open and invariant.** u^{±1}e_Vu^{∓1} = e_{T^{±1}V} ∈ J.

**I_U ⊆ J.**
- supp f is clopen and contained in U, so finitely many V_i with e_{V_i} ∈ J cover it.
- Over F_2, f = e_{supp f}(1-∏_i(1-e_{V_i})) ∈ J, and so fu^j ∈ J.

**J ⊆ I_U.**
- ru^{-i} ∈ J has u^0-coefficient f_i.
- Suppose f_i(x) = 1. x is not periodic, so there is a clopen V ∋ x inside {f_i = 1} with V∩T^jV = ∅ for the finitely many nonzero exponents j of ru^{-i}.
- Then e_V(gu^j)e_V = g e_{V∩T^jV}u^j = 0 for j ≠ 0, and e_Vf_ie_V = e_V. So e_V ∈ J and x ∈ U ✓.

**Uniqueness.** e_V ∈ I_U iff V ⊆ U, and clopen sets form a basis ✓.

**Quotient.**
- Restriction is a surjective homomorphism, because Y is invariant and locally constant functions on Y extend to X.
- Its kernel is {Σf_ju^j : f_j|_Y = 0} = I_U, since coefficients are unique in R_Y ✓.

**Credit note (for sk-novelty).** For principal (free-action) transformation groupoids, the correspondence between ideals and invariant open sets is most likely known in the Steinberg-algebra literature: ideals of Steinberg algebras of strongly effective ample groupoids, Clark–Edie-Michell and coauthors. The node says "Compare ..." and the proof is direct. A bounded search should decide between "known" and "new direct proof".

## 2. `aperiodic-subshift-el-normal-subgroups-are-sandwiched` + `-proof`: PASS

**Lemma 2 (trivial centre of EL_n(R_Y) for nonempty invariant Y).**
- Separating y from T^{-j}y kills the coefficients of nonzero exponent. Y inherits aperiodicity.
- The remaining c ∈ LC(Y,F_2) is invertible, and comparing u^0-coefficients in cc^{-1} = 1 gives c = 1 ✓.

**Step 0.** I_N is a two-sided ideal: over F_2 the permutation matrices e_ij(1)e_ji(1)e_ij(1) lie in G, and (eq:elementary) applies. By Lemma 1, I_N = I_Y for a unique Y ✓.

**Step 1.** e_ij(I_Y) ⊆ N, so E_Y ≤ N ✓.

**Step 2a.**
- If π_Y([g,h]) = 1 for every tower root h, then π_Y(g) commutes with every e_ij(ρ_Y(s)).
- These s̄ form a subring containing ρ_Y(1) = Σρ_Y(e_C), ρ_Y(u^{±1}) and ρ_Y(e_a), which generate R_Y.
- So π_Y(g) is central, hence trivial by Lemma 2 ✓.

**Step 2b.**
- ρ_Y sends E_ab(W) to E_ab(W∩Y), so it maps B_m(U_C) onto B_m(U_C∩Y). The corner of π_Y(k) is κ restricted to U_C∩Y.
- π_Y(k) ≠ 1 gives y ∈ U_C∩Y with κ(y) ≠ I.
- On a clopen W ∋ y with κ|_W = κ_0 we get H_W ≤ N, as in the note's l.205-221, with the G3 line of sk-referee-1.
- So e_W ∈ I_N = I_Y, that is W∩Y = ∅, contradicting y ∈ W ✓.

**Uniqueness.** E_{Y'} ≤ N gives I_{Y'} ⊆ I_N. N ≤ ker π_{Y'} gives I_N ⊆ I_{Y'} ✓.

**Corollary 4 (infinite X: EL_n simple iff X minimal).**
- Minimal: Y ∈ {∅, X}, so N = G or N ≤ ker π_X = 1.
- Not minimal: take a proper nonempty invariant Y. Then ker π_Y ∋ e_12(e_V) for a nonempty clopen V off Y, and π_Y(e_12(1)) ≠ 1 ✓.

**Proposition 5 (the K_2 layer).**
- St_n(R)/⟨⟨x_ij(I_Y)⟩⟩ ≅ St_n(R_Y): generators and relations lift.
- The surjection St_n(R) → G carries this normal closure onto E_Y.
- In St_n(R_Y) ↠ G/E_Y ↠ EL_n(R_Y), the kernel of the second map is the image of the kernel of the composite, K_2(n, R_Y) ✓.

**Wording note ("Aperiodicity is needed").** The example "the orbit closure of a point asymptotic to $p$, plus $p$ isolated" contradicts itself: in an orbit closure of a point asymptotic to p, the point p is not isolated. A clean example is X = Y ⊔ {0^∞} with Y a Sturmian subshift. 0^∞ is an isolated fixed point, because Sturmian words have 1's with bounded gaps. Then F_2[t^{±1}] is a direct factor of R, and its congruence ideals (t-1)^k give infinitely many normal subgroups with the same Y ✓.

## 3. Relevance to the note
Corollary 4 is a sharp "iff" for the hypothesis "minimal" (among infinite subshifts). Theorem 3 explains what minimality buys: normal subgroups correspond to subsystems, up to a K_2 layer. As a remark this would cost two to three lines, and whether it earns them is main's call. Nothing in the note depends on it.

## 4. Status
No GAP and no FAIL in the claims. Two notes: credit (Steinberg-algebra ideal theory) and the wording of the aperiodicity example. Queue entries 26 and 27 are done.
