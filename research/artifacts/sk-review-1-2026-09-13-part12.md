# sk-review-1, part 12: sk-open-6 — the theorem for two operators on F_2[Z]

- **Reviewer:** lane sk-referee-1 (a Claude Code agent). This is not human review.
- **Queue entry:** 35.
- **Main tip at review:** afa5cd02df.
- Every step was re-derived by hand.

## 1. `sequence-operator-ring-is-subshift-crossed-product` + `-proof`: PASS
- **Homomorphism.**
  - The rule π(f)δ_n = f(T^nx)δ_n gives σπ(f)σ^{-1}δ_n = f(T^{n-1}x)δ_n = π(f∘T^{-1})δ_n ✓.
  - π is additive and multiplicative on the free left module ✓.
- **Image.** π(e_a) = D_a. Translates and products of the e_a give cylinder indicators, so π(R) = R_x ✓.
- **Injective.** Take f_{j_0} = 1 on a nonempty clopen W. The orbit of x is dense in X, so T^{m+j_0}x ∈ W for some m. In π(r)δ_m = Σ_j f_j(T^{m+j}x)δ_{m+j} the coefficient of δ_{m+j_0} is 1 ✓.
- **Model tests.**
  - Primitive period N: R ≅ M_N(F_2[t^{±1}]). Since F_2[t^{±1}] is Euclidean, EL_{3N} = SL_{3N}. The group is residually finite and not simple ✓.
  - Constant x ✓.
  - Fibonacci word, with D_0 = 1 - D_1 ✓.

## 2. `sequence-el3-simple-iff-uniformly-recurrent-aperiodic` + `-proof`: PASS
- **Step 2 (minimal ⟺ uniformly recurrent).**
  - (⇐) Every word of y ∈ X is a word of x, and a word of y of length at least M(v) contains v. So L(y) = L(x), and x lies in the orbit closure of y ✓.
  - (⇒) A limit of windows avoiding v gives y ∈ X without v. Its orbit closure is proper ✓.
- **Step 3.** X is finite ⟺ x is periodic ✓.
- **Step 4.**
  - The e_12(σ^j) are distinct ✓.
  - Item 2 is the criterion `subshift-elementary-group-simple-iff-infinite-minimal` (review part 10 §3, PASS).
  - Item 3 is the theorem node, extended to n ≥ 3 by the routine change (review parts 7 and 11, A8/S1) ✓.

## 3. The note text (proposal part 1 §(a), §(b1); part 2 §(b2), §(b3), §(c)): PASS, with notes

**(a) Theorem.** It is true by §1–§2 ✓.
The remark is correct, apart from note N1 below.
- The ideal from a non-recurrent word is the set of Σ D_{P_j}σ^j whose P_j contain no word of y. The condition does not depend on the representative, because L(y) ⊆ L(x). The ideal is proper (1 is not in it) and nonzero (D_v, for a word v of x missing from y) ✓.

**(b1) Ring, (T), separated occurrences, simplicity, centre.**
- **Span.** σ^{-t}D_aσ^tδ_n = [x_{n+t} = a]δ_n. Products give every D_P, and D_Pσ^i·D_Qσ^j = D_P(σ^iD_Qσ^{-i})σ^{i+j} ✓.
- **Vanishing.** If P_j contains a word of x occurring at n, the δ_n-coefficient of rδ_{n-j} is 1 ✓.
- **Separated occurrences.**
  - Take 2k+1 ≥ M+L. Suppose a word u of that length occurs at p and p+d with 0 < d ≤ L.
  - Then u is d-periodic, so it has at most d ≤ L subwords of length L.
  - But u has length ≥ M, so it contains all p(L) > L words of length L of x, a contradiction.
  - Morse–Hedlund gives p(L) > L because x is not eventually periodic. A uniformly recurrent, eventually periodic sequence is periodic ✓.
- **Simple.**
  - D_vσ^jD_v = D_v(σ^jD_vσ^{-j})σ^j = 0 when the occurrences of v are more than |j| apart. And D_vD_{P_0}D_v = D_v, because v extends a word of P_0 centrally. So D_vrD_v = D_v ✓.
  - 1 - ∏_{0≤i<M}(1 - σ^iD_vσ^{-i}) = 1 by uniform recurrence ✓.
- **Centre.**
  - Compare δ_{m+j} coefficients: ([v at m+j] - [v at m])[x_{win(m+j)} ∈ P_j] = 0.
  - For each n, choose a long central word v of x at n with occurrences more than |j| apart. Then v occurs at n and not at n-j, so D_{P_j} = 0 for j ≠ 0.
  - Commuting with σ makes [x_{win(n)} ∈ P_0] constant ✓.

**(b2) Finite models.**
- w runs from the first occurrence to the second, which resolves sk-referee-1 G1 ✓.
- D^y_P is defined by the windows of y, which resolves G2 ✓.
- **Well defined.** Two representatives of the same element differ only on words that do not occur in x. The windows of y are words of x, so both give the same D^y ✓.
- **Preserved.** The covariance σ_ND^y_Pσ_N^{-1} = D^y_{P'} holds on the circle ✓.

**(b3) Towers.**
- σ^aD_Wσ^{-b}δ_{n+b} = [W at n]δ_{n+a} ✓.
- **Product rule.** For b ≠ c the product needs occurrences of v at n and at n+c-b, with 0 < |c-b| ≤ 2m. That is excluded ✓.
- **Absorption.** σ^iD_P·σ^aD_Wσ^{-b}·D_Qσ^j = σ^{a+i}D_{W'}σ^{-(b-j)}, where W' refines W by the conditions from P at offset a and Q at offset b ✓. It needs occurrences more than 2(m+w) = 2(2w+1) apart, but only 2m = 2w+2 is used for B_m(v), because the base ring is B_1(v) ✓.
- **Roots.** D_v = E_00(v), D_vσ = E_{0,-1}(v), D_vσ^{-1} = E_{01}(v) ✓.
- **Subring argument.** σ^{±1} = Σ_v D_vσ^{±1}, and D_a is a sum of D_v ✓.
- **κ.** ece ∈ M_d(C_v), and C_v ≅ LC(U_v,F_2) through §1. It is locally constant, so it is constant, equal to κ_0 ≠ I, on the occurrences of some long extension v' ✓.
- **H ⊆ G and H ⊆ N** as in the note ✓.
- **Level ideal:** D_{v'} ≠ 0 ✓.

**(c) Corollary edits.**
- ∏_t σ^{-t}D_{v_t}σ^t multiplies δ_j by [x_{[j,j+n)} = v] ✓.
- x_n = ⌊(n+1)α⌋ - ⌊nα⌋ is uniformly recurrent and not periodic for irrational α. Its language is that of the Sturmian subshift ✓.

**Notes (no GAP).**
- **N1.** The remark says "If $x$ has period $N$, then $R_x\cong M_N(\F_2[t,t^{-1}])$". This needs the least period N, which is what the bridge node says ("primitive period word"). Write "least period $N$".
- **N2.** (b2) says nonzero elements stay nonzero "since the exponents stay distinct modulo $N$". It also needs "and every word of $x$ of length $2k+1$ occurs in $y$". One clause fixes it.
- **N3.** (b3) writes E_ab(W)E_cd(W') = δ_bc E_ad(W∩W'). This holds if D_W means "some word of W occurs centered at n" and W∩W' means the set of words at which both occur. For sets of words of different lengths, set intersection is empty. Fix a common length, or say "W∧W'".
- **N4.** (b3) inherits sk-referee-1 G3. "Conjugation by $c$ on $H$ is conjugation by $\kappa_0$" needs the line "$c=(1-e)I_3+ece$, and every occurrence of $v'$ is an occurrence of $v$".
- **N5.** "occurs at n" means "centered at n" throughout (b1)–(b3). Say it once, next to the definition of D_P.
- **N6.** l.55 now reads "the algebraic crossed product of the orbit closure of $x$; see Nekrashevych". Whether Nekrashevych is the right locator is for sk-citations.

**Reader trade-off.** The mathematics is the same, and the proofs sections are about 30 lines shorter. The statement needs no subshifts, clopen sets, compactness or crossed products. The price is the remark linking it to minimal subshifts (+3 to +12 lines), and word-set bookkeeping in place of clopen sets. Which is clearer is main's call.

## 4. Status
- No GAP and no FAIL.
- Queue entry 35 is done.
