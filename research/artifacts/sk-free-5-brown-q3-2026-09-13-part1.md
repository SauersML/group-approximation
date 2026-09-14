# sk-free-5: Brown's Question 3, weakly dense QD and Popa subalgebras of II_1 factors (2026-09-13, part 1)

Lane sk-free-5 (wave 10, free lane, operator algebras). Sources were read from arXiv e-print sources on MSI (`/scratch.global/sauer354/sk/sk-strong-7/br/src`, `/scratch.global/sauer354/sk/sk-free-5/bdx/x`) unless stated otherwise.

## 0. Verdict
- **T1, ESTABLISHED (unreviewed).** Every II_1 factor with separable predual contains a weakly dense unital C*-subalgebra isomorphic to the full group C*-algebra `C*(F_∞)`. It is residually finite-dimensional, hence quasidiagonal, and has the local lifting property.
  - This answers the QD clause of Brown's Question 3 positively for every separable II_1 factor: the property (T) factor `L(G_X)` of the note, `L(SL_3(Z))`, the free group factors, and factors not embeddable in `R^ω`.
  - Node: `separable-ii1-factors-have-weakly-dense-full-free-group-cstar`; proof in route `separable-ii1-factors-weakly-dense-free-group-cstar-proof`.
- **Lemma S, ESTABLISHED (unreviewed).** In `L(G)` for an ICC Kazhdan group `G`, a projection `p` of a C*-subalgebra `A` that almost commutes in norm with 2-norm approximants `y_s ∈ A` of the Kazhdan generators, with finite-dimensional compressions, has `τ(p) ≤ 4ε_S^{-2}(4η + 2δ)²`.
  - So any weakly dense Popa algebra in a property (T) group factor hides its finite-dimensional structure on corners of vanishing trace.
  - Node: `kazhdan-group-factor-popa-corners-have-vanishing-trace`; route `kazhdan-group-factor-popa-corners-vanishing-trace-proof`.
- **T2, OPEN.** Does some property (T) factor contain a weakly dense Popa algebra? `property-t-factors-contain-weakly-dense-popa-algebras`, with Attempts.

## 1. The question and its context (verbatim)

**Brown, *Tracial invariants, classification and II_1 factor representations of Popa algebras*, arXiv:math/0111286 (v3, 2002-03-13), §Questions, item 3:**
> "Can a free group factor or a II$_1$ factor with property T
> contain a weakly dense, QD C$^*$-subalgebra? How about a Popa algebra?
> Our constructions always give McDuff factors (so we have some place to
> hide the Popa algebra).  Note that amenability can't be an obstruction
> since $L(G_1 \times G_2) \cong L(G_1) \bar{\otimes} L(G_2)$ and hence
> many non-amenable groups give McDuff factors and hence contain dense
> QD subalgebras by Theorem \ref{thm:arbitraryMcDuff}."

**The same paper, Theorem `thm:arbitraryMcDuff` and its proof (source l.2741ff):**
> "There exists a Popa algebra $A$ with the property that for each McDuff
> factor, $M$, there exists a trace $\tau_M \in \TA$ such that
> $\pi_{\tau} (A)^{\prime\prime} \cong M$."
> Proof: "Since every II$_1$ factor arises as the weak closure of a GNS
> representation of $C^* ({\mathbb F}_{\infty})$, and $C^* ({\mathbb
> F}_{\infty})$ is residually finite dimensional, this theorem follows
> from Theorem \ref{thm:basicconstruction}."

The GNS representations there are quotient maps of `C*(F_∞)`. The McDuff tensor factor `R` is where the Popa algebra is hidden.

**Brown–Dykema, *Popa algebras in free group factors*, arXiv:math/0207005, introduction (source l.205–240):**
> "By definition, a Popa algebra is a unital, simple C$^{*}$-algebra $A$ with
> the property that for every finite set $\mathfrak{F} \subset A$ and
> $\epsilon > 0$ there exists a finite dimensional subalgebra $0 \neq B
> \subset A$ (the inclusion not necessarily unital) with unit $e$ such
> that $\| [x,e] \| < \epsilon$ for all $x \in \mathfrak{F}$ and for
> each $x \in \mathfrak{F}$ there exists $b \in B$ such that
> $\| b -  exe \| < \epsilon$."

> "It was shown in~\cite{brown:AFDtraces} that all McDuff II$_1$--factors
> have weakly dense Popa algebras, but with Property~(I) above, our
> construction yields the first non--McDuff example, which thus answers
> Question~11.1 in~\cite{brown:AFDtraces}.  Since $A_s$ is a Popa
> algebra, it is quasidiagonal (...) and thus quite distinct from previously known
> weakly dense C$^*$--subalgebras of $L(\Fb_s)$ that arise as reduced
> free products of C$^*$--algebras."

**Brown, *Invariant means and finite representation theory of C*-algebras*, arXiv:math/0304009v2, §1.3.** This was read through WebFetch of the arXiv HTML, not against the source:
- "every McDuff factor contains a weakly dense Popa algebra (Theorem 5.3.3)";
- "all the (interpolated) free group factors L(F_n) (1<n<∞) contain finitely generated, weakly dense Popa algebras".

**Brown, same paper, the Corollary after Theorem `arbitraryMcDuff`, items (4)–(6) (source l.2772–2785):**
> "\item There exists a sequence of II$_1$ factors, $R_n \subset
> B(L^2(M))$, such that $R_n \cong R$ for all $n$ and for each $a \in A$
> we can find $x_n \in R_n$ such that $\| a - x_n \| \to 0$.
> \item There exists a sequence of normal, u.c.p. maps $\varphi_n : M
> \to M_{k(n)} ({\mathbb C})$ such that $\| \varphi_n (ab) - \varphi_n
> (a) \varphi_n (b) \|_2 \to 0$ for all $a,b \in A$.
> \item There exists a completely positively liftable u.c.p. map $\Phi :
> M \to R^{\omega}$ such that $\Phi|_A$ is a $*$-monomorphism."

Items (1)–(3) of the same Corollary:
- (1) is a 2-norm local finite-dimensional approximation, `‖E_B(exe) − (x − e^⊥xe^⊥)‖_2 < ε‖e‖_2`;
- (2) is finite-rank projections almost commuting in norm;
- (3) is a state on `B(L²(M))` whose centralizer contains `A`.

The memoir version (math/0304009, l.4715ff) says: "With the exception of statement (3), all assertions above follow from the quasidiagonality of $A$ (identified with a weakly dense subalgebra of $M$)."

## 1b. Statement fidelity
- **The question has no further condition.**
- **No trace condition can be meant.** An amenable trace on a weakly dense subalgebra forces injectivity (memoir, l.4636: "Since $A$ is quasidiagonal $\tau$ must be a quasidiagonal trace. In particular, it must be an amenable trace and hence ... produce the hyperfinite II$_1$-factor in the GNS construction", in the unique-trace, locally reflexive case). Yet Brown–Dykema answer the free group factor case positively with a QD algebra.
- **T1's algebra has all six listed properties:**
  - (1) exactly on polynomials, through the corners `q_j` (errors scale with `‖e‖_2` under norm approximation);
  - (2), (3), (5), (6) from quasidiagonality;
  - (4) because T1 applied inside `R` embeds `C*(F_∞)` in `R`, and Voiculescu's theorem gives approximate unitary equivalence of the two essential faithful representations.
- **What T1's algebra lacks is simplicity**, which is the second clause.

## 2. Theorem T1
**Statement.** `M` is a II_1 factor with separable predual. There is an injective unital *-homomorphism `π : C*(F_∞) → M` with `π(C*(F_∞))'' = M`.

**Proof outline** (complete proof in the route node):
1. **Norming family.** Take a norming sequence of finite-dimensional representations `ρ_j` of `C*(F_∞)`, each repeated infinitely often, so that `sup_{j≥m}‖ρ_j(x)‖ = ‖x‖` for every `m`. It exists because `C*(F_∞) ⊆ C*(F_2)` is residually finite-dimensional (Choi 1980).
2. **Corners.** Take orthogonal projections `q_j` with `τ(q_j) = 2^{-j-1}`, and put `e_i = 1 − Σ_{j≥i}q_j`. Fix unital embeddings `M_{d_j} ⊂ q_jMq_j`.
3. **Generators.** `z_i = w_i + Σ_{j≥i}ρ_j(a_i)`, where `w_i ∈ U(e_iMe_i)` is within `2^{-i/2}` in 2-norm of `e_iy_{κ(i)}e_i`. Here `(y_k)` generates `M`, and `κ` has infinite fibres (Lemma U: polar decomposition in a finite algebra).
4. **Injective.** For a word in the first `m` generators, each `q_j` with `j ≥ m` reduces it with compression `ρ_j(x)`. So `‖π(x)‖ ≥ sup_{j≥m}‖ρ_j(x)‖ = ‖x‖`.
5. **Weakly dense.** `‖z_i − y_k‖_2 ≤ 5·2^{-i/2}` for `i ∈ κ^{-1}(k)`, so `y_k` is a strong limit of elements of `π(C*(F_∞))`.

**Remarks.**
- **(R1) QD, MF, LLP.** The image is QD and MF and has the LLP. Brown–Dykema's Popa algebras `A_s` are finitely generated and simple; T1's algebra is neither.
- **(R2) The subalgebra avoids the group.** For a non-amenable ICC group `Γ`, a QD subalgebra of `L(Γ)` contains no copy of `C*_r(Γ)` (Rosenberg; QD passes to subalgebras). So T1's algebra is far from `λ(Γ)`, in line with Brown–Dykema's remark.
- **(R3) No embeddability information.** QD weakly dense subalgebras carry no information about `R^ω`-embeddability. T1 holds for every separable II_1 factor, including non-Connes-embeddable ones (which exist by MIP* = RE). The trace `τ∘π` on `C*(F_∞)` is then not liftable, which is consistent, since the trace of a QD algebra need not be quasidiagonal.
- **(R4) Why Brown's second clause is different.** A Popa algebra is simple, and its approximating corners must almost commute in norm with finite sets that approximate generators. Lemma S shows that in property (T) group factors those corners have vanishing trace. In T1's algebra the corners `q_j` exactly reduce finitely many generators, with finite-dimensional compressions, but the algebra is not simple.
- **(R5) Model test of Lemma S on T1.** Corners `q_j` with `j ≥ m ≥ i` serve the generators `z_1, …, z_m` with `η = 0`, and `δ ≈ 5·2^{-i/2}`. Lemma S allows traces up to `400ε_S^{-2}2^{-i}`, and indeed `τ(q_j) ≤ 2^{-i-1}`. Consistent.

## 3. Lemma S (vanishing Popa corners in property (T) group factors)
**Statement.** Let `G` be ICC with property (T), `(S, ε_S)` a Kazhdan pair, `M = L(G)` and `A ⊆ M` a C*-subalgebra. Suppose:
- `y_s ∈ A` with `‖y_s − λ_s‖_2 ≤ δ` for `s ∈ S`;
- `p ∈ A` is a nonzero projection, and `B ⊆ pAp` is a finite-dimensional C*-subalgebra with unit `p`;
- `‖[p, y_s]‖ ≤ η` and `dist(py_sp, B) ≤ η` for `s ∈ S`.

Then `τ(p) ≤ 4ε_S^{-2}(4η + 2δ)²`.

**Proof** (route node):
1. **Spectral gap.** The conjugation representation on `L²(M) ⊖ C1 = ℓ²(G∖{e})` has no invariant vectors (ICC). So `‖x − τ(x)‖_2 ≤ ε_S^{-1} max_s ‖[λ_s, x]‖_2` for all `x ∈ M`.
2. **A relative-commutant projection.** With matrix units of `B`, build a projection `e ∈ B′ ∩ pMp` with `τ(e) = τ(p)/2`, using halving projections in the II_1 corners `f^{(r)}_{11}Mf^{(r)}_{11}`.
3. **Almost commutation.** In norm, `‖[e, y_s]‖ ≤ ‖[e, py_sp]‖ + ‖py_s(1−p)‖ + ‖(1−p)y_sp‖ ≤ 2η + η + η`. The term with `(1−p)y_s(1−p)` commutes with `e ≤ p`.
4. **Conclusion.** `(τ(p)/4)^{1/2} ≤ ‖e − τ(e)‖_2 ≤ ε_S^{-1}(4η + 2δ)`.

**Consequence for Popa algebras.** Let `A ⊆ L(G)` be a weakly dense Popa algebra and `δ > 0`.
- Kaplansky density gives `y_s ∈ A` with `‖y_s‖ ≤ 1` and `‖y_s − λ_s‖_2 ≤ δ`.
- Every Popa corner for `F = {y_s}` at tolerance `η` has trace `≤ 4ε_S^{-2}(4η + 2δ)²`.
- For a full II_1 factor, replace `λ(S)` and `ε_S` by a spectral-gap set of Connes (J. Funct. Anal. 16 (1974); recalled, locator not checked).

## 4. T2 status (Popa algebra in a property (T) factor)
Attempts, recorded on the open node:
- **(a) T1's algebra.** Popa's approximation holds on the corners `q_j`, but the algebra is not simple. No simple QD hull inside `M` was found.
- **(b) The property (T) bimodule argument.** The vector `(p ⊗_B p)/τ(p)^{1/2}` in `L²M ⊗_B L²M`, a subbimodule of a multiple of the coarse bimodule, is almost central at relative scale `η` for the finite set.
  - The Kazhdan set of `M` need not lie in `A`. Transferring 2-norm approximations costs `‖y − y′‖_2/τ(p)^{1/2}`, which diverges on the vanishing corners of Lemma S.
  - So the argument dies at weak density.
- **(c) The tower structure of `G_X`.** `G_X = ⟨L_y, L_{y′}⟩`, with `L_y` a union of finite groups `GL_3(A(𝒫_n))` (route of `subshift-elementary-groups-are-character-rigid`), so `L(G_X)` is generated by two hyperfinite subalgebras.
  - Brown–Dykema use free product structure of `L(F_s)` and residual finite-dimensionality of full amalgamated free products of matrix algebras.
  - An analogue would need the two hyperfinite algebras in a position whose full C*-hull keeps finite-dimensional representations on vanishing corners. Not attempted in this part.

## 5. Novelty (bounded)
- **Read at source:** Brown math/0111286 (§Questions, Theorem arbitraryMcDuff); Brown–Dykema math/0207005 (introduction).
- **Read through WebFetch:** Brown math/0304009v2 §1.3.
- **Six web searches**, on: weakly dense QD or RFD subalgebras of II_1 factors; Brown's question; Popa algebras in property (T) factors; full group C*-algebra embeddings.
- **What I found:**
  - no statement that every separable II_1 factor contains a weakly dense copy of `C*(F_∞)`;
  - no answer to either clause of Q3 for property (T) factors;
  - on main, sk-answered-questions part1 marks Q3 as not answered.
- **Not checked:** MathSciNet citations of Brown math/0111286; Hadwin's and Shulman's RFD papers. T1 is elementary, so a prior remark is plausible, and the claim node says "not found in the bounded search", not "new".
