# EX review wave 2, part 2: dividing the unit over C-space boundaries, and Toms's twisted halves (2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0.

**Landings.**
- ex-tw-rotation-gluing: `ccd84801ac`, `add4b46ce2`, `62c3905409` and `6bd93b8b9a`.
- ex-rank-toms-b-obstruct: `c10da90ad6` and `61d456ae21`.

**Sources read.**
- `research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md` and its parts 2, 3 and 4.
- A. S. Toms, "Schubert calculus and uniform property Γ", arXiv:2606.12188v2, as extracted text (lane copy
  `ex-rank-toms-b-obstruct/lit/2606.12188.txt`):
  - Section 2 (pp. 5--6), Subsection 3.2 and Section 4 (pp. 6--8);
  - Lemma 1 with its proof (pp. 9--16), Lemma 2 (p. 17) and Theorem 2 (pp. 18--19);
  - Proposition 4 with its proof (pp. 20--23) and Theorem 5 (pp. 23--24).

## 2.1 Structure

- **Prerequisites.**
  - Every proof route of the four `bauer-*` division claims requires only
    `strict-comparison-unit-divisibility-equivalences`, which has a PASS (`ex-review-analysis-2026-09-12-part4.md`).
  - `bauer-c-space-strict-comparison-pure-and-z-stable` additionally requires
    `bauer-strict-comparison-pure-iff-divisible-unit` and `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`. Both
    have a PASS in the same part.
- **Consumers.** `toms-winter-holds-on-bauer-tlfnd-locus` stays open: its routes need
  `strict-comparison-forces-tracially-divisible-unit` or `r-fibre-w-star-bundles-divide-the-unit-uniformly`, both open.
- **The two rank-obstruct claims.** Each has a `requires: []` proof route with a complete body. The rank-problem
  roots stay open (index §0).

## 2.2 Part 1: facts (F2), (F5) and Lemmas 1--3 (the staircase): PASS

- **(F2).** λ(b) ≤ s + μ((s,1]). On (s, 1−s), x − x² ≥ s(1−s) ≥ s/2, and 1/(1−s) ≤ 1 + 2s for s ≤ 1/2.
- **(F5).** |λ(b²) − λ(B²)| ≤ |λ(b(b−B))| + |λ((b−B)B)| ≤ 2η by Cauchy--Schwarz. So the defects differ by at most 3η.
- **Lemma 1.**
  - π_{λ_0}(A)'' is a II_1 factor: λ_0 is extreme, A is simple and infinite-dimensional, and the trace is faithful.
  - The ideal of ‖·‖_{2,λ_0}-null bounded sequences is two-sided, by traciality.
  - Kaplansky approximants of matrix units give a unital *-homomorphism into the quotient. Projectivity of
    C_0((0,1]) ⊗ M_N lifts it to order zero maps, and continuity of λ ↦ λ(φ(1)) gives the open set.
- **Lemma 2.** θ(g_a) are central, orthogonal positive contractions. So Σ_a θ(g_a)φ_a is c.p.c. order zero, and
  (F1) evaluates it at λ ∈ C_a.
- **Lemma 3 (staircase).** Put e_j = φ(e_jj) and c_j = clamp(Nth(λ) − j + 1).
  - **Bounds.** B ≤ Σ e_j = φ(1) ≤ 1.
  - **(F4).** λ(e_j) = λ(φ(1))/N. Write e_j = a*a and hφ(e_11) = aa* with a = π(e_1j)h^{1/2} ∈ C*(φ(M_N)).
  - **(ii).** Σ_{j≤r} clamp(x − j + 1) = x for 0 ≤ x ≤ r. So λ(B) = t h(λ) λ(φ(1)) ∈ [t h(λ)(1−δ), t h(λ)].
  - **(iii).** By orthogonality, B − B² = Σ(z_j − z_j²)e_j + Σ z_j²(e_j − e_j²).
    - At most one c_j lies in (0,1), contributing at most 1/(4N).
    - Σ_j λ(e_j − e_j²) = λ(φ(1) − φ(1)²) ≤ λ(1 − φ(1)) < δ on supp h.
  - **(i).** Every c_j = 0 when h(λ) = 0.

## 2.3 `bauer-c-space-strict-comparison-divides-unit` (Theorem A, part 2 Section 3): PASS, one wording note

Re-derived step by step.
- **Choice of t.** (t − γ, t + γ) = (1/(n+1), 1/n), and 1 − t − ε ≥ 1/8.
  - With d_k = (ε/(16·2^k))², the costs satisfy Σ6s_k = 3ε/8 and Σ(6s_k + δ_k) ≤ ε/2.
- **Screening.** Property C gives finitely many disjoint levels. A shrinking plus Lemma 2 makes φ_k δ_k-good on
  supp h_k ⊆ W_k.
- **(R-up), active.** (th_k + η)(1 + 2s_k) + 4d_k/s_k ≤ th_k + 6s_k + 2η, using d_k/s_k = s_k.
- **(R-up), inactive.** η(1 + 2s_k) + 6η/s_k ≤ 8η/s_min.
- **(R-low).** λ(b_k) − σ ≥ th_k − δ_k − η − σ.
- **Moves.**
  - d_λ(F_{k−1}) ≥ μ_{W_{k−1},λ}({0}) = 1 − d_λ(W_{k−1}). The margin is ≥ 1 − t − 3ε/4 ≥ 1/8 at every extreme trace,
    so integrating ranks over μ_τ gives strict inequality at every τ.
  - Strict comparison and Rørdam's lemma give c_k with c_k c_k* = (x_k − ε'_k)_+ and c_k*c_k ∈ her(F_{k−1}).
  - F_{k−1}(W_{k−1} − ε_k)_+ = 0 makes her(F_{k−1}) orthogonal to (W_{k−1} − ε_k)_+.
- **Final rank.** Ranks add over orthogonal sums. d_λ(W) ∈ [t − 3ε/4, t + 3ε/4], using Σσ_k ≤ Σs_k + ε/8 and Lη ≤ ε/8.
  Integrating gives |d_τ(W) − t| < γ.
- **Division.** Strict comparison in M_n(A) and M_{n+1}(A) gives n[W] ≤ [1] ≤ (n+1)[W]. Item 3 of the
  equivalences gives item 1.
- **Wording note (no verdict change).**
  - The inductive hypothesis records only d_λ(w_i^{(k−1)}) = μ_{b_i,λ}((σ_i,1]). The step "subtracting ε_k raises
    σ_i by ε_k" needs the stronger form that the construction does supply: w_i^{(k−1)} = (c_i*c_i − r_i)_+ with
    r_i = Σ_{i<j<k} ε_j. Then d_λ((w − r)_+) = μ_{b_i,λ}((s_i + ε'_i + r_i + r, 1]) for all r ≥ 0, by (F3).
  - The owner was told.
- **Scope.** The recalled property C facts are not used in the proof, as the artifact says. Novelty against the
  literature was not checked here.

## 2.4 `bauer-c-space-strict-comparison-pure-and-z-stable`: PASS

Given §2.3, (e) ⟹ (a) of `bauer-strict-comparison-pure-iff-divisible-unit` gives purity. With nuclearity and
tracially locally finite nuclear dimension, (e) ⟹ (a) of `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit` gives
Z-stability. Both theorems have a PASS. The scope bullets correctly mark as recalled that there exist C-space compacta
which are not countable unions of finite-dimensional ones.

## 2.5 `bauer-strict-comparison-unit-division-is-local` (Proposition D): PASS

Compactness fixes L first. One precision (N, δ) with L(6d^{1/2} + δ) ≤ ε/2 makes the level sums of §2.3 at most ε/2.
Each Y_k carries a δ-good order zero map into A, so Lemma 2 is not needed. Steps 3--7 apply verbatim.

## 2.6 `bauer-unit-division-iff-summable-local-division` (Theorem E): PASS

- **(a) ⟹.** Take N ≥ 4/ε² and δ = ε²/4, so ω ≤ ε/√2.
- **(a) ⟸.**
  - s_i ≤ ω_i, and δ_i ≤ ω_i since δ_i ≤ 1.
  - Only members with h_i(λ) > 0, hence λ ∈ O_i, enter the sums at λ. So the overshoot is at most 8Σ_{λ∈O_i} ω_i.
  - η and the cut levels are chosen after the finite family.
- **(b).** The complement of Z_sum is open. Finitely many summably divisible Y_j with (ε/m)-summable families give an
  ε-summable cover of K.
- **(c).** Property C of Y gives disjoint levels. Disjoint compact C_{k,a} have disjoint open neighbourhoods, which are
  intersected with the division sets. At any λ ∈ K at most one member per level contains λ, so the weights sum to at
  most Σ_k ε2^{−k}.
- **(d).**
  - A closed C-neighbourhood F of λ in Z gives an ε-summable family covering F.
  - The compact set cl B ∖ ∪𝓕 misses Z, so it is covered by finitely many summably divisible Y_j. Their families are
    taken (ε/m)-summable after m is known.
  - So cl B is summably divisible, a contradiction.
  - Closed heredity of property C gives Z ⊆ X_C, and transfinite induction gives Z ⊆ K^{(C,∞)}.
- **Proposition 10.1 (nuclear remark).** Constant matrix units in a trivial M_Y lift through the Evington--Pennig
  restriction q_Y. Order zero lifting along ℓ^∞(A) → ℓ^∞(A)/c_Y makes Y a division set at every precision.

## 2.7 `bauer-unit-division-metric-order-criterion` (Lemma 8.1, Proposition 8.2, Corollary F): PASS, one wording note

- **Lemma 8.1.** On (0,σ], x ≤ (x − x²)/(1 − σ) ≤ 2(x − x²). So λ(b) ≤ 2λ(b − b²) + μ((σ,1]).
- **Proposition 8.2.**
  - Upper: t(1 + 2s) + 2κ/s + 16mη/s ≤ t + 5ε_0/8, with s = ε_0/8 and κ = ε_0²/64.
  - Lower: t − 3κ − 7mη, using δ_i + 2d_i ≤ 3(1/N_i + δ_i) on active members.
  - Margin: ≥ 1 − t − 5ε_0/8 ≥ 1/8.
- **Corollary F.** A cover of mesh below ℓ_A(ω) has members inside division sets of weight ≤ ω. Its order bounds the
  weight sum.
  - Hilbert cube: [0,1]^D with D = ⌈log_2(4/r)⌉ has covers of order D + 1 and mesh r/2. Tails add ≤ 2^{−D} ≤ r/4.
  - Witness bound: ℓ_A(ω) ≤ 16·2^{−2c/ω} ≤ 2^{−c/ω} for small ω.
- **Wording note (no verdict change).**
  - The per-member lower bound is stated for all members. The displayed sum t − 3κ − 7mη is correct only if inactive
    members use the trivial bound μ ≥ 0, since Σ_all δ_i is not controlled by κ.
  - The same reading is needed in Theorem E(a) ⟸ ("sums range over active members"). With it both proofs are
    complete.
  - The owner was told.

## 2.8 `toms-diagonal-quotient-has-nonconstant-continuous-ranks`: PASS

Construction and Lemma 2 checked against Toms pp. 7--8 and 17. In Lemma 2 the points x_{r+1} = (x_r, x_r, ℓ_r), with
arbitrary ℓ_r, lie in D_{r+1}.
- **Step 1.** q_L splits into N = 2^{L−1} leaf projections of fibre rank d, and φ_L(1_l) = 1_{l0} + 1_{l1}.
  - k_{l0} = 2k_l − 1 and k_{l1} = 2k_l, so ‖b_{L+1} − φ_L(b_L)‖ = 1/(2N).
  - τ(g(b_L)) is a Riemann sum for every trace, since every trace on A_L integrates normalized fibre traces.
- **Step 2.** φ_L(a)|_{D_{L+1}} depends only on a|_{D_L}. So restriction defines the quotient.
- **Step 3.** On D_L all leaf coordinates coincide, so φ_{1,L}(h q_1) = h(y) q_L is central.
  - The mixed moments factor, giving joint law Lebesgue × ν.
  - Hence d_τ((b − (1−h))_+) = ∫ t dν = τ(h), non-constant at the point traces τ_y.
- **Step 4.** T_P ⊕ T_{P′} vanishes only where S_y = P^⊥ = P′^⊥, which is impossible. The N diagonal summands
  Hom(θ^d ⊗ γ_l, S ⊗ γ_l) = S^{⊕d} make c_top divisible by (c_d(S)^d)^N = 0 for N ≥ 2.
- **Step 5 (model test).** Along the diagonal extension of x, b and h commute, and b ≤ φ(b_L) leafwise. So
  (b − (1−h))_+ vanishes at every stage point.

## 2.9 `toms-twisted-swap-pairs-are-totally-degeneracy-forcing`: PASS, one wording note

- **Step 1.** The roots of E_2 ⊗ E_1* are β_j − α_i − u, with u = c_1(O(1) ⊗ O(2)^{−1}) = c_1(O(−1)).
  - Δ_w(c(E_2 − E_1)) = c_{w²}(E_2 ⊗ E_1*) is Toms's Section 2 identity (p. 6).
  - The u^{w²} term has coefficient ±1 and is the only term of top CP-degree. It is nonzero iff w² ≤ j_r = 2d_r².
- **Step 2.** Toms's proof of Lemma 1 (pp. 11--16) uses exactly Δ_n ≠ 0, torsion-free Künneth, injectivity of π_1^*
  and π_2^*, and y_i^{2n²} ≠ 0.
  - So it propagates any rank-n pair with 2n² ≤ j_i.
  - Starting from n = w ≤ √2 d_r ≤ d_{r+1}, ranks and d_i both double.
- **Step 3.** The fibre fraction is w2^{n−r−1}/(k d_r 2^{n−r}) = w/(2kd_r) at every point.
- **Step 4.**
  - y_n = φ(E_2) x φ(E_1) vanishes at x_0.
  - z ↦ τ((E_1 − z*z)²) is 4-Lipschitz on contractions.
  - An exact equivalence would give corner contractions with ‖E_1 − y*y‖_{2,u} ≤ 2‖V − y‖_{2,u} → 0.
- **Step 5 (in B).** Let F_i = ψ_{m+1,n}(E_i), G_i = E_{n,m}F_i E_{n,m}, and η_m = Σ_{r≥m}(1 − α_r) as in the o6-plus
  artifact. Toms's Proposition 4(5) proof gives σ(1 − E_{n,m}) ≤ η_m.
  - Compress **on the left only**: c = E_{n,m} y_n = G_2 x F_1. Then y_n*y_n − c*c = F_1x*(F_2 − G_2)xF_1, whose
    ‖·‖_{2,u} is at most τ(F_2 − G_2)^{1/2} ≤ √η_m.
  - At x_0 the topological map G_2 x G_1 vanishes. So the compression of F_1 − c*c to G_1(x_0) is the identity, and
    Tr(A²) ≥ Tr((PAP)²) gives tr_{x_0}((F_1 − c*c)²) ≥ tr(G_1(x_0)) ≥ δw/(2kd_r).
  - μ({x_0}) ≥ δ (Proposition 4(3)) gives ‖F_1 − c*c‖_{2,u} ≥ δ(w/(2kd_r))^{1/2}. Here F_1 = E_1 in B, so the bound
    holds with −√η_m.
- **Wording note.**
  - A two-sided compression G_2 x G_1 costs up to 5√η_m.
  - The written "compress x by the top-branch projection" should say "on the left", as Step 3 of the o6-plus
    artifact does. Only the constant is at stake.
  - The owner was told.
- **Dilution correction.** The node's correction of the dilution heuristic follows from part 1. Swapping in all copies
  gives a bundle map between pushforwards, which vanishes somewhere.
