# sk-open-2 plan (2026-09-13): one page that proves everything

**Target.** A complete proof of Theorem 1 of `simple_kazhdan_sofic_group.tex`: G_X = EL_3(LC(X,F_2) ⋊ Z) is infinite, finitely generated, simple, Kazhdan and LEF, so sofic and hyperlinear.
- It must fit on ONE printed page in the note's own format (amsart 11pt, margins 1.15in).
- It must be exactly as rigorous as the current proof (disk l.67-227, about 2.5 pages).
- It comes with an honest verdict on whether a different ring or group would give a shorter proof.

**Why this matters.** A famous question is answered by a short argument. At one page, every reader can check the whole argument in one sitting, and the note's claim to elegance becomes visible.

**Changes to the architecture, not to wording:**
- A1. "R is simple" and "Z(R) = F_2" are dropped as separate facts.
  - The level-ideal step only needs this: an ideal containing a nonzero e_W contains 1, because finitely many translates of W cover X.
  - The existence of a local transvection that fails to commute with g is a direct computation of a few lines. Summing over a clopen partition gives g = cI. Comparing coefficients against e_C and e_C u shows that c is T-invariant, so c is constant and g = I.
- A2. The level ideal is taken over all positions: {r : e_ij(r) ∈ N for all i ≠ j}. The commutator formula gives closure under two-sided multiplication, so no permutation matrices are needed.
- A3. H_W ⊆ G: transvections between different blocks are e_pq(E_ab(W)), and the identity [t_xz, t_zy] = t_xy in GL_d(F_2) gives the rest. The ring computation with E_bb goes away.
- A4. The finite models become maps ρ_k: R → M_N(F_2) that are additive, multiplicative on any fixed pair once k is large, and nonzero on any fixed nonzero element once k is large. This replaces the "finite list of sums and products" bookkeeping.
- A5. The partition in the simplicity step need not refine the letter partition.

**Radical alternatives to test and record (firewalls):**
- Other finitely generated infinite simple rings over finite fields. Candidates and expected verdicts:
  - Leavitt algebras: not LEF.
  - Group rings: never simple.
  - Quantum tori over F_q: finite over the centre.
  - Weyl algebras in characteristic p: not simple.
  - Odometer crossed products: not finitely generated, so EJZ does not apply.
  - Toeplitz or Z^d crossed products: same proof, not shorter.
  - Direct limits of matrix rings: not finitely generated.
- Simplicity through the normal subgroups of an ultraproduct of finite simple groups: this does not control normal subgroups of a subgroup.
- Soficity from approximate models without the periodic-word lemma: normalized-rank closeness in GL_{3N}(F_2) gives no permutation closeness on F_2^{3N}, since fixed-point sets are exponentially small.
- Simplicity by citing a stable-range sandwich theorem: owned by sk-stable-rank-a/b. Not duplicated here.

**What this lane does not duplicate:**
- sk-proof-minimal-concrete and -conceptual rewrite within the existing structure.
- sk-simplicity-short-a/b and sk-lef-short each own one step.
- This lane restructures the whole proof (A1–A5) and tests the result against one printed page with a pdflatex probe on MSI, in the note's preamble.

**Deliverables:**
- `research/artifacts/sk-open-2-proposal-2026-09-13.md`: the full candidate LaTeX for §1, line and page counts, and trade-offs.
- A verification artifact covering every step.
- A review request in `queue/sk-referee-1.txt`.
