# EX review wave 2, part 7: Baum--Connes at Bernoulli coefficients, Deligne imports, the wreath no-go and Cuntz suprema (2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0. This part covers the census
claims of ex-bc-measured-coefficient (3), ex-bc-module-monster (3), ex-nh-deligne-hs (3), ex-hs-instability-extension (1)
and ex-rank-toms-b-construct (1).

**Sources re-checked on MSI.** The lanes' PDFs were extracted with ghostscript into
`/scratch.global/sauer354/ex/ex-verify2-analysis/`, or their existing extractions were used.
- Chakraborty--Echterhoff--Kranz--Nishikawa, arXiv:2210.09209: Theorem 2.8 is verbatim, "for each countable G-set Z,
  there is a weak K-equivalence ... If G moreover satisfies BCC, there is an isomorphism". So Baum--Connes enters
  only the second sentence, as the node says.
- Bönicke--Dell'Aiera, arXiv:1810.04415: Theorem 4.6 is verbatim.
- Finn-Sell, arXiv:1401.6841: Theorem 3.7 ("fails to be a surjection, but is an injection") and Corollary 4.4 are
  verbatim.
- Bachner--Dogon--Lubotzky, arXiv:2508.17392: Theorem 1.3, Proposition 1.5 and the degree-4 cover sentence are
  verbatim.
- Bader--Lubotzky--Sauer--Weinberger, arXiv:2303.08943: Corollary 2.14 is verbatim, and Theorem 2.10 is present.
- Stover, arXiv:2407.07680: Theorem 1.5 and "the intersection of the kernels of all homomorphisms from Γ_n onto finite
  groups is 2Z" are verbatim.
- Not re-read here: Chabert--Echterhoff 2001 and the Osajda papers. Their quotes are the lanes' readings.

**Roots.** `baum-connes-counterexample-group-exists` and `non-hyperlinear-group` stay open.
- The Bernoulli claims reduce the module route to one comparison map. They prove no failure.
- `kt-wreath-models-never-round-on-the-vertex` gives an equivalence at wreath-extendable models, not
  non-hyperlinearity.

## 7.1 `bernoulli-shift-weak-k-equivalence-and-going-down`: PASS

- **Item 1.** CEKN Theorem 2.8 with A_0 = C, A = C(Λ) and B = C(Λ ∖ {0}). ι ⊕ φ is a KK-equivalence C ⊕ B → A, and the
  F = ∅ component is the unit, from their proof.
- **Item 2.** Bönicke--Dell'Aiera Theorem 4.6 applied to discrete groups: the compact open subgroupoids are the finite
  subgroups, and the unit space is a point. Green--Julg for finite H is standard.
- **Item 3.** The generalized Green--Julg theorem for proper algebras, as recorded in CE01. Not re-read.

## 7.2 `bernoulli-bc-splits-into-host-and-cylinder-comparison`: PASS

- **Lemma E.** A kernel element lifts to A ⋊_max G, dies in B ⋊_max G, and lies in I ⋊_max G. The case B = c_0(Y) with
  finite stabilizers uses Green imprimitivity.
- **Item 1.** Evaluation at the fixed configuration 0 is split by the unit, so C(X) ≅ I_1 ⊕ C in KK^G, and assembly
  splits.
- **Items 2--3.** Restricting Φ to finite H gives a block triangular matrix, so T is a weak K-equivalence. Going-down
  plus proper coefficients make both left factors of μ_{G,I_1} ∘ K^top(T) = T_r ∘ μ_{G,c_0(S)} bijective.
- **Item 4.** Over torsion-free G a weak K-equivalence is a K-isomorphism. Inclusion--exclusion makes the cylinders a
  Z-basis of C_c(X ∖ {0}, Z), and free orbits give ⊕Z with K_1 = 0.
- **Item 5** is the five lemma along support levels.
- **Item 6** is the amenable-kernel transfer. That import is unreviewed; see Notes.
- **Item 7.** Finite subgroups of F_p ≀_Z G lie in ⊕F_p for torsion-free G, so Λ = Z[1/p]. The Haar trace of a cylinder
  over F is p^{−|F|}. Lück's theorem is an unreviewed import.

## 7.3 `bernoulli-assembly-injective-beyond-the-host`: PASS, every host re-derived

Checked against `research/artifacts/bc-bernoulli-rank-functionals-torsion-2026-09-13.md`.
- **Claim W.** Finite windows I_1^W ≅ C(Λ^W ∖ {0}) exhaust I_1, and K_*(− ⋊ H) commutes with the limit.
  - At level W both sides are ⊕_{[t]} R(H_t).
  - The image of δ_s p_σ splits over the H_s-orbits extending s. The orbit {s} returns [σ], and every other orbit has
    larger support. So the matrix is block unitriangular.
- **R1'.** Induction from the finite G_x preserves weak containment into the regular representation. π_{x,σ}(f) has
  finite rank, since g x ∈ U_z allows at most |supp x|·|G_z| elements g.
- **R2'.** π(1_{C_s}) is G_s-invariant, and the rank of π(1_{C_s} p_τ) is the multiplicity of τ. Same-size cylinders
  see only the orbit of x.
- **R3'.** Take a minimal-size nonzero component m_{[s']}. Pairing with every irreducible σ of G_{s'} kills every
  coefficient of the virtual representation.
- **Torsion-free anatomy (R5--R8).** Möbius inversion, truncation via Lemma E, and additivity for B-separated patterns,
  obtained through spectral projections of a locally constant approximant. The three shapes follow.
- **Model test.** Z/2 on Z = G gives source Z³ = target Z³, with unitriangular T_r.

## 7.4 `module-defect-needs-non-k-exact-host`: PASS

- **Part 1.** Half-exactness of K^top, naturality of assembly and three vertical isomorphisms transport middle
  exactness. So Baum--Connes with coefficients implies K-exactness.
- **Part 2.** The contrapositive for the module triple, plus Kirchberg--Wassermann for exact groups.
- **Part 3.** Osajda's Theorem 6.3 groups act properly on CAT(0) cube complexes (Haagerup, non-exact). Higson--Kasparov
  gives Baum--Connes with all coefficients, so they are K-exact.
- The "only embedded expanders are known" sentence is a bounded status statement with dated corrections.

## 7.5 `monster-bc-detector-lives-on-a-proper-orbit-ideal`: PASS as an import

- Finn-Sell's Theorem 3.7 and Corollary 4.4 are verbatim. Theorem 3.8's ladder with C_0(Ω_X) ⋊_r Γ ≅ K is consistent
  with the section heading read.
- The node's restriction to Finn-Sell's coarse-embedding definition, and hence to Osajda's isometric-expander hosts, is
  correctly stated.

## 7.6 `osajda-monster-hosts-for-bc-module-route`: PASS as an import, not re-read here

The quotes are the lane's readings of Osajda arXiv:1406.5015 and 1703.03791. The two dated corrections, weak versus
coarse embedding and residually finite relators that are not expanders, are consistent with Finn-Sell's remark quoted
in §7.5.

## 7.7 Deligne and stability imports: three PASS

- **`bdl-deligne-type-two-norm-inapproximability`: PASS.** Theorem 1.3, Proposition 1.5 and the degree-4 cover
  sentence are verbatim.
  - The mechanism paragraph (rounding J to an exact involution, which costs only 2n^{−1/2} in normalized HS) is
    correct.
  - It correctly does not claim hyperlinearity results.
- **`blsw-real-lattice-frobenius-stability`: PASS.** Corollary 2.14 is verbatim, and Theorem 2.10 is present.
  - The scope fence is correct: Sp_4(R) has real rank 2, so Deligne's triple cover of Sp_4(Z) lies outside Theorems 1.3
    and 2.10.
- **`deligne-covers-of-sp2g-z-have-finite-residual-2z`: PASS.** Stover's Theorem 1.5 and the 2Z sentence are verbatim,
  and the kernel reading is forced.
  - Re-derived: every finite quotient of Γ~ kills some z^{n′}, so it factors through Γ_{n′} and kills z². Hence
    2Z ⊆ Res_fin(Γ~).

## 7.8 `kt-wreath-models-never-round-on-the-vertex`: PASS, conditional on five unreviewed premises

- **Step 5, re-derived.**
  - e_Γ is fixed by Γ, so σ(e_Γ) ∈ N = σ(Γ)′ ∩ M. Normalization puts σ(e_{t_0Γ}) in N, so it commutes with σ(γ), and
    σ(e_{γt_0Γ}) = σ(e_{t_0Γ}).
  - These are distinct lamps, so trace preservation gives ‖σ(e_a) − σ(e_b)‖²_2 = 2 − 2Re τ(σ(e_a e_b)) = 2. That is a
    contradiction.
- **The diagonal form** is the standard ultrafilter selection with k(n).
- **Corollary 1.** (H1) at wreath-extendable models ⟺ no wreath-extendable model exists, vacuously. A trace-preserving
  model of W exists iff W is hyperlinear.
- **Premises.** Steps 1--4 rest on five established claims with no PASS line in any review:
  - `nonunit-projection-bounded-by-root-spectral-mass`;
  - `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`;
  - `vertex-rounding-deep-nonunit-root-mass-vanishes`;
  - `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`;
  - `kun-thom-wreath-carries-rigid-defect`.

  They lie outside this lane's census and were not re-derived.
- **What it does not do.** It establishes no non-hyperlinearity. `non-hyperlinear-group` still needs (H1) for every
  model, which is open.

## 7.9 `cuntz-sups-with-continuous-rank-converge-uniformly`: PASS

- **Step 1.** h_{1/j}(t) = min(1, j(t − 1/j)_+).
  - Upper bound: τ(g(x)) ≤ d_τ(x) for x = (b_j − 2/j)_+. By Rørdam's lemma with ‖a − b_j‖ < 1/j,
    d_τ(x) ≤ d_τ((a − 1/j)_+).
  - Lower bound: h_{1/j} = 1 on [2/j, ∞) gives g_j ≥ d_τ((b_j − 3/j)_+) ≥ d_τ((a − 4/j)_+).
- **Step 2.** G_j = max(g_1, ..., g_j) is continuous, increasing, and squeezed between rank functions increasing to
  d(a). Dini on compact QT(A) gives uniform convergence.
- **Step 3.** Compact containment (a − 1/j)_+ ≪ a = sup a_n gives G_j ≤ d(a_n) ≤ d(a) for large n.
- **Model test.** In C([0,1]), δ_{1/(2n)} shows that continuity is load-bearing.

## Notes

- **Unreviewed imports** used by §7.2 and §7.3: `amenable-kernel-bc-transfer-and-ktop-half-exactness` (Chabert--Echterhoff
  Corollary 3.5 and half-exactness) and `lueck-surjective-assembly-traces-lie-in-lambda-g`. They are imports of
  published theorems and were not re-read.
- **Owner messages.** No finding needs a correction or an owner message.
