# UN novelty checks, part 2: normal-subgroup literature, architect and converse nodes, wave-3 landings

Lane `un-novelty`, 2026-09-13. Continues part 1 (514b76e752). Verdicts use the same scale: NEW (bounded), FOLKLORE, PRIOR.

## 0. Sources and a correction

**Correction to part 1.** doi 10.1007/BF02169976 is A. V. Stepanov, "On the normal structure of the general linear
group over a ring", J. Math. Sci. 95 (1999) 2146–2155. It is a translation of Zap. Nauchn. Sem. POMI 236 (1997)
166–182. Part 1 and the search listing credited it to Golubchik–Mikhalev, which is wrong.

**Read in full.** Stepanov's paper, from the Springer PDF fetched with curl on MSI and read locally (all 10 pages).

**Read in part.**
- Vavilov–Stepanov, "Linear groups over general rings. I. Generalities", J. Math. Sci. 188 (2013) 490ff (Zap. POMI
  394). Pp. 490–497 only: introduction, scope, notation.
- Vavilov–Stavrova, "Basic reductions in the description of normal subgroups", J. Math. Sci. 151 (2008) 2949ff.
  Pp. 2949–2951 only. It covers Chevalley groups over commutative rings, so it does not apply here.

**Not read.** Vaserstein, "On the normal subgroups of GL_n over a ring", LNM 854 (1981) 456–465; Golubchik, Russian Math.
Surveys 39 (1984); Wilson, Proc. Cambridge Philos. Soc. 71 (1972); Borevich–Vavilov (1985); Gerasimov, Mat. Sb. 62
(1989); the rest of the 674-item survey. MathSciNet and zbMATH were not reached.

## 1. Is `local-annihilation-makes-projective-el-simple` prior?

**Stepanov, verbatim.**
- Abstract: "In particular, it is shown that the normality of E(n,R) in GL(n,R) and the standard distribution of
  subgroups normalized by E(n,R) follow from some conditions of linear dependence in R."
- §1.4: "We always assume that n ≥ 3."
- §1.6(3), standard distribution: "for any subgroup H ≤ GL(n,R) normalized by E(n,R), there exists a unique ideal
  I ≤ R such that E(n,R,I) ≤ H ≤ C(n,R,I)".
- Theorem 4.4: "Assume that for any proper two-sided ideal I in R, the following conditions hold: (a)
  [GL(n,R,I),E(n,R)] = E(n,R,I); (b) for any a ∈ GL(n,R), there exist b ∈ E(n,R/I) and α ∈ (R/I)^n (α ≠ 0) such that
  α_i = (u^b α)_j = 0 for some i,j ∈ {1,…,n}, where u = ρ_I(a) is the image of a in GL(n,R/I). Then the normal
  structure of GL(n,R) is standard."
- The method is Lemmas 4.1 and 4.3: elementary transvections are extracted from matrices with a zero-divisor entry.
- The introduction notes that Gerasimov built rings, in every dimension, where E(n,R) is not normal in GL(n,R). So there
  is no unconditional theorem for arbitrary rings.

**Specialized to simple R.**
- The only proper ideal is 0, so (a) holds trivially.
- (b) becomes a single linear-dependence condition over R.
- Theorem 4.4 then says that every subgroup normalized by E(n,R) either lies in C(n,R,0), which is central, or contains
  E(n,R). That is the node's conclusion.

**Comparison.**
- Local annihilation ("for every finite F ⊆ R, the s admitting t ≠ 0 with ts = 0 and tfs = 0 for all f ∈ F generate R")
  is a different linear-dependence hypothesis. I did not decide whether it implies Stepanov's (b), whether (b) implies it,
  or whether some simple ring separates the two.
- Both proofs use the same classical zero-divisor extraction.

**Verdict.**
- **Method: PRIOR TECHNIQUE.** Credit Stepanov 1997 Thm 4.4 with Lemmas 4.1 and 4.3, and the Wilson–Golubchik–Borevich–
  Vavilov line it cites.
- **The criterion as stated: NEW (bounded).**
- **The Steinberg-algebra theorem: NEW (bounded)** as an application.
- **Before any public "new criterion" framing:** decide whether local annihilation implies (b), and read Vaserstein LNM
  854. If it does imply (b), the theorem is Stepanov's Theorem 4.4 plus the local-annihilation lemma.

## 2. un-architect b9ba6293f1 and the flagship assembly

- **`full-defect-in-m-by-m-kills-mf-quotients-of-el-2m`: NEW (bounded), a routine corollary** of tex Thm l.918. The block
  identity E_n(M_m(R)) = E_(nm)(R) is standard (Bass; Hahn–O'Meara). Credit the manuscript.
- **`mf-elementary-groups-force-stably-finite-simple-rings`: NEW (bounded), a routine corollary.** Items 2–3 are
  contrapositives of item 1 plus the folklore simple-ring Tarski node (part 1 §3).
- **`free-group-cantor-elementary-group-lef-iff-invariant-measure`: OPEN.** As a group-level dichotomy the statement is
  NEW (bounded). Its inputs and credits:
  - measure half: Kerr–Nowak residual finiteness, via Ma's restatement; the Grigorchuk–Medynets/Ma tower template; the
    Pestov artifact §3.3;
  - paradox half: tex Thm l.918 via Rainone–Sims and ABBL;
  - simplicity: local annihilation, with the caveat in §1;
  - (T): EJZ.
  - ex-novelty holds the ring equivalence and the two instances.

## 3. un-converse nodes

- **`weyl-algebra-is-exactly-matricial`: FOLKLORE (reduction mod p), and a DUPLICATE.** It states the same embedding
  A_1(Q) → ∏_ω M_p(F_p) as un-calibration's `weyl-algebra-over-q-is-lef-ring-not-matricial-over-q`. Make one of them
  canonical.
- **`matricial-aperiodic-sft-rings-are-not-quantum-rigid`: NEW (bounded).**
  - "Periodic quantum tiling (Q1)–(Q3)" is the repo's own notion (`sft-crossed-product-fp-iff-quantum-rigid`).
  - **Name clash.** Carette–Moutot, "Aperiodicity in Quantum Wang Tilings", arXiv:2302.04503 (2023), define quantum
    tilings through tensors. Those are different objects, and they don't treat crossed products or finite presentation.
    Add a `distinct_from` note.
  - The key step, specializing a finite window to a finite field so that translations have finite order, is folklore.

## 4. Wave-3 and open-explorer landings (checked up to 14:50:29 CDT)

### 4.1 `boundary-action-simple-kazhdan-group-is-nonsofic` (un-hyperlinear-paradox 82478cbb12): famous-problem level

**Against the literature: NEW.** No nonsofic group is known there. Existence of a non-sofic group is open per Capraro–
Lupini, LNM 2136 (2015), and Pestov, arXiv:0804.3968 (search listings; not re-read).

**Against the repo: a routine corollary.** It combines the established Lean node
`d-ary-leavitt-groups-nonsofic-over-finite-fields` with `boundary-crossed-product-carries-leavitt-family`.
- Any "nonsofic" framing stands or falls with the repo's own nonsofic Leavitt theorem.
- This node adds only simplicity and (T).

**Flags.**
- The verifier should re-derive the corollary.
- Confirm that the Lean node is root-reachable with axiom closure [propext, Classical.choice, Quot.sound].

### 4.2 Other boundary-action nodes
- **`boundary-crossed-product-carries-leavitt-family`: FOLKLORE, and PRIOR at C*-level.** J. Spielberg, "Free-product
  groups, Cuntz–Krieger algebras, and covariant maps", Internat. J. Math. 2 (1991), presents C(∂F_n)⋊F_n as a Cuntz–Krieger
  algebra (search listing; not read). The explicit algebraic isometries are routine. Credit Spielberg.
- **`boundary-action-simple-kazhdan-group-is-hyperlinear`: OPEN, famous, no verdict.**
  - Yes would give a hyperlinear nonsofic group.
  - No would give an explicit non-hyperlinear group.
  - The literature treats both as open.

### 4.3 Remaining landings
- **`continuum-many-simple-kazhdan-lef-groups` (un-open-5): NEW (bounded), a routine corollary** of the Pestov construction
  and marked-language rigidity.
  - Continuum results exist for other classes: f.g. simple groups, and ICC (T) groups (Ioana–Tucker-Drob,
    arXiv:2512.04531, listing only).
  - None was found for sofic simple Kazhdan groups.
- **`irreducible-sft-leavitt-gl-max-mf-quotient-formula` (un-k1-homology): NEW (bounded), a routine corollary.**
  - The K_1 formula is PRIOR: Ara–Brustenga–Cortiñas, "K-theory of Leavitt path algebras", arXiv:0903.0056, Münster
    J. Math. 2009 (listing).
  - The MF half is tex Thm l.1218.
  - The homological reading rests on the Matui import and on Cuntz's K-theory, which is recalled.
- **`lrf-cantor-actions-give-lef-full-and-elementary-groups` (un-full-groups-bridge).**
  - Full-group LEF: PRIOR (Ma arXiv:2209.00580 Thm C; Grigorchuk–Medynets).
  - The ring-level combinatorial-model equivalence: NEW (bounded). It overlaps ex-novelty's Theorem C check.
- **`mf-rigidity-is-monotone-in-matrix-rank` (un-open-2): FOLKLORE.** MF passes to subgroups, and EL_N normally generates
  EL_M.
- **`toeplitz-ring-has-infinite-middle-mf-regime` and `mf-thresholds-rescale-under-matrix-amplification`: NEW (bounded),
  routine corollaries** (tex Prop l.1072; J → F_2[z^{±1}]; the block identity).
- **`effective-free-group-kazhdan-lef-type-is-pi01` (un-open-6).** The upper bound is FOLKLORE (Σ⁰₁ paradox certificates
  by compactness). The completeness node is OPEN.
- **Plans only, no verdict:** un-open-1, -3, -4, -7.
  - un-open-3's characteristic-dependent simplicity input is PRIOR (Clark–Exel–Pardo–Sims–Starling arXiv:1806.04362,
    credited in the plan).
  - un-open-7 uses Vershik–Gordon (finitely presented LEF ⟹ RF), also PRIOR.
- **Import `ara-goodearl-leavitt-mn-monoid-is-one-relator` (un-low-rank-band e9a8f6bf70):** an import, not a novelty item.

### 4.4 Not checked (landed after 14:50:29)
un-architect 79531a14bb, un-tarski 0156bb3f0a, un-reduced-cstar 3a56e40cf8, un-low-rank-band 92fa30e814,
un-boundary-families 0e439a2b56, un-open-5 7e6f1c8002, un-sofic-not-lef 9ef8948121, un-verify-3 2ba472b59d.
