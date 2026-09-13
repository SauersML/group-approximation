# UN novelty checks, part 1: simplicity, paradox thresholds, traces, calibration rings

Lane `un-novelty`, 2026-09-13. Bounded novelty and priority checks for UN claims that would be framed as new.
ex-novelty handles the three headlines already queued with it (`boundary-action-elementary-simple-kazhdan-not-mf`,
`toeplitz-free-group-elementary-groups-are-lef-kazhdan`, `free-group-crossed-product-matricial-iff-invariant-measure`).

## 0. Method and bound

- **Starting point.** `research/artifacts/un-prior-art-2026-09-13-part1.md` and part 2 (538afe1ed4): 15 papers read at
  source and 12 web queries. Nothing below repeats that search.
- **This pass.** Six web queries (September 2026), arXiv abstract pages for 1912.11386 and 1705.06555, and pp. 1–3 of the
  arXiv PDF of 1705.06555, read locally.
- **Not reached.** MathSciNet and zbMATH; the Springer abstract of "On the normal structure of the general linear group
  over a ring" (J. Math. Sci., doi 10.1007/BF02169976), which redirects to a login; Vaserstein (regular rings); Golubchik
  (arbitrary rings); Beuter–Gonçalves' full text.
- **Verdicts.**
  - NEW (bounded): no source found within this bound.
  - FOLKLORE: every step is standard and the statement is likely known, but no verbatim source was located.
  - PRIOR: a located source states it.

## 1. Simplicity of EL_n over simple Steinberg algebras

Nodes: `local-annihilation-makes-projective-el-simple` (Lean on main) and `steinberg-elementary-groups-are-simple-mod-centre`
(6c58d38ebb). un-verify passed both (171f0f7525).

**Classical cases.** Over a division ring, E_n/Z is simple. Over commutative rings the sandwich classification is due to
Wilson and Golubchik (search snippet; not read).

**Exchange rings: PRIOR for that class.** arXiv:1912.11386, abstract verbatim: "Let $R$ be an exchange ring. We prove that
the relative elementary subgroups $E\_n(R,I)$ are normal in the general linear group $GL\_n(R)$ if $n\geq 1$ and that the
standard commutator formula $E\_n(R,I)=[E\_n(R),E\_n(R,I)]=[E\_n(R),C\_n(R,I)]$ holds if $n\geq 3$." The listing also says
that the paper "classifies the subgroups of GL_n(R) that are normalised by the elementary subgroup E_n(R) in the case n≥3".
- For a simple exchange ring the only levels are 0 and R. So a normal subgroup of E_n(R) is central or everything, which is
  the node's conclusion.
- The non-MF tex already proves simplicity for L_{F_2}(1,2)^× through this sandwich theorem (credited there to Preusser).
  Purely infinite simple rings are exchange rings (Ara–Goodearl–Pardo).
- So the Leavitt instance is PRIOR.

**Beyond exchange rings: NEW (bounded).**
- The local-annihilation criterion ("simple ring with local annihilation ⟹ every normal subgroup of EL_n, n ≥ 3, is central
  or everything") and its consequence for every minimal effective ample 𝒢 were not found in the sources checked.
- It covers rings that are not known to be exchange rings, e.g. LC(X,F_q)⋊Z. The Pestov artifact proves that case by hand.
- **Risk.** A general "linear dependence" criterion for arbitrary associative rings may exist in the Golubchik-school
  literature (the doi above; its snippet says normality and standard distribution "follow from certain conditions of
  linear dependence in R"). It was not read. Before any public "new" framing, read that paper, Vaserstein, and
  Hazrat–Vavilov's surveys (arXiv:1910.14444, 2004.12870 surfaced in the search).

## 2. Paradoxical-level thresholds for MF quotients

Nodes:
- `paradoxical-ring-el-n-full-mf-radical-from-twice-level` and `stably-infinite-ring-elementary-groups-have-no-mf-quotient`
  (the architect is reconciling the two);
- `non-ibn-ring-el-n-full-mf-radical-above-module-rank`.

**Verdict: NEW (bounded) as statements; routine corollaries of the manuscript.**
- **No outside source.** No source on MF quotients of elementary groups appeared outside `non_mf_groups_exist.tex`, either
  in un-prior-art's search or in this pass.
- **Mechanism is classical.**
  - The threshold proofs apply tex Thm [full complementary idempotents] (l.918) to M_n(R), then use the block identity
    E_2(M_n(R)) = E_{2n}(R).
  - The non-IBN proof conjugates through R^m ≅ R^{m+d}.
- **Credit.** The manuscript, first; the block identities are standard K-theory folklore.

## 3. Algebraic Tarski for simple rings

Node: `simple-ring-stably-finite-iff-unit-not-paradoxical` (un-verify PASS).

**Verdict: FOLKLORE.**
- **(b)⟺(c)** is Tarski's theorem for preordered monoids, already imported through KMP arXiv:2502.17190v3 Cor 2.16. The
  classical form for states on partially ordered K_0 with order unit is Goodearl–Handelman (search surfaced "Rank functions
  and state spaces of K_0" and "Simple regular rings with a unique rank function", J. Algebra 1976).
- **(a)⟺(b)** is elementary for simple rings: nonzero idempotent classes are order units.
- **No verbatim source.** No exact statement for arbitrary simple rings was located.
- **Recommendation.** Keep the node, credit Tarski, Goodearl–Handelman and KMP, and don't frame it as new.

## 4. Traces on elementary groups

### 4.1 `elementary-group-trace-amenable-iff-ring-residually-finite`
- **Kazhdan collapse, PRIOR.** For a (T) group, the factorization property (an amenable canonical trace) forces residual
  finiteness: Kirchberg, "Discrete groups with Kazhdan's property T and factorization property are residually finite", Math.
  Ann. 299 (1994). Ozawa's survey Thms 6.1 and 7.4 are already imported by un-traces.
- **Ring step (EL_n(R) RF ⟺ R RF, for f.g. R and n ≥ 3): FOLKLORE-level.**
  - A finite-index normal subgroup meets a root subgroup e_12(R) in e_12(J) with J of finite index.
  - Commutator relations turn J into a two-sided ideal of finite index whose relative elementary subgroup lies in the kernel.
  - No source was located.
- **Corollary C** ("QD trace ⟺ matricial rank function" is false) is packaging of the above, not a new theorem.

### 4.2 Corona traces are MF traces: the concept is PRIOR
Nodes: `lef-group-canonical-trace-is-a-corona-trace` and `corona-traces-separate-paradox-from-measure-for-el-n`.

**Source.** C. Schafhauser, "MF traces and the Cuntz semigroup", arXiv:1705.06555v1 (18 May 2017), read from the PDF.
- Abstract: "A trace $\tau$ on a separable C$^*$-algebra $A$ is called *matricial field* (MF) if there is a trace-preserving
  morphism $A\to\mathcal Q_\omega$, where $\mathcal Q_\omega$ denotes the norm ultrapower of the universal UHF-algebra
  $\mathcal Q$."
- p. 1: "A tracial state (hereafter referred to as a trace) on a C$^*$-algebra $A$ is called matricial field if one can find
  linear, *-preserving maps $\varphi_n : A \to \mathbb M_{k(n)}$ which approximately preserve the multiplication and the trace
  in the same sense as above; note, however, the $\varphi_n$ are not required to be approximately isometric."
- p. 2: "if every trace is MF, then Connes's Embedding Problem [...] has a positive solution. [...] the MF-trace problem is a
  uniform version of Connes's Embedding Problem."
- p. 3 credits the terminology and results on MF dynamics to [25] (Rainone–Schafhauser).

**Consequences.**
- **Equivalence.** For separable C*_max(G), a "corona trace" τ = tr_ω∘Φ, with Φ a unital *-homomorphism into
  ∏M_{d_k}/⊕M_{d_k}, is exactly an MF trace. Reindex the approximate maps; M_d ⊂ Q is trace-preserving.
- **Statement (a),** a canonical MF trace ⟹ G operator MF: the argument of tex Thm l.1349, as the node already credits.
- **Statement (b),** LEF ⟹ canonical trace MF: folklore (permutation models whose normalized traces converge to δ_e).
- **Separation theorem.** Its content is tex Thm l.918 (paradox side) and the LEF embedding (measure side), read at trace
  level.
- **Recommendation.** Rename "corona trace" to "MF trace (Schafhauser)" in both nodes and credit 1705.06555 and
  Rainone–Schafhauser. Don't frame the separation as new.

## 5. Calibration rings

### 5.1 `weyl-algebra-over-q-is-lef-ring-not-matricial-over-q`: FOLKLORE
- **Char 0.** A_1 over a field of characteristic 0 has no finite-dimensional representation, since tr[x,y] = 0 ≠ n.
- **Char p.** Over F_p, F_p[x]/(x^p) with y ↦ −d/dx is the standard p-dimensional representation. Reduction mod p of Weyl
  algebras is a standard technique (e.g. Belov-Kanel–Kontsevich, arXiv:math/0512169, surfaced in the search).
- **Not located.** No verbatim source for the ultraproduct embedding A_1(Q) ↪ ∏_ω M_p(F_p). Its role as a calibration row
  (F1) is this lane's packaging.

### 5.2 `group-ring-lef-iff-group-lef-iff-elementary-group-lef`: FOLKLORE
- **Group ⟹ ring.** Permutation matrices on finite local models.
- **Ring ⟹ group.** Units of an ultraproduct of finite matrix rings.
- **EL_n ⟹ group.** Whitehead's lemma puts diag(u, u^{-1}) in E_2.
- **Item 3** needs the existence of finitely generated amenable non-LEF groups (e.g. Abels' groups). It is recalled, not
  quoted.

## 6. Other landings checked this pass

- **`crossed-products-are-transformation-steinberg-algebras` (un-architect 2e5fbbeafb): PRIOR.** Beuter and Gonçalves, "The
  interplay between Steinberg algebras and skew rings", J. Algebra 497 (2018) 337–362. They realize partial skew group rings
  of partial actions on totally disconnected spaces as Steinberg algebras of the transformation groupoid (search listing;
  full text not read). The global-action case is the node. Recommendation: add a citation route and credit.
- **`exactly-matricial-rings-are-lef-rings`: FOLKLORE** (residual finiteness of f.g. commutative rings, Malcev-type).
- **`invariant-measure-gives-rank-function-any-field`** is OPEN, not established. It is consistent with the characteristic-p
  Kaplansky firewall `measure-side-stable-finiteness-contains-char-p-kaplansky`, so no action is needed.

## 7. Summary table

| Node | Verdict | Credit / source |
|---|---|---|
| local-annihilation-makes-projective-el-simple | NEW (bounded); exchange-ring case PRIOR | arXiv:1912.11386; Golubchik-school paper unread (risk) |
| steinberg-elementary-groups-are-simple-mod-centre | NEW (bounded) beyond exchange rings | as above; Leavitt case via the tex |
| paradoxical-ring-el-n-full-mf-radical-from-twice-level (+ dup) | NEW (bounded), routine corollary | tex Thm l.918 |
| non-ibn-ring-el-n-full-mf-radical-above-module-rank | NEW (bounded), routine corollary | tex Thm l.918 |
| simple-ring-stably-finite-iff-unit-not-paradoxical | FOLKLORE | Tarski; Goodearl–Handelman; KMP Cor 2.16 |
| elementary-group-trace-amenable-iff-ring-residually-finite | PRIOR (Kazhdan part) + FOLKLORE (ring step) | Kirchberg 1994; Ozawa survey 7.4 |
| lef-group-canonical-trace-is-a-corona-trace | PRIOR concept (MF traces) | Schafhauser arXiv:1705.06555; tex l.1349 |
| corona-traces-separate-paradox-from-measure-for-el-n | PRIOR concept; folklore corollary | as above; tex l.918 |
| weyl-algebra-over-q-is-lef-ring-not-matricial-over-q | FOLKLORE | reduction mod p |
| group-ring-lef-iff-group-lef-iff-elementary-group-lef | FOLKLORE | elementary |
| crossed-products-are-transformation-steinberg-algebras | PRIOR | Beuter–Gonçalves, J. Algebra 497 (2018) |
| exactly-matricial-rings-are-lef-rings | FOLKLORE | Malcev-type |
