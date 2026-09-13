# EX novelty and priority log, part 2 (2026-09-12)

Lane `ex-novelty`. This continues the log section of `research/artifacts/ex-open-status-2026-09-12.md`,
which holds the open-status table, the method, and entries up to 22:07.

For each landing in `state/landed.log` I read the new nodes' statements and credit lines and checked
the nearest literature within the stated bound. Tags as before:
- **P**: primary abstract or text fetched;
- **W**: web or listing summary.

"No credit line" means that grep found no credit, novelty or citation sentence in the node.

## Entries 22:09–22:25

- **22:09, ex-weak-soficity, 57fdcf7cf3.** Howie pro-p tuple test at A5. Technical; no novelty claim.
- **22:10, ex-lueck-approximation, 912ea9ef17.** `binary-leavitt-unit-group-is-l2-acyclic` (established,
  unreviewed).
  - Credits: Khanh arXiv:2609.08428, Definition 2.1 and Corollary 4.3 (verified artifact), for
    frame-complex acyclicity; Sauer–Thumann arXiv:1304.6843 for the l²-invisibility of V.
  - Not searched specifically; novelty unverified.
- **22:10, ex-bernoulli-negative, 44fec21fb7.** `bernoulli-factor-algebraic-actions-have-finite-stabilizers`,
  no credit line.
  - It follows in one line from mixing. Factors of Bernoulli shifts are mixing, and the character `x ↦ x(a)`
    is fixed by `Stab_G(a)`. So an infinite stabilizer forces the character to be constant, which means
    `a = 0`.
  - Folklore. A one-line credit ("immediate from mixing") would do. No message.
- **22:12, ex-free-unused-power, c609c3bab4.** A citation import only.
- **22:12 / 22:13, ex-bernoulli-positive, 26c156968e and 781800afec.**
  - The approximation threshold credits Seward (Corollary 6.1, Lemma 6.2).
  - The collapse set `D(G)` being a subgroup is elementary from Seward's equal-entropy theorem and
    products of Bernoulli shifts.
  - No credit risk.
- **22:13, ex-free-bridges, b850838e74.** `leavitt-unit-groups-have-fixed-price-one` credits Gaboriau
  (Critères VI.24(3)) and Furman's variant. It observes that commutativity of the ring is never used.
  Credit is adequate.
- **22:14, ex-hyperbolic-vtf, 085e9f3d35.** Chern–Quillen detection of prime-order torsion. Technical;
  not reviewed.
- **22:15, ex-complexity-amenable, 2ca0926b8c.** `twisted-brin-thompson-wp-equals-actor-orbit-problem`,
  no credit line.
  - The abstracts of Belk–Zaremsky arXiv:2001.04579 (Geom. Topol. 26 (2022)) and Zaremsky arXiv:2201.00711
    (P) contain no word-problem results.
  - The nearest prior art for item (b), the coNP bound relative to the orbit problem: Birget
    arXiv:1902.03852 (word problem of 2V coNP-complete) and arXiv:math/0310335.
  - The lane was messaged at 22:45.
  - The root `fp-simple-groups-with-arbitrarily-complex-word-problem` correctly stays OPEN: the new route
    requires the OPEN `type-a-actors-with-arbitrarily-hard-word-problem`, which runs through
    `permutational-boone-higman-conjecture`.
- **22:15, ex-left-orderable-nonsofic, 8baa5808d4.** `infinite-left-orderable-kazhdan-group` is OPEN.
  - It is Navas's Question 3, verbatim (arXiv:1712.06462v2, p. 3). The node quotes Vergara
    arXiv:2407.03579v3 for the open status. Correct.
  - Consequence: a left-orderable nonsofic group from the rigid-pair mechanism would also answer Navas's
    Question 3 (route `infinite-left-orderable-kazhdan-group-from-rigid-pair`). That raises the bar for
    the lane.
- **22:16, ex-toms-winter, eca20c7e2a.** Bauer-divisible unit rank density. Technical. Context: arXiv:2604.24682
  proves Toms–Winter under stable rank one plus tracial locally finite nuclear dimension.
- **22:16, ex-blackadar-kirchberg, 1283a1a764.** `stw07-separating-qd-quotients-force-quasidiagonality`,
  no credit line. It is standard: A embeds in ∏ A/J_i, products and C*-subalgebras of quasidiagonal
  algebras are quasidiagonal, and separability lets one pass to countably many ideals. Low risk.
- **22:17, ex-atiyah-torsion-free, 004ae54ac2.** Double ascending HNN kernel tree, plus a
  locally-indicable extension citation. Technical.
- **22:18, ex-baum-connes, acc5d83c1b; 22:22, dd95bf500c.** Amenable-kernel transfer citation, module
  K-inexactness route and fences. The root stays OPEN.
- **22:18, ex-kazhdan-simple-hyperlinear, f375478c72.** LEF-consequence artifacts. Context: Alekseev–Thom
  arXiv:2608.05362 (P). A Kazhdan group whose sofic embedding has an ergodic centralizer is LEF, and
  residually finite if finitely presented.
- **22:19, ex-q34-kt-double, 2dc316605c.** Commutant normalization. Technical.
- **22:20, ex-ugc, c9d69e02a3.** `elementary-abelian-galois-games-round-with-linear-loss`. The lane's
  artifact records a bounded novelty check (Section 7), not re-checked here.
- **22:20, ex-rank-problem-villadsen, ddf8f06131.** `toms-schubert-algebra-misses-a-rank` is OPEN, so
  no refutation of STW XXIII is claimed. It builds on Toms arXiv:2606.12188v2 (a simple AH algebra
  without uniform Γ).
- **22:20, ex-q34-leavitt-hs, 5c1973dd19.** `leavitt-unit-group-has-no-integer-heisenberg-subgroup` is
  OPEN. The non-embedding of the Kun–Thom wreath into L_2^x is conditional on it.
- **22:21, ex-determinant-monster, 4d6e754a07.** `serre-class-atoms-obey-degree-bound` (established), no
  credit line.
  - A Serre-class measure has mass at most 1/deg at an algebraic point and none at a transcendental one.
  - Nearest prior art to check: Thom, "Sofic groups and Diophantine approximation" (CPAM 61, 2008), on
    log-regularity of spectral measures over sofic groups. One search found nothing closer. Low risk.
- **22:21, ex-hyperbolic-vtf, b76f42e6af.** `every-hyperbolic-group-is-good` is OPEN with Attempts.
  `good-cocompact-proper-groups-are-virtually-torsion-free` is established and unreviewed. Nearest prior art
  surfaced: Boggi, "Finite subgroups of the profinite completion of good groups", Bull. LMS (2025).
  Outcome in the note below.
- **22:23, ex-quantum-pcp, 987c340b4c.** Citation imports (commuting Hamiltonians on small-set
  expanders in NP; NLTS from good qLDPC codes). Not source-checked here.
- **22:23, ex-q34-collapse, f8d1346e0f.** `block-monomial-hs-models-sofic-mod-amenable-soft-kernel`
  (established). `hyperlinear-groups-admit-masa-normalizing-microstates` is OPEN, correctly marked as
  equivalent to a positive Q3.4 answer. No over-claim.
- **22:24, ex-kadison-kaplansky, 510cea6b08.** `selfless-projection-traces-equal-k0-trace-image` explicitly
  disclaims novelty ("standard consequence of strict comparison").
- **22:25, ex-nonsofic-action-relative, 3d96d53492.** Mixing-root edits; the root stays OPEN.
- **22:25, ex-k1-properly-infinite, 412dd76324.** `dd-toeplitz-algebra-is-properly-infinite` answers
  Blanchard's Question 5.4 (arXiv:1507.02535v1, 1312.7722v7) positively.
  - It credits Blanchard and Blanchard–Rohde–Rørdam Theorem 5.5.
  - One search found only Blanchard's own papers, no earlier answer.
  - It does not decide LXI. Credit adequate; novelty bounded.

## Entries 22:26–22:42

- **ex-unitary-class-three, 4edaed478a, 003ca49dfc, a7e18e225c.** CLAIMED SOLUTION of its root
  (row 21 of the table), unreviewed.
  - Route: `class-three-via-spin-bordism-trapping-tower` requires
    `simple-ah-algebra-with-class-three-component-group`, which has a proof route: a simple unital
    nuclear AH algebra with three unitaries whose triple commutator is an order-two class outside U0.
  - It credits Toms's trapping (arXiv:2609.09535). That paper's text has no nilpotency or commutator
    statement (P), so there is no priority threat.
  - Recommend an ex-verify-analysis pass before anyone calls it solved.
- **ex-lueck-approximation, fdf9d8f7f3 and ffe5863325.**
  - `decidable-groups-have-right-computable-l2-betti-numbers` is Löh–Uschold arXiv:2202.03159,
    Theorems 1.1–1.2 (HTML P). The node credited only a Grabowski remark. Lane messaged at 23:10.
  - `binary-leavitt-unit-group-has-irrational-l2-betti-numbers` is immediate from the lamplighter cube
    inside V and Grabowski's values for (Z/2 wr Z)^3 (arXiv:1004.2030, P). Credit is wired through
    `lamplighter-groups-have-irrational-l2-betti-numbers`.
  - `binary-leavitt-unit-group-has-fixed-price-one`, `elementary-groups-over-infinite-rings-have-fixed-price-one`
    and `gaboriau-commensurated-chain-fixed-price-criterion` duplicate ex-free-bridges'
    `leavitt-unit-groups-have-fixed-price-one` (b850838e74, 22:13). Priority inside the swarm is ex-free-bridges.
    Lane messaged at 23:15.
  - The Kun–Thom wreath and double fixed-price-one claims and the wreath L²-acyclicity look new within
    the graph.
- **ex-nh-mipstar, c9e84ceb8c and 89de1ecb58.**
  - `lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap` credits only Paddock–Slofstra.
    Atserias–Mančinska–Roberson–Šámal–Severini–Varvitsiotis arXiv:1611.09837 (abstract P) reduce binary
    linear constraint games to isomorphism games through a CFI-type construction, and separate qc from
    tensor-product isomorphism. Lane messaged at 23:10.
  - The planar-count corollary credits Mančinska–Roberson arXiv:1910.06958.
- **ex-determinant-monster.**
  - ff83a99a96, `integer-root-limits-are-galois-balanced-serre-measures` (unreviewed), builds on
    Smith's inequalities.
    - The commit subject says it answers Thom's 2007 question: "It would be very interesting to
      characterize the continuous parts of the spectral distribution function intrinsically"
      (math/0701294v3, after Theorem 5.4).
    - The lane's own artifact (Section 5) records that realization for Thom's class, which needs normal
      integer approximants, is unsettled. So it is a partial answer. The node title is accurate.
  - 11382c9376, `integral-operator-norm-below-two-is-quantized` (unreviewed), credits Thom and Lück
    arXiv:1901.00827. What is new is removing the approximation, over every group.
  - e3d3bfa673 records an absence claim with a bounded check.
- **ex-kazhdan-simple-hyperlinear, 56bdeb8d3e and a73f7f76cf.**
  - `operator-mf-group-not-weakly-quasidiagonal-exists`: the witness is EL_3(LC(X,F_q) ⋊ Z) for a minimal
    subshift X.
  - The node says an introductory arrow in Dadarlat arXiv:2007.12655v2 is false for groups. The reading
    of Dadarlat's definitions deserves an ex-verify check before that is stated anywhere public.
  - The Turing-degree realization has low credit risk.
- **ex-kadison-kaplansky, dab3891556 and d9acb657b1.** The free-product projection traces cite K_0
  generation by factor images. Scalar commutators forcing nθ ∈ τK_0 credit de la Harpe–Skandalis.
  Adequate.
- **ex-complexity-sofic, 076f1bec8c.** `residual-finiteness-of-finite-presentations-is-pi2-complete` is
  OPEN and cites Kharlampovich–Myasnikov–Sapir arXiv:1204.6506. One search found only Bridson–Wilton
  (triviality of profinite completions is undecidable) and Sapir's Minsky survey arXiv:1504.07736
  (abstract P). No completeness statement found.
- **ex-nonsofic-action-entropy, 3ecde705af; ex-nonsofic-action-relative, 23b018d16c.** Păunescu's class is
  invariant under measure equivalence; the node credits Alpeev arXiv:1706.01864 after four queries. One
  lattice outside the class gives every Howe–Moore lattice a mixing nonsofic action. Adequate.
- **ex-bernoulli-negative, d2a8ad5ce4 and 2c4a31bcd4.** Co-induced finite-subgroup shifts add H(Y)/|F|
  (bounded novelty note present); induced absorption never collapses entropy. The root stays OPEN.
- **ex-rank-problem-lix, 16cd5f1cc8 and 464531f0c9; ex-rank-problem-villadsen, a57ae731c8 and 5eb6bccb86.**
  - Toms's no-Γ algebra fails Thiel's (O6+) and has no small joins.
  - Rank density plus small joins gives all ranks.
  - The root stays OPEN.
- **ex-rr0-dichotomy, c94145c599.** The dichotomy fails iff a finite simple real rank zero algebra has an
  infinite M_2, and such an algebra is a non-separative exchange ring. The literature frame is the
  separativity problem of Ara–Goodearl–O'Meara–Pardo (1998).
- **ex-blackadar-kirchberg, a9803215dd and d502e4d3be.** Quasidiagonality of extensions by ideals with no
  compact open primitive subset, citing Brown–Dadarlat. Not checked further.
- **Low risk, no check beyond the subject line:**
  - 66938b864e ex-toms-winter: attribution fix;
  - b2033f6b04, 7e05aa7711, 03294b62a7 ex-ugc: 2-to-2 and SSEH imports, Galois rounding;
  - afeb2d0090 ex-lueck-approximation: tracial rank functions;
  - 043a53d47b ex-k1-properly-infinite: LXI length reformulation;
  - 4656ff0c3d ex-weak-soficity;
  - 2a70eebc6c ex-fp-simple-sofic: Penrose full group, soficity folklore;
  - df0475921f ex-thompson-v-soficity: open target posed;
  - a5564e38b5 ex-baum-connes: trace defect ⇒ surjectivity failure;
  - aa6b4d74d4 ex-toms-winter;
  - 14a3ca5645 ex-free-objects: presentation, not compared with Khanh or OpenAI;
  - a564fb2cfc ex-rokhlin-lower;
  - eb7e149f1a ex-left-orderable-nonsofic;
  - d48bdd179a ex-q34-collapse;
  - dc2f7ed4d4 ex-free-unused-power;
  - 54faf1cd64 ex-hyperbolic-vtf;
  - a1e1bf7e3c ex-bernoulli-positive.

## Boggi note

Boggi–Zalesskii, arXiv:2406.08639 (Bull. LMS 2025), abstract (P): "Let G be a residually finite, good
group of finite virtual cohomological dimension. We prove that the natural monomorphism G ↪ Ĝ induces a
bijective correspondence between conjugacy classes of finite p-subgroups of G and those of its profinite
completion Ĝ."

Finite virtual cohomological dimension presupposes a torsion-free finite-index subgroup. So their
theorem assumes virtual torsion-freeness, and it does not contain the lane's implication "good +
cocompact proper action with fixed points ⇒ virtually torsion-free".

It is adjacent prior art for how good groups control finite subgroups of Ĝ, and it deserves a mention on
`good-cocompact-proper-groups-are-virtually-torsion-free`. Novelty of (G) is otherwise unverified: two web
searches, the Boggi–Zalesskii abstract, and nothing more.
