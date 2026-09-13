# SL_3(Z) coherence, part 2: what each incoherence construction needs inside SL_3(Z)

Lane z3-04-sl3z-coherent, 2026-09-13. Unreviewed. Part 1:
`research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part1.md` (non-dense subgroups
are coherent; tree hierarchy class 𝓗; shape of a witness).

## 5. Products: no commuting non-elementary pairs

**Theorem 5.1.** SL_3(C) contains no two commuting subgroups A, B that are both not
virtually solvable. In particular F_2 × F_2 does not embed in SL_3(C), and no product of
two non-virtually-solvable groups embeds in SL_3(Z).

*Proof.* The Zariski closures Ā and B̄ commute. Since A is not virtually solvable, Ā° is
not solvable, and a Levi subgroup S of Ā° has type A_1 (part 1, proof of Theorem 3.1, or
S = SL_3). B̄ lies in the centralizer of S.
- If S = SL_3, the centralizer is μ_3, so B is finite.
- If S acts irreducibly on C³ (S = SO(q)), its centralizer consists of scalars by Schur's
  lemma, so B is finite.
- If C³ = 2 ⊕ 1 as an S-module, the centralizer preserves the isotypic components and
  acts by scalars on each, so it is the torus {diag(t, t, s)} in the adapted basis. Then B
  is abelian.
In each case B is virtually solvable, a contradiction. ∎

*Graph node.* The owner lane z3-04-sl3z-incoherent records the stronger integral statement
(`sl3z-products-of-infinite-subgroups-are-polycyclic`: centralizers of infinite-order
elements of SL_3(Z) are solvable, so a product of two infinite subgroups is polycyclic).
This section is an independent check of the part used here, not a separate node.

*Obstruction recorded.* The classical incoherence witnesses in products of free groups
cannot occur in SL_3(Z). These are the fibre products and kernels of maps F_2 × F_2 → Z
that are finitely generated but not finitely presented (Grunewald; Baumslag–Roseblade).
The same witnesses do show that SL_n(Z) is incoherent for n ≥ 4, since SL_2(Z) × SL_2(Z)
embeds block-diagonally in SL_4(Z).

## 6. Normal fibres of infinite index force density

**Theorem 6.1.** Let K ≤ SL_3(Z) be finitely generated, and let N ⊲ K be an infinite,
finitely generated normal subgroup of infinite index that is not virtually solvable.
Then K and N are both Zariski-dense in SL_3, and [SL_3(Z) : K] = ∞.

*Proof.* Two facts are used.
- (Φ) A finitely generated group Γ that is virtually free non-elementary, or virtually a
  closed surface group of genus ≥ 2, has no infinite finitely generated normal subgroup
  of infinite index. Reason: b_1^(2)(Γ) > 0, while b_1^(2) vanishes for a finitely
  generated group with such a normal subgroup (Gaboriau, *Publ. Math. IHÉS* 95, 2002).
  Classically: in free groups (Schreier) and in closed surface groups (Griffiths), a
  nontrivial finitely generated normal subgroup has finite index; pass to a finite-index
  torsion-free subgroup Γ_0 and intersect.
- The classification of non-dense subgroups (part 1, Theorem 3.1).

Suppose K is not Zariski-dense.
- (V) K is virtually polycyclic, so N is virtually solvable. Contradiction.
- (F) K is a finitely generated discrete subgroup of SO(2,1), hence a finitely generated
  Fuchsian group up to index 2. It is not elementary, since N is not virtually solvable.
  Fg non-elementary Fuchsian groups are virtually free or virtually closed surface groups
  (Selberg's lemma and geometric finiteness), so (Φ) gives a contradiction.
- (P) Conjugate K into P_1 (or P_2) and let π: P_1 → GL_2(Z) with kernel U ≅ Z². Put
  K̄ = π(K), N̄ = π(N), V = K ∩ U and W = N ∩ U.
  - N̄ ≅ N/W is not virtually solvable (W is abelian), so N̄ is infinite and K̄ is a
    non-elementary fg virtually free group. By (Φ), [K̄ : N̄] < ∞.
  - The index satisfies [K : N] = [K̄ : N̄]·[V : W], because K/N contains VN/N ≅ V/W with
    quotient K/VN ≅ K̄/N̄. So [V : W] = ∞, and W_Q ⊊ V_Q in Q² = U ⊗ Q.
  - For n ∈ N and v ∈ V the commutator [n, v] lies in N ∩ U = W. In additive notation,
    π(n)·v − v ∈ W, so N̄ acts trivially on V_Q/W_Q. W is normal in K, so N̄ preserves
    W_Q. The action of GL_2(Z) on U is faithful (B ↦ det(B)^{-1}·B^{-T} has trivial
    kernel).
  - If W_Q = 0, then N̄ fixes the nonzero subspace V_Q pointwise, so N̄ lies in the
    stabilizer of a nonzero vector, which is solvable. Contradiction.
  - If dim W_Q = 1, then V_Q = Q². N̄ preserves the line W_Q and acts trivially on Q²/W_Q,
    so N̄ is upper triangular, hence solvable. Contradiction.

So K is Zariski-dense, with closure SL_3.
- The closure of N is normalized by SL_3, so its identity component is a connected normal
  subgroup of SL_3: either trivial or SL_3. It is not trivial because N is not virtually
  solvable. So N is Zariski-dense.
- If K had finite index in SL_3(Z), it would be a lattice in SL_3(R). Margulis's normal
  subgroup theorem would then force N to be finite or of finite index. Contradiction. ∎

*Obstruction recorded.* Free-by-free groups F_k ⋊ F_m with k, m ≥ 2, and surface-by-free
groups, are incoherent (Kropholler–Walsh; reference to be checked). More generally,
kernels of fibrations over free groups give incoherence. Inside SL_3(Z), any such witness
must be a Zariski-dense thin subgroup whose finitely generated normal fibre is itself
Zariski-dense. Surface-by-Z and free-by-Z thin subgroups would not help, since they are
coherent (Scott; Feighn–Handel).

## 7. L²-fibering in dimension two

The graph already records `virtually-rfrs-cd2-coherence-characterization`. For a finitely
generated virtually RFRS group G with cd_Q(G) ≤ 2, coherence of G is equivalent to
b_2^(2)(G) = 0, and to G being virtually free-by-cyclic. Also recorded:
`higher-l2-betti-obstructs-rfrs-group-algebra-coherence` (a positive higher L²-Betti
number gives a finitely generated subgroup not of type FP_∞(Q)).

**Consequence 7.1 (a concrete incoherence target).** Suppose H ≤ SL_3(Z) is finitely
generated, virtually RFRS, with cd_Q(H) ≤ 2 and Euler characteristic χ(H) > 0 (defined
because such H has a finite-type resolution when it is of type FP_2; in dimension two,
b_2^(2)(H) − b_1^(2)(H) = χ(H) for infinite H). Then b_2^(2)(H) ≥ χ(H) > 0, so H is
incoherent, and so is SL_3(Z). By part 1, H is Zariski-dense and thin.

Such H cannot be:
- free or a surface group (χ < 0, and coherent anyway);
- a product of two non-elementary groups (Theorem 5.1);
- in 𝓗 (Corollary 4.1).
So a positive answer to Problem 3.4 implies: **every finitely generated virtually RFRS
subgroup of SL_3(Z) of rational cohomological dimension ≤ 2 is virtually free-by-cyclic
and has b_2^(2) = 0.** This consequence is recorded as a claim so the incoherent side can
aim at it.

## 8. Dead leads and live cases

Dead:
- **Abelian-by-coherent.** Z^n ⋊ Q with Q coherent is coherent (Lemma 1.1). This covers
  Z² ⋊ F_2 and the affine subgroups.
- **Products.** Commuting non-elementary pairs do not exist in SL_3 (Theorem 5.1).
- **Trees over virtually solvable edges from non-dense pieces.** Such groups are coherent
  (Corollary 4.1). This covers ping-pong combinations of parabolic pieces, amalgams over
  unipotent subgroups, and HNN extensions over diagonalizable subgroups.
- **Classical coherent classes.** 3-manifold groups (Scott), free-by-cyclic groups
  (Feighn–Handel), one-relator groups (graph node `one-relator-groups-are-coherent`).

Live, for either answer:
- (L1) Zariski-dense thin subgroups with a Zariski-dense finitely generated normal fibre
  of infinite index (Theorem 6.1).
- (L2) Virtually RFRS thin subgroups with cd ≤ 2 and b_2^(2) > 0, e.g. χ > 0 (Consequence
  7.1).
- (L3) Zariski-dense thin subgroups that split over no virtually solvable subgroup and are
  not Fuchsian-like. Here Theorem 1.3 gives nothing and new ideas are needed.

A proof of coherence must handle one-ended Zariski-dense thin subgroups of SL_3(Z). No
general structure theory of these is known here: Anosov subgroups are hyperbolic, and
hyperbolic groups can be incoherent (Rips's construction gives finitely generated, not
finitely presented subgroups), so hyperbolicity alone does not help.
