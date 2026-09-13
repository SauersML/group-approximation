# EX review, analysis lanes, part 6 (2026-09-13)

Lane `ex-verify-analysis`. Verdict legend as in `ex-review-analysis-2026-09-12.md` §0. Main tip at
review time: `b38ee6bf9`.

## 1.12 ex-nh-mipstar: quantum symmetry rung toward a non-hyperlinear group

None of these claims decides `non-hyperlinear-group`. They connect it to graph isomorphism games:
- `qc-isomorphic-not-qa-isomorphic-graph-pair-exists` is OPEN;
- `non-ce-quantum-automorphism-group-of-finite-graph-exists` is OPEN;
- the NH root stays OPEN.

### `qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group` (9eb255abc3, 89de1ecb58, ed270bac5f): PASS

Re-derived. Trust surfaces: BCEHPSW arXiv:1812.11474v2, Theorem 2.1(3), Remark 4.3, Theorems 4.7 and
4.9, Example 3.14, Theorem 3.15(1), all quoted.
- **Schur closure (S1).** MV = VN iff M_{xx'} v_{xa} v_{x'a'} = N_{aa'} v_{xa} v_{x'a'}. Both directions
  follow from row and column orthogonality. So W(V) is closed under sums, products and entrywise
  products.
- **Reductions.** Sizes match. Complements are intertwined, so we may assume connectivity.
  Same-component matrices built by entrywise polynomials are intertwined, which transfers
  connectivity.
- **Central projection.** R_Z = J_X ⊕ J_Y intertwines U with itself. The four block identities (S2)
  make P = Σ_{d∈Y} u_{xd} independent of x. Every generator lies below P or below 1 − P, so P is
  central.
- **P ≠ 0.** U' = [[0, V], [V^t, 0]] is a magic unitary intertwining A_Z, and the universal map sends
  P to 1.
- **h(P) = 1/2.** Right invariance gives
  h(P)1 = Σ_e u_{xe} h(Σ_{d∈Y} u_{ed}) = (1−P)h(P) + P·h(1−P). Since P ≠ 0, h(P) = h(1−P).
- **Corner.** The (X,Y) block is a magic unitary in P·O(G) intertwining (A_X, A_Y), so ψ exists and
  2h∘ψ is tracial, using Kac type (B4).
- **Non-embeddability.** A trace-preserving L^∞(G) ↪ R^U restricts to the corner of trace 1/2, and
  q R^U q ≅ R^U. That would give A(Iso(X,Y)) → R^U, against (QG1) via (B1).
- **Credit.** The Lupini--Mančinska--Roberson corner construction (their Theorem 4.4) is credited.
  The additions, the invariance computation and the embedding step, are correctly identified.
- **Mančinska--Roberson corollary.** It is flagged as known from abstracts only. That is honest.

### `lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap` (c9e84ceb8c, ed270bac5f): PASS as a composition of published results

- **Tracial state ⟺ perfect qc strategy.** GNS gives a faithful trace, and a homomorphism into a
  faithfully traced algebra pulls the trace back.
- **R^U model ⟺ perfect qa strategy.** BCEHPSW Theorem 2.1(3),(4).
- **Transfer.** BCEHPSW Theorem 5.6 and Proposition 5.3 at t = qc and t = qa, together with
  Paddock--Slofstra (P1) and (P2).
- The node correctly credits AMRSSV Theorem 6.5 for the qc half. The only new part is the composition
  with Paddock--Slofstra Proposition 5.8, and the novelty search is marked as bounded to four papers.

### `closure-safe-support-is-exactly-the-colored-iso-rung` (1828655f67, 89de1ecb58): PASS

Re-derived.
- **(P0).** τ(pq) = ||pq||²_{2,τ}.
- **(P1).** Row PVMs with injectivity give column sums q_j with Σ_j τ(q_j) = N and τ(q_j) ≤ 1, so
  q_j = 1 under a faithful trace.
- **(CS1 ⇒ CS2).** Colour pairs by support components. Diagonal pairs are reserved, by row
  orthogonality and injectivity. The GNS magic unitary satisfies the colour relations by (P0), so
  X ≅_qc Y. Closure safety makes A(H) → A(Iso(X,Y)) well defined, so there is no qa model.
- **(CS2 ⇒ CS1).** λ = [c_X = c_Y] gives a bisynchronous game. A(Iso(X,Y)) is a quotient of A(H), so the
  trace pulls back. Its components are monochromatic, and any R^U model of A(H) factors through
  A(Iso(X,Y)) by (P1).
- **Colored union.** The coproduct and antipode respect the transpose-closed colour relations.
  R = Σ_{k ≠ cross} E_k = J_X ⊕ J_Y, and Steps 5--7 above apply verbatim.
- **Scope.** The plain-graph reduction is explicitly not claimed.

### `colored-cfi-rung-is-the-solution-group-case` (8f81b394fc): PASS as an import

- Roberson--Schmidt arXiv:2111.12362v1: Definitions 3.1, 3.2, 6.3 and 6.5, and Theorems 3.8 and 6.7,
  quoted with page numbers.
- **Consequences.** A *-isomorphism preserves tracial states and R^U models, which matches the
  qc/qa-satisfiability reading of A(M, b + b').
- The decolouring theorems are correctly marked as not used.

## 1.13 ex-ugc: symmetric Galois unique games

None of these claims bears on the truth of `unique-games-conjecture`, and each node says so. The root
and `unique-games-gap-admits-polynomial-time-algorithm` are OPEN.

### `galois-unique-game-value-is-transversal-expansion` (c9d69e02a3, 1373122d44): PASS

Re-derived.
- **Value.** f ↦ T_f = {τ(v)f(v)} is a bijection from labelings to left transversals of K. The constraint
  holds iff s t_v is the point of T_f in the coset sv. So val = max_T Pr[st ∈ T].
- **Perfect completeness.** ΛT = T forces Λ ∩ tKt^{-1} = {e}, since t and λt both lie in T ∩ tK.
  Conversely, under freeness one coset Λg_O per orbit meets each coset of the orbit exactly once.
- **SDP.** (≥) from φ = ⟨π(g)ξ, ξ⟩, where φ = 0 on K ∖ {e} gives orthogonality within vertices.
  (≤) by averaging left translates, using conjugation invariance of μ.
- **Folded tests.** They are Galois games: folding makes {f = 0} a transversal of ⟨1⟩.

### `elementary-abelian-galois-games-round-with-linear-loss` (c9d69e02a3): PASS, one wording note

Re-derived.
- **Uniform push-forward.** φ = Σ w_χ χ with φ|_K = δ_0, so by Fourier inversion on K the push-forward
  of w to K̂ is uniform.
- **Spanning.** By Markov, w{λ < 1 − η} ≤ ε/η. With η = 2pε/(p−1), good restrictions have density
  ≥ (p+1)/(2p) > 1/p, so they are not in a proper subgroup and contain a basis.
- **Complement.** Y = (log_ζ χ_i) restricts to an isomorphism on K, so T = ker Y is a complement.
- **Cost.** 1 − val ≤ Pr[Y(s) ≠ 0] ≤ Σ_i (1 − λ_{χ_i})/(1 − cos(2π/p)) ≤ C_p ε log_p k.
- **Cyclic example.** φ = (1 + cos(πx/n))/2 = 1/2 + (χ_1 + χ_{−1})/4 is positive definite, vanishes at n,
  and has objective cos²(π/2n). With val = 1 − 1/n, the loss is of order √ε. Correct.
- **Trust surface.** The Khot--Vishnoi tightness estimate through Bonami--Beckner was not re-derived.
- **Wording note.** The general formula gives C_2 = 2 at p = 2. The stated C_2 = 3/2 comes from the
  separate choice η = 3ε, whose density margin 2/3 > 1/2 suffices, as the proof route notes. The claim
  displays both side by side as if C_2 were the formula at p = 2.

### `galois-games-round-through-free-subgroups` (03294b62a7, ef903527e2): PASS

Re-derived.
- **Duality.** Stabilizer formulas.
- **Rounding.** T = {g : g^{-1}H ∈ D} is a transversal, because Y(ga) = a^{-1}Y(g) and K acts freely on
  G/H. For s ∈ H, Y(st) = Y(t), so 1 − val ≤ μ(G ∖ H).
- **Kernels.**
  - w(B) ≤ 1/3 for B = {λ < 1 − 3ε}, so Re φ ≥ 1/3 on K ∩ (the good kernels).
  - φ vanishes on K ∖ {e}, so that intersection is trivial.
  - A halving chain needs at most log_2 k representations.
  - The common kernel is normal, so it meets every conjugate of K trivially.
- **Cost.** E|ρ(s) − I|²_HS = 2d(1 − λ), while off ker ρ, |ρ(g) − I|²_HS ≥ 2(1 − cos(2π/m)).
- **Subgroup certificates.** 1_L is admissible when L ∩ K = {e}.

### `unique-games-hard-at-completeness-one-half` (b2033f6b04): PASS

- Splitting each 2-to-2 linear constraint into its two unique branches with weight w_c/2 gives
  OPT(U)/2 ≤ OPT(U') ≤ OPT(U). So (1 − ε, ε) hardness becomes ((1 − ε)/2, ε) hardness.
- `two-to-two-games-theorem-citation` quotes Khot--Minzer--Safra ECCC TR18-006 Theorem 1.4 verbatim,
  and the other works it relies on are credited.
