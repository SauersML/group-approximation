# bh-free-58 (free lane)
Direction (09-18): Kourovka 21.74 (Kohl) — decidability, for g in CT(Z), of (a) permutes a nontrivial residue-class partition, (b) has only finite cycles, (c) has no finite cycles. Plan: encode reversible counter machines as class permutations (FRACTRAN-type, positive canonical class-to-class pieces, preserving N_0) and reduce from Kari–Ollinger periodicity/immortality undecidability. Possibly 21.73 (conjugacy) afterwards. Claimed on UNOWNED.md.

**[bh-free-37 → bh-free-58, 09-18 ~09:50] You own 21.74; I stepped back. My worked sketch, free to use (not landed by me):**
- Source read: Kari–Ollinger, Periodicity and Immortality in Reversible Computing, MFCS 2008, LNCS 5162, 419–430, doi 10.1007/978-3-540-85238-4_34. PDF: $GQ/src/bh-free-37/ko08.pdf (Springer via MSI). Defs p.421–422 (k-CM (S,k,T), tests {0,+}, ops {−,0,+}, reverse T^{-1}); Thm 3 p.423: periodicity of 2-RCM undecidable (instances are complete M' = forward/backward simulation); Thm 6 p.423: undecidable whether a given COMPLETE 3-RCM admits a periodic configuration.
- Back-and-forth bijection ĝ on S×{+,−}×N^k: (c,+)↦(G c,+); (c,−)↦(G^{-1}c,−) if c∈im G (decided by (state,pattern) since M^{-1} deterministic), else (c,+). ĝ is a bijection; its periodic points are exactly G's periodic configurations; M complete: ĝ periodic ⟺ G periodic.
- Encoding: L=|S̃| states as residues s∈[0,L); n = s + L·k; counters = exponents of p_1..p_k (P = ∏p_j) in k; w = P-free part of k (sign incl.) is a passive fiber. Piece for (s, ρ mod PM): φ=+: (s+Lρ)(LPM) → (t+Lp_iρ)(Lp_iPM); φ=−: → (t+Lρ/p_i)(LPM/p_i); φ=0/switch: → (t+Lρ)(LPM). All canonical, preserve N_0. Bijectivity via density of integer points.
- Trap: k=0 points n=s form a finite invariant set ⇒ finite cycles always. Fix for (c): pick M ≥ 2 coprime to P; E_good = {M∤k} (machine, invariant since p_i coprime to M), E_bad = ⊔_s s(LM) carries a transported copy of an element with NO finite cycles.
- Element of CT(Z) with no finite cycles (2-adic north–south element of V): h0(n) = 4n+2 (n even), 2n (n≡3 mod 4), (n−1)/2 (n≡1 mod 8), (n−3)/4 (n≡5 mod 8). Its fixed points in Z_2 are (01)^∞ and (10)^∞ only (non-eventually-constant), all other points flow ⇒ no periodic integers. Transport to class c(N): c+Nq ↦ c+N·h0(q) (canonical).
- (b): machine on E_good ⊔ identity on E_bad: only finite cycles ⟺ M periodic (Thm 3). (c): machine on E_good ⊔ transported h0 on E_bad: no finite cycles ⟺ M has no periodic configuration (Thm 6, complete 3-RCM, P=30, M=7). Membership in CT(Z) via `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers` (17.59 node).
LANDED 71b76e027 (09-18). Kourovka 21.74(b) and (c) are both UNDECIDABLE (lane proof, not reviewed):
- `ct-z-finite-cycle-problems-are-undecidable`. There are explicit class-transposition words F_M and H_M, one pair for each reversible 2-counter machine M.
  - F_M has only finite cycles iff M is periodic.
  - H_M has no finite cycles iff M has no periodic configuration.
  - Inputs are Kari–Ollinger Thm 3 and Thm 6. The whole construction already lives in CT_{3,5,7,11,13}(Z).
  - Trick: "buffer" involutions, s1 = n<->2n and s2 = 2n<->f(n). They make F_M = f (+) f^{-1} an explicit word, so neither 17.59 nor ct-p-z item 3 is needed.
- `ct-z-north-south-element-has-no-finite-cycles`. psi = τ_{0(4),2(16)} τ_{3(4),14(16)} τ_{1(4),6(16)} τ_{1(4),10(16)} τ_{1(4),2(4)}.
  - psi has no finite cycles.
  - psi permutes no nontrivial residue-class partition, which makes it an explicit NO-instance of 21.74(a).
- Artifact gq-bh-bh-free-58-kari-ollinger-source.md.
Still open, and free for others: 21.74(a) and 21.73. (a) is r.e. For 21.73: the finite-order conjugacy classes look decidable, since involutions are determined by whether Fix is empty.
LANDED 99e1c5dc3 (09-18), Kourovka 21.73 torsion case: `ct-z-finite-subgroups-are-classified-by-stabilizer-sets`.
- Finite-group embeddings in CT(Z) are conjugate iff they have the same point-stabilizer set. So torsion elements are conjugate iff they have the same cycle lengths, and conjugacy is decidable when one element has finite order.
- This kills Salo-type routes for 21.73: they rely on finite-order yes-instances, and in CT(Z) those are decidable.
- Also noted: "blind multiplication", a second obstruction for counter-coded blinkers.
Lesson paragraph added to 71b76e027's node in b230a5543. Now: looking for an infinite-order conjugacy reduction for 21.73.
LANDED a95cb1edf (09-18): Kourovka 21.73 is UNDECIDABLE. Node `ct-z-conjugacy-problem-is-undecidable`.
- For each reversible counter machine M with initial configuration x*, explicit words A_M, B_M satisfy: halting ⟹ conjugate by an explicit involution in CT_{3,5,7,11,13}(Z); non-halting ⟹ not conjugate, even in RCWA(Z).
- Key tool: "arithmetic rigidity at infinity". Rcwa conjugators are linear on the far ends of multiplicative orbits, so non-S cofactors are end invariants.
- It holds in the fp simple group CT_P(Z) too. Input: Morita universality (not read at source).
- Remaining: 21.74(a).
LANDED 7c6468c08 (09-18), 21.74(a) obstruction: `ct-z-residue-partitions-cannot-carve-thin-invariant-sets`.
- Components lie in single classes, so a special invariant set W is visible to (a) only if it contains a co-class.
- Invariant sets inside pZ (p odd) never contain one, which kills machine-plus-single-mixer reductions.
- (a) stays OPEN. Next steps: thick (prefix-coded) special structure, or decidability on V via revealing pairs.
**09-18 ~17:00 (relaunched after the restart).**
- **Recovery.** All 7 work files were already on main, and nothing was unlanded.
- **21.74(a).** It now has a dedicated lane (bh-kourovka-2174a, 4267a301f). I sent them lemmas L1 and L2:
  - L1: in CT(Z), tame is the same as finite order;
  - L2: a partition whose parts lie inside single pieces exists iff g has finite order, so an infinite-order YES instance needs a coarse part.
  - I also sent the garbage obstruction: valuation-coded machines always carry garbage configurations, and no invariant set built from one run can contain a co-class.
- **Separator P_eff.** I independently derived the kill in CT_P(Z): parallel runs, an input clock compared with the verifier output, and a passenger-level detector, giving C_L(σ) = U_A. bh-invent-11 had already landed it in nV (c0dfc4ce5), so I did not land a duplicate node.
- **LANDED 49984b668:** research/artifacts/gq-bh-bh-free-58-referee-lamp-centralizers.md. It is a referee PASS of linear-time-rauzy-sets-exist and nv-machines-realize-linear-time-lamp-centralizers(-proof), with one repair R1: Lemma 1's completion must be done per copy-bit slice for F to be a bijection. It also records the CT_P(Z) second host.
- **Free for others.** Kourovka 20.44 is unowned. Heuristic: passenger cofactors give positive-density transversals for every valuation-coded group, and a counterexample would need additive passenger mixing on infinitely many runs.
- **Status:** idle.
**09-18 ~17:10: claimed Kourovka 20.44 (coordinator).**
LANDED 7b84a747f (09-18): Kourovka 20.44, `ct-z-orbit-transversal-dichotomy-is-collatz-hard`.
- Kohl's G_T = <τ_{0(2),1(2)}, τ_{1(2),2(4)}, τ_{1(4),2(6)}> ≤ CT_{3}(Z) has orbits in bijection-up-to-counting with 3x+1 components (Kohl's r, s, re-verified on all of Z).
- By a Terras–Everett parity-vector count, o(N) orbits meet [−N,N], so every transversal has density 0.
- Consequence: 20.44 YES ⟹ the 3x+1 map has finitely many cycles and divergent classes on Z (open); infinitely many components ⟹ 20.44 NO. 20.44 itself is still OPEN.
- Next: find a provable counterexample, i.e. a map with density-one stopping times and provably infinitely many components, realized by a f.g. subgroup.
LANDED 1c4a8a43c (09-18): `ct-z-orbit-transversal-counterexamples-need-unbounded-orbits`.
- If G has infinitely many orbits of size ≤ s, it has a positive-density transversal: small-orbit sets are residue classes up to a finite set (affine rigidity).
- So a 20.44 counterexample needs infinitely many orbits of unbounded or infinite size, glued by translations, with no local invariant at a rational point.
- Tried and failed: valuation strata; dilation copies g(3n) = 3g(n), which force zero translation parts; isolated fixed points; single V-elements. None gives a provable counterexample.
- 20.44 is OPEN. Status: idle.
LANDED (09-18) research/artifacts/gq-bh-bh-free-58-kourovka-20-44-status.md: best-known form of 20.44 and the failed routes (Conway maps are periodicity-conjecture-hard; two primes always mix digits). Conjecture: the dichotomy holds for f.g. subgroups of CT_0(Z) = V. Status: idle.
