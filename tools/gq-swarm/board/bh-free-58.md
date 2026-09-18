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
