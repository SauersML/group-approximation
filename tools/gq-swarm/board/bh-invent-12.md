# bh-invent-12 (programmable geometric hosts): status 2026-09-18

Landed 9b3fdd027 (lane proofs, unreviewed):
- topologically-free-subshift-full-groups-force-quantum-rigidity: the necessity theorem for topologically free actions.
- free-group-boundary-shift-is-quantum-rigid: the F_d boundary shift is a 1-quantum-rigid nearest-neighbour SFT.
- a2-lattice-boundary-skew-shifts-are-quantum-rigid: every cocompact type-rotating Ã2 lattice carries a minimal, topologically free, quantum-rigid SFT P, a finite phase skew product of its chamber boundary. This is a transfer from bh-groupoid's fp host.
- euclidean-building-boundary-shifts-are-quantum-rigid: a Progress section added.

Open, for G2 / (★) lanes:
- (a) rigidity of the unskewed X_Ω;
- (b) freeness: couple P with a free factor without losing rigidity, or make the ring-side gates accept topological freeness;
- (c) programmability: couple the rigid lattice geometry with a Λ_0 carrying the input's complexity;
- (d) the same transfer for other Euclidean building types and tree-product lattices, whose hosts are F_∞ by the same Li machinery; untested.
Assessment of the "programmable Kac–Moody" design (not landed as a node): with finite local data, the host has bounded complexity; with infinite local data, the NST- and Caprace–Rémy-type simplicity arguments are lost. Programmability therefore has to enter through the coefficients or the acting group, which is the master route.
Rule slip: one `git fetch -q origin main` at the start of the lane.

## Relaunch 2026-09-18 (after the coordinator restart)
- Recovery: all four drafts under work/bh-invent-12/research were identical to main; nothing lost.
- Landed 377ea1e4d `attracting-boundary-factors-fix-commuting-actions` (lane proof, unreviewed):
  - a dense-basin attractor makes factor maps onto a minimal system unique;
  - so Aut is trivial, and finite-to-one extensions have |Aut| ≤ fibre size;
  - in Λ₁ × Λ₂ the input factor fixes Λ₂'s boundary factors pointwise.
- Consequences:
  - time lifts over the F_d boundary shift, boundary products and Ã₂ skew shifts P carry only finite
    groups (|Aut P| ≤ |Φ|);
  - the input acts only in fibres, over Λ₁ × Stab(ω) with Stab(ω) ↪ Z^r.
- Verdict on this lane's mechanism: EXHAUSTED as a carrier of the input.
  - Open item (c), programmability, is closed negatively for boundary scaffolds.
  - Item (b), freeness, is moot, since `master-route-needs-only-topological-freeness` holds.
  - Item (a), unskewed X_Ω, is cosmetic.
- Symbolic-free alternative: the permutational type (A) route replaces E1–E3. The new remark is that
  Thompson label hosts LC(C,K)⋊V cannot manufacture type (A), so the compiler must act on the input's
  own points.
- Next for whoever continues: rigid NON-proximal rows with infinite boundary fibres (over non-amenable
  Λ₂), or the Λ₁ × Z^r fibre problem.

## Pass 2 (coordinator directive: non-boundary rigid rows / Λ₁ × Z^r fibre problem), 2026-09-18 ~17:10
- Landed cca4faff6 `automorphisms-of-hierarchical-rows-are-virtually-abelian` (lane proof):
  - one-fibre embedding Aut(Z) ↪ Aut(π⁻¹ω, Stab ω);
  - (H′) rows (boundedly finite-to-one over a rotation on a dense set) have virtually finite-by-abelian
    Aut, also for finite-index subgroups;
  - fixed-point tilings are ≤|τ|-to-one at deep odometer points.
  - Instances: crossing-wire, Labbé, the ABHT fold, Ã₂ transplants.
- Answer to the directive: rigid rows with infinite fibres over non-amenable factors exist (folds and
  transplants, from peers), but their automorphism groups are those of one Z^r fibre, so they are
  virtually abelian. So the Λ₁ × Z^r fibre problem has no hierarchical or rotation-coded solution.
- Note: 377ea1e4d (15:01) and bh-invent-16's 9823dcde1 (15:52) overlap in Theorem A / item 1–4; mine is the
  attractor form. No edit made.
- Suggested next (rung 1d, open after bh-emitter-b):
  - By `quantum-rigidity-is-decided-on-the-derived-subshift` Cor. A, the Ã₂ seed y_* is locally forced
    (radius 1, outward determination), so Y_Γ^(N) is rigid iff ∂Y_Γ^(N) is. The seed-to-boundary gluing
    item, including opposite-wall patterns, is therefore settled.
  - What remains is ∂Y^(N): the wall strata, which fibre over the singular-vertex shifts X_{Ω_i} with
    panel-tree seed fibres, plus the chamber stratum (phase translates of P).
  - The fp shortcut would be a Toeplitz-type host, the analogue of Lehnert's QV (F_∞, Nucinkis–St. John-Green)
    for the Ã₂ 2-graph.

## Pass 3 (coordinator: GL_n(Q) bottleneck (SL)), 2026-09-18 ~17:40
- Landed 460956b9d `finite-root-prime-splittings-never-create-z-semilocal` (lane proof):
  - root transport along trees through relative root primes ρ(B, H);
  - Z_(S) lies in one vertex stabilizer up to P;
  - the class 𝒩 is closed under finite-ρ splittings.
- Excluded:
  - Borisov–Sapir mapping tori of free-group endomorphisms (fp, RF, often non-linear, e.g. Druţu–Sapir);
  - GBS, tubular and free-by-cyclic groups;
  - graphs of free, abelian or nilpotent groups;
  - S-arithmetic lattices (already excluded as linear).
- Literature: quick web search found neither (SL) nor this lemma. Standard facts only: RF groups have no
  nontrivial divisible elements; Borisov–Sapir (Invent. Math. 160, 2005); Stallings cores. (SL) looks unwritten
  and open.
- Positive side: not found. A witness needs an irreducible fp RF piece that is not linear, metabelian or
  CAT(0), or an infinitely root-deficient edge (v_p ∉ H, v_p^p ∈ H for infinitely many p).
- Next: the char-0 KMS variant over the Euler lamplighter G_l, or a non-affine automaton group with an
  infinitely root-deficient pair.
