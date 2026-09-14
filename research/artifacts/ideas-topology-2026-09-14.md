# Ideas lane: Whitehead asphericity, Eilenberg--Ganea, Andrews--Curtis (2026-09-14)

Lane `ideas-topology`. The lane ideated first, then made quick kills, then executed
one idea in depth.

**What main already had.**
- f658813da: `whitehead-asphericity-conjecture`, `eilenberg-ganea-conjecture` and the
  Bestvina--Brady dichotomy.
- b8c495ff0: `andrews-curtis-conjecture`, the stable AK(3) correction and the
  Z-conjecture equivalence.
- 3d31757e8: the balanced Kervaire--Laudenbach to Whitehead bridge.
- 56f8f8ca2, 58aa5ecdc: the balanced-failure filter.
- Greps of main's claim and route nodes found none on labelled oriented trees (LOTs).
- The only L²-Betti mention of Whitehead is a passing remark in
  `l2-normal-rank-bound-fails-for-torsion-free-groups`: the torsion-free Osin--Thom
  inequality β₁^(2) ≤ nrk − 1 was "an imagined second road to … a case of Whitehead
  asphericity". The ideas I1–I3 below are that road, made explicit for one-cell complements.

## 1. Ideas, with the first decisive test and the kill criterion

Status in brackets: dead, covered, alive (not yet tested), or executed.

**I1 [executed, §2]. L² vanishing kills π₂ of one-cell complements.**
- Idea: if a finite contractible 2-complex L loses one open 2-cell, the remainder K has
  χ(K) = 0. The Euler--Poincaré formula for L²-Betti numbers then gives
  b₂^(2)(K̃) = b₁^(2)(π₁K). When that vanishes, the integral 2-cycles of K̃ sit inside
  a zero ℓ²-kernel, so π₂(K) = 0.
- Test: write the argument out.
- Kill: some step needs more than faithfulness of von Neumann dimension.
- Not on main as a node. Main mentions the road only in passing (see the header).
- Likely known: Osin--Thom (arXiv:1108.2411) tie their inequality to a case of Whitehead
  asphericity, and Hillman, *Four-manifolds, geometries and knots*, Chapter 2 treats
  deficiency-one complexes. Neither was checked here.

**I2 [executed, §2]. LOT complexes are one-cell complements.**
- Idea: adding one 2-cell that kills a vertex generator of a LOT presentation gives a
  contractible complex. So by I1, a non-aspherical LOT complex has a group with positive
  first L²-Betti number.
- Kill: the augmented complex is not contractible. It is contractible; the proof is in
  `lot-complexes-vanishing-l2-betti-aspherical-proof`.

**I3 [alive, at least as hard as balanced Kervaire--Laudenbach, §3]. Do one-cell
complement groups always have b₁^(2) = 0?**
- This would prove Whitehead's finite one-cell case, including asphericity of all LOT
  complexes.
- Test: a structural argument from H₁ = Z, weight one and deficiency one, or numerics
  (I16).
- Kill: a one-cell complement group with b₁^(2) > 0.
- Relation to Osin--Thom:
  - One-cell complement groups have normal rank 1, so for torsion-free ones I3 is the
    finitely presented case of the Osin--Thom inequality.
  - The Fisher--Lodha counterexamples on main are not finitely generated, so they do not
    reach I3.
  - With torsion the inequality already fails (`torsion-breaks-l2-normal-rank-bound`), but
    no such witness is known to be a one-cell complement group.
- Landed as the OPEN node `one-cell-complement-groups-have-vanishing-first-l2-betti`.

**I4 [alive]. Fibred one-cell complements.**
- Idea: if the commutator subgroup of a one-cell complement group is finitely generated
  and infinite, the group is a mapping torus of it. Lück's and Gaboriau's vanishing
  theorems for normal subgroups (recalled, not pinned) would then give b₁^(2) = 0, so
  the complex would be aspherical.
- Test: pin the vanishing theorem at source and land the corollary.
- Kill: the theorem needs more than finite generation of the kernel.

**I5 [dead]. L² invariants on Bestvina--Brady kernels to decide gd(H_L).**
- Any 2-dimensional K(H_L,1) has infinitely many cell orbits
  (`bestvina-brady-poincare-kernel-has-geometric-dimension-two`, Attempt 1).
- L²-Betti numbers of H_L cannot separate cd 2 from gd 2: the Eilenberg swindle adds free
  π₂ summands.

**I6 [dead as a separator, not pinned]. Quantum state-sum invariants of 3-deformations
for Andrews--Curtis.** For a contractible presentation complex, every
representation-theoretic count collapses to the trivial group. The known TQFT-type
invariants of 2-complexes are expected to reduce to finite-group data. No source was
pinned in this lane; this is recorded only as a warning.

**I7 [covered]. Stable AC through the Z-conjecture.** Already on main
(`shehper-z-conjecture-iff-one-stabilization-ac`).

**I8 [covered]. Balanced Kervaire--Laudenbach failures as AC candidates.** Bridge B5 in
`research/artifacts/ideas-bridges-2026-09-13.md`.

**I9 [dead]. Gersten's cd-2 criterion on the Bestvina--Brady subcomplex.** The
subcomplex has π₁ with a binary icosahedral retract, so cd = ∞ and the criterion is
silent. This is recorded in the Bestvina--Brady artifact, Attempt 1.

**I10 [alive, low]. Almost-representation defect profiles as AC-distance lower bounds.**
- Idea: AC moves change relator lengths boundedly, so the defect of approximate
  homomorphisms F₂ → Sym(n) killing r₁ and r₂ scales with trivialization length.
- This gives distance bounds only, never an invariant.
- Kill: the bounds are weaker than the known length lower bounds (Lishak, Bridson;
  recalled).

**I11 [partially killed]. The L² bridge to Kervaire--Laudenbach through χ = 1 complexes.**
- The balanced-failure complexes K_P of 3d31757e8 have χ = 1, so b₂^(2)(K_P) ≥ 1 holds
  automatically, and I1 constrains nothing there.
- What survives is I15: the wedge K_P ∨ S¹ has χ = 0.

**I12 [alive, not started]. Howie's ascending-chain type.**
- Idea: extend I1 to increasing unions, using Lück's dimension function for arbitrary
  modules.
- Test: pin Howie's reduction at source.
- Kill: the dimension of the colimit loses the vanishing.

**I13 [dead]. Exotic 4-sphere invariants for AK(n).** The Akbulut--Kirby homotopy spheres
are known to be standard (attributed to Gompf; not re-read), so no smooth invariant
separates them.

**I14 [alive, consequences only]. Further restrictions on one-cell counterexample groups.**
- Property (T) forces b₁^(2) = 0 (Delorme--Guichardet, as used on main in
  `ghb7-l2-betti-two-euler-proof`), so these groups lack (T).
- Inner amenable groups are reported to have b₁^(2) = 0 (Chifan--Sinclair--Udrea;
  recalled).
- Test: pin both at source and add them to
  `whitehead-one-cell-counterexamples-have-positive-first-l2-betti`.

**I15 [executed, §2]. The one-cell case alone implies the balanced Kervaire killing form.**
- Idea: a balanced failure (G, w) gives a contractible L whose one-cell complement
  L − e_W is K_G ∨ S¹. The wedge retracts onto K_G, and π₂(K_G) ≠ 0 by main's bridge.
- Not on main: main's route `nonnegative-deficiency-kervaire-via-finite-whitehead` used the
  full Whitehead conjecture.

**I16 [alive, MSI only]. Numerical census of b₁^(2) for small LOTs.**
- Idea: take normalized first Betti numbers of low-index normal subgroups of LOT groups
  on at most 6 vertices, computed with GAP.
- This is only evidence: LOT groups are not known to be residually finite, so Lück
  approximation may not apply.
- Kill for I3: ratios bounded away from 0 along a residual chain.

## 2. Execution of I1, I2 and I15

**Landed claims** (Cairn rg:2):
- ESTABLISHED `finite-2-complex-with-zero-second-l2-betti-is-aspherical`: a finite
  connected 2-complex with infinite π₁ and χ(K) + b₁^(2)(π₁K) = 0 is aspherical. Route
  `finite-2-complex-zero-second-l2-betti-aspherical-proof`.
- ESTABLISHED `contractible-complex-minus-cell-has-cyclic-homology`: removing one open
  2-cell leaves χ = 0, H₁ ≅ Z, H₂ = 0, and an infinite weight-one π₁. Route
  `contractible-complex-minus-cell-homology-proof`.
- ESTABLISHED `whitehead-one-cell-counterexamples-have-positive-first-l2-betti`: a
  non-aspherical one-cell complement has b₁^(2) > 0 and no amenable normalish subgroup.
  Route `whitehead-one-cell-positive-l2-betti-proof`.
- ESTABLISHED `lot-complexes-with-vanishing-first-l2-betti-are-aspherical`: every LOT
  complex is a one-cell complement, and it is aspherical when b₁^(2) = 0. Route
  `lot-complexes-vanishing-l2-betti-aspherical-proof`.
- OPEN `contractible-2-complex-minus-a-cell-is-aspherical`: Whitehead's finite one-cell
  case.
- OPEN `one-cell-complement-groups-have-vanishing-first-l2-betti`: I3.

**Conditional routes:**
- `one-cell-l2-vanishing-gives-one-cell-whitehead`: I3 implies the one-cell case.
- `kervaire-killing-form-via-one-cell-whitehead`: the one-cell case implies
  `kervaire-killing-form-holds-over-nonnegative-deficiency-groups`.

**Trust surface.**
- Proved inline: vanishing of b₀^(2) for infinite groups, and faithfulness of von
  Neumann dimension.
- Pinned at source: Lück's survey *L²-Invariants from the Algebraic Point of View*
  (arXiv:math/0310489), from its e-print TeX
  `/scratch.global/sauer354/ideas-topology/src/luck/ltwoalg.tex`. The pinned statements
  are:
  - the definition of b_p^(2)(G) (l.1176);
  - cellular computation (l.1292);
  - homology invariance (l.1321);
  - b₀^(2) (l.1437);
  - the Euler--Poincaré formula (l.1456);
  - the identification with reduced ℓ²-homology (l.1669–1695).

  Quotes are in `finite-2-complex-zero-second-l2-betti-aspherical-proof`. The survey's
  proofs point to Lück's book (Theorems 1.35, 6.54) and to Lück 1997 (Theorem 6.1), which
  were not opened.
- Import used: the amenable-normalish vanishing,
  `amenable-normalish-kills-l2-betti-bounded-cohomology`.
- No novelty is claimed, and the literature was not searched. I1 and I2 are likely known.
  I15 is elementary and may be folklore.

## 3. Exact barrier

- **The L² route is at least as hard as balanced Kervaire--Laudenbach.** The chain now on
  main runs `one-cell-complement-groups-have-vanishing-first-l2-betti` ⇒
  `contractible-2-complex-minus-a-cell-is-aspherical` ⇒
  `kervaire-killing-form-holds-over-nonnegative-deficiency-groups`.
  - Proving I3 would settle the killing form over every finitely presented group of
    deficiency zero.
  - That is open beyond the recalled Gerstenhaber--Rothaus, Pestov and Klyachko cases.
- **Direction.** I1 is one-directional. An aspherical one-cell complement can have
  b₁^(2) > 0 in principle, so a counterexample to I3 would not by itself refute
  Whitehead.
- **Reach.** The L² constraint sees only χ = 0 complexes. On the χ = 1 balanced-failure
  complexes it gives nothing (I11).
- **Untouched.** The Bestvina--Brady dichotomy and Andrews--Curtis are not touched by this
  execution: I5, I6, I9 and I13 are dead, and I10 is low.
