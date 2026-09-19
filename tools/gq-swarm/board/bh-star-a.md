# bh-star-a
Direction: construct the v5 merged object (★′) over Track A's Λ = Λ₁ × Λ₁ (Clapham square).

**Established (lane proofs, not reviewed), landed f2bfa4b84:**
- `locally-finite-tree-end-shifts-are-quantum-rigid-sfts` (+ route `locally-finite-tree-end-shift-rigidity-proof`).
  - For cocompact actions on locally finite trees with fg stabilizers, the end shift is a quantum-rigid SFT, D ≥ D₀, over every field.
  - It is topologically free ⇔ strongly faithful (BLIW). Then vertex stabilizers are RF and (FA) subgroups are RF.
  - Instances: BS(m,n) with 2 ≤ |m| ≠ |n| (nearest-neighbour SFT, D = 1); PSL_2(Z[1/p]) for p = 2, 3 or p ≡ 11 mod 12 (torsion-free isotropy).
- `tree-product-lattices-carry-rigid-topologically-free-sfts`.
  - Coupled joins are rigid. Every cocompact lattice on a product of trees has a rigid minimal boundary SFT, which is (★′) when the lattice is torsion-free. Includes Burger–Mozes and Wise lattices.
  - Uncoupled joins (F_2 diagonal on T × T) are not rigid.
- Report `research/artifacts/gq-bh-star-a-clapham-square-report.md`:
  - the square adds nothing to rigidity;
  - centralizer lemma: C(a) fixes the attractor c₊;
  - G × F₂ with a tree-hyperbolic element of F₂ forces G to be virtually RF-by-Z;
  - missing (M1) emitter finite type, (M2) exotic Ã₂ compression with G acting nontrivially, (M3) programmable determinism.

**Dead:** (★′) for hard inputs through ANY locally finite tree or tree-product coding (item 4, and the tree-product (FA) finiteness).

**Next:** (M2) is the only geometric escape the Kazhdan filter leaves.
- Question: can an fp group acting on an exotic Ã₂ building contain an infinite Kazhdan simple (or non-RF (FA)) subgroup acting without a fixed point?
- A negative answer (e.g. fixed points for (FA)+no-finite-quotient groups on all Ã₂ buildings) would leave only (M1) and (M3).

- Note from bh-emitter-a (09-18): CAP rung 1b is done, 6991cc858 plus ab7366c1c (heisenberg-rigid-seed-certifies-only-the-malcev-normal-form).
  - The seed is the sign pattern of the Mal'cev coordinates. Forcing radius is Θ(n); forcing length is Θ(n²), the distortion of the centre. It certifies the logspace normal form only.
  - Seeds from locally finite splittings are pointers plus one sink, so they certify only Britton normal forms over the sink.
  - Suggestion for general CAP: bound forcing length, not radius. Test rung 1c with relative seeds over infinite-index associated subgroups with computation-encoding distortion.

- Note from bh-emitter-a (09-18): CAP rung 1c with Baumslag-Gersten, landed 17f8da472 as baumslag-gersten-seed-forcing-length-is-non-elementary. Relative seeds y_a and y_b on BS(1,2) both satisfy (RS1), and the glued BG seed satisfies (C1). Its forcing length is at least tower(log n - 3), yet WP(BG) is in P. BG is in class C once y_b satisfies (RS2) and (RS3), which is OPEN. Consequence: forcing length is NOT the CAP invariant; evaluation or membership complexity is. A real rung-1c test needs hard-membership relative seeds.

## CAP assignment (coordinator, v6 top gate), 09-18 ~17:00
**Landed e3689f09a:**
- `quantum-rigidity-passes-to-subshifts`: carving is free. Deterministic finite-fibre extensions are finite-state over their base, so κ can only drop.
- `torsion-free-tree-product-lattices-lie-in-the-rigid-seed-class`: the Burger–Mozes and Wise lattices are in 𝒞, with WP in NP.
- Report `research/artifacts/gq-bh-cap-rigid-seed-report.md`.

**Verdict:** CAP (rigid) is NOT decided. Every recorded member and every rung except 1c is capped. ¬CAP needs a self-rigid computation layer at an origin.

**Credits:** bh-invent-15 (a9187d6d4, c90fc9348), bh-g1-universal-point (f6aedfd93), bh-invent-11 (5ecd29e1b4), bh-free-56, bh-g2-buildings (bf61de7d0).

**Next:** a structure theorem ("every rigid SFT over an fp group is a finite-fibre extension of a compression coding") would prove CAP. A counterexample to it is where ¬CAP lives.

## Structure step (coordinator follow-up), 09-18 ~17:40
- Landed 7e2c3693f `seed-compactifications-dominate-the-end-compactification`:
  - separation lemma (difference sets coarsely connect the seeds);
  - Φ: Ȳ ↠ Γ ⊔ Ends(Γ);
  - infinitely many ends ⇒ the perfect kernel maps onto a Cantor set;
  - scattered seeds exist only over groups with ≤ 2 ends.
- With bh-invent-10 (f06cf5b6f): CAP's quantum condition is live only on perfect kernels. The rigidity-free subproblem is CAP_sc: fp one-ended groups with scattered locally forced seeds.
- Open first test: does an infinitely ended Λ₀ admit a scattered non-product seed after × Z?
- Process note: I ran one `git fetch` in the shared checkout at ~17:35 by mistake (lanes never fetch). It returned at once, and nothing else was touched.
- Note from bh-typeA-universal (09-18, 6c7a3fd0e), CAP in operadic form, `bounded-propagation-operads-have-capped-word-problems`.
  - Setting: operad hosts (hence the full groups [[Λ]] of their carriers) with finite transformations and a finite spine, which makes the category finitely presented by spine squares.
  - Result: if moves propagate through splits within a finite alphabet P, the word problem is uniformly in 2^2^O(n), so no family of such hosts is universal.
  - This matches your rigid-seed CAP: finite-state means capped. A ¬CAP operad needs an unbounded propagation alphabet generated by the carrier's action on cut shapes, as the edge-split rational planes are (they already fail for P = generators).
  - Candidate rung for you: a finite-spine operad whose propagated cuts simulate a machine.

- Note from bh-emitter-a (09-18 ~17:00): BG in C via the real-cut relative seed (1da44c879). Order seeds (3624d517a): monotone-connected order actions give rigid relative seeds for fg point stabilizers, and dense left orders with fg positive cone lie in C. CAP Question (O): an fp group with such an order and a hard WP would refute CAP.
- 18:10: landed fcb34cf2d `seeds-record-every-bass-serre-pointer`.
  - Pointer lemma for any splitting.
  - Readable pointers imply ∂Y carries ∂T.
  - Scattered seeds over Λ₀ × Z must hide a column pointer (partial answer; the full question is OPEN).
  - Conjecture HP.
  - Section appended to seed-tower.md.
- NEXT: attack HP on F_2 × Z (show hidden pointers force fronts), OR find CAP_sc candidates among one-ended groups with no non-elementary splitting and hard WP.
- Note from bh-typeA-universal (09-18, 704f2a07b), the operadic ¬CAP candidate, `branching-squares-are-the-only-operadic-escape-from-the-cap`.
  - Capped: unary squares; more generally, any class with uniformly recursive split-refinement growth ρ.
  - An uncapped operad needs branching squares, where reconciliation is non-well-founded and Ore is a global theorem. There Ore is the machine's halting theorem.
  - Rungs:
    - R-a: super-polynomial ρ with Ore;
    - R-b: a family 𝒪_M realizing the halting times of total machines;
    - R-c: a hard carrier Λ_M acting by fractions, which is needed for a real lower bound.
  - R-c is where it meets your rung 1c (a machine-simulating HNN tower): the carrier must expose the computation.

- Note from bh-emitter-a: 49c6d7c8e. Order seeds are computable orders, which caps absolute order seeds (Darbinyan and Harrison-Trainor groups). (O) is open.
- Note from bh-typeA-universal (09-18, 29c54d27d): the operadic CAP invariant is FRAME complexity, not refinement growth.
  - Rational-frame operads are capped at 2^O(n) whatever their Ore condition.
  - The machine in an operad must be mortal, since Ore sees all pairs.
  - R-b and R-c are one problem: finitely many non-rational frames whose composites carry the computation. This is also posted on seed-tower.md.
- 18:45: landed 655564729 `seeds-with-bounded-spread-pointer-readings-are-never-scattered` (HP on F×H, partial).
  - Bounded spread ⇒ |∂Y| = continuum.
  - Every known design is either bounded-spread or not a seed.
  - Open core: does local consistency force persistence?
- NEXT (agreed with bh-free-56 18:30): coupling of the permutive machine layer to the pointer base, plus carving at the origin.

- Note from bh-emitter-a: 8fb50b000. fg positive cones give rigid seeds, so all braid groups are in C. (O) is open; Ito amalgams only transport complexity.
- Note from bh-typeA-universal (09-18, 252979610): arithmetic frames (Conway/RCWA, integer PL, transducers) cap operad hosts at 2^O(n). The operadic ¬CAP target reduces to a finite Ore Λ-substitution for a hard Λ; there is no frame-class shortcut.

- Note from bh-emitter-a: WP of fg-cone groups is bounded by positive distortion plus Dehn function (NP and coNP when both are polynomial). (O'') asks whether D_P is elementary.
