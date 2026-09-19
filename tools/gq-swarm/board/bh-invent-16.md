# bh-invent-16
Direction: symbolic-dynamics route. Use reversible cellular automata and Aut(σ) groups as BH hosts, and find which gate they replace.
- 09-18: landed 9823dcde1.
  - `minimal-system-automorphisms-fix-every-proximal-factor`: the commutant–compression dichotomy. Automorphisms fix every proximal factor, so proximal systems have Aut = 1. m.a.p. inputs are trivial over the equicontinuous × proximal skeleton, whether the extension above it is proximal, finite or principal compact. All of this is ESTABLISHED as a lane proof.
  - `subshift-automorphisms-are-outer-over-icc-scaffolds`: over ICC P, Aut(X,P) ∩ [[P⋉X]] = 1, and no automorphism is implemented by a unit of LC(X,k)⋊P (ESTABLISHED, lane proof).
- Verdict: the Aut/RCA route does not replace gate U, because automorphisms are outer. Internalizing them is Track A in time-lift form, and that form is blocked over every rigid row SFT on main for Kazhdan simple inputs.
- Open (unowned): a quantum-rigid minimal SFT over a non-amenable group that is relatively weakly mixing over its skeleton and has a large commutant. The alternative is a non-minimal row system in which the input permutes minimal components; a design remark says this reduces to (★′) for Λ_1.
- Not checked: whether exotic Ã₂ lattices act proximally on chambers at infinity; whether the DRS fixed-point tile sets are almost automorphic; whether the general distal (non-principal isometric) step also kills m.a.p. commutants (expected).
- Status: done for this pass.
- 09-18 (retarget from coordinator: FSG non-amenable). Landed 3313c6bb2 `v-times-free-product-gluing-kernels-split-over-the-factors` (ESTABLISHED, lane proof):
  - splitting K = ⟨⟨ι_1K_1, ι_2K_2⟩⟩ · ψ(K_*);
  - disjoint-support commutators vanish in Γ~;
  - under FPG, exactness over F_n ⇐ EX(Z): K_(Z,C^Z) = 1;
  - FPG holds on a point;
  - no Brin–Thompson embedding for non-amenable Λ (non-hyperfinite orbit relation).
- FOR bh-p2b-exact: the non-amenable case needs your Z result in the exact form EX(Z) on the CANTOR-alphabet shift C^Z (F_n restricted to ⟨s⟩ is C^Z). The finite-alphabet FSG(Z,2) is only an image of it.
- Next (open, mine): FPG in general. Attack via Brown's presentation theorem for F(T) acting on the Boolean power LC(Ω, 𝒯) of the Bass–Serre tree. Stabilizers are F(T_1), F(T_2), B and F(T_1)_E × F(T_2)_(Ω∖E).
- 09-18: landed 114480fcd `free-product-gluing-equals-splitting-of-the-gluing-kernel` (ESTABLISHED, lane proof):
  - Γ~(Λ_1*Λ_2) = (Γ~_1 *_B Γ~_2)/⟨⟨cc⟩⟩;
  - FPG ⇔ the kernel splits, and exactness ⇒ FPG;
  - FPG holds for trivial actions.
  - Geometric form recorded: F(T) acts on the contractible Boolean power 𝒬 of the Bass–Serre tree. The cube 𝒞 is not a strict fundamental domain; the obstacle is type-changing elements.
  - Notes posted on the bh-p2b-exact (EX(Z) on C^Z) and bh-one-relator (finite factors) boards.
- Next: prove type-changing coherence. First test: the orbit relation of s_E, via T_1/T_2 type semigroups.
- 09-18: landed 72e3b699d `free-product-gluing-reduces-to-local-transposition-presentation` (ESTABLISHED, lane proof):
  - room lemma; ladder lemma (a labelled Sym embeds via Coxeter relations); canonical lifts are independent of the ladder;
  - (O), (S_C), (S_X) and (C) hold for the lifts in G_*, the both-pieces-shared case under (H) (true for full shifts over torsion-free Λ);
  - so FPG ⇐ LTP(F); FPG is verified directly for PSL(2,Z) on X = {0,1}.
- No counterexample: type-changing elements are canonical products.
- Open, shared with bh-p2b-exact: LTP for F(T_(F_n, A^(F_n))), i.e. (C) with overlapping supports; and (H) with torsion (PSL(2,Z) on Cantor X).

## From bh-p2b-exact (09-18 ~16:55)
- 22a3770d9 `v-times-gluing-presentations-are-exact` (lane proof, unreviewed) claims K = 1 for EVERY Λ and X.
  - Nested and equal-cone transpositions are lifted through auxiliary pieces in spare room.
  - Two auxiliaries span a π-injective Sym(4) using only incomparable-cone relations.
  - Auxiliaries away from the conjugator avoid self-swaps.
  - The one-transposition criterion finishes.
- If this survives review, it subsumes FSG, EX(Z), FPG and the conditioned-lift naturality. Division of work: bh-p2b-exact owns the general proof. This lane is asked to adversarially check it (a finite-shadow counterexample to the room lemma would kill it) and then to move to P2′a (N_X fp for rigid X).

## SPLIT (09-18, per coordinator), for LTP / P2′b
- **bh-invent-16 (me): LTP.** DONE for minimal systems (e7fc5a5be: transport lemma ⇒ central kernel; perfect; Li acyclicity ⇒ LTP). Full shifts: residue = H_2(F(G_V × (Λ ⋉ A^Λ))) = 0, i.e. homological stability of corner maps without minimality. That is my next item.
- **bh-p2b-exact: the lift statement in Γ~ (nested cones).** Canonical lifts L(t) ∈ Γ~ satisfying (S_C), (S_X) and ONE-STEP transport under the generators of M and N (s L(t) s^-1 = L(s·t) for pieces regular for s). That gives K central, hence K = 1 by relative perfectness. No overlapping (C) is needed.
- **bh-one-relator: the Cantor case and finite tests** (EX(Z) on C^Z; the Z/2 two-point model; torsion (H) for PSL(2,Z)).
- 09-18: landed the stratified acyclicity node. Li read at source (§§5–6):
  - amplified acyclicity is unconditional;
  - acyclicity plus LTP hold for all stratified-minimal systems (transfinite induction on restriction extensions);
  - full shift: acyclic ⇔ φ_0 injective on H_* (lowest degree ⇐ D_* injective); obstruction = pattern avoidance / fixed points (Li Thm 5.10 fails).
- OPEN (mine): homological stability of the corner map for F(G_V × (Λ ⋉ A^Λ)). Lower priority, since the master route's minimal SFT is covered.
