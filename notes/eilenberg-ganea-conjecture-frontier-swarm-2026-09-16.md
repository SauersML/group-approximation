# Eilenberg--Ganea conjecture: frontier attack, 2026-09-16

- Agent: `hi-fron-eilenberg-ganea-conjecture` (swarm, angle FRONTIER).
- Hole worked: `bestvina-brady-epsilon-map-conjecture` (locked 2026-09-16, TTL 180m, unlocked at the
  end).
- Outcome: **reduction**. The ε-map hole is replaced by a strictly weaker sufficient claim (NE),
  which Whitehead's conjecture also implies. Some cases are proved unconditionally. Nothing is
  committed; the referee lands the work.
- Main artifact: `research/artifacts/eilenberg-ganea-frontier-2026-09-16.md`.

## 1. Frontier map

Beneath the root, on the landed head as read 2026-09-16:

- `eilenberg-ganea-conjecture` has no direct proof route. The live refutation path runs through
  `bestvina-brady-poincare-kernel-has-geometric-dimension-three`: `gd H_L = 3` for the
  Bestvina--Brady kernel `H_L`, with `L` a flag triangulation of the Poincaré spine.
- That claim has one route, `epsilon-map-conjecture-gives-poincare-kernel-gd-three`. It requires:
  - `bestvina-brady-epsilon-map-conjecture` (OPEN): the Remark on p. 470 of Bestvina--Brady;
  - `acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear` (claim A, established on main
    through Nitsche--Thom Theorem 1.2);
  - `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead` (established on main).
- The complementary side is `bb-kernel-gd-two-if-l-lies-in-contractible-2-complex` (claim C).
- **Choice.** The ε-map conjecture is the whole remaining input of the only refutation path, and
  it is a statement about maps out of one fixed finite 2-complex. So it is both the highest-leverage
  hole and the most concrete one. It was locked for this lane.

## 2. State of the art (literature gate, checked 2026-09-16)

The web search budget ran out during the gate, and the arXiv API then returned HTTP 429. This is a
spot check, not a review. The full table is in the artifact, §1.

- **Bestvina--Brady**, Invent. Math. 129 (1997) 445--470. Pinned earlier on main.
  - Theorem 8.7: `gd H_L = 3`, or Whitehead's conjecture fails.
  - The Remark on p. 470 is the ε-map conjecture.
- **T. T. Nguyên-Phan**, arXiv:1907.12063v1 (2019). Pinned earlier on main. The ε-map conjecture
  "remains open"; the relative form fails in dimension 1.
- **Nitsche--Thom**, J. Group Theory 25 (2022), arXiv:1811.07737v2. Pinned on main.
  - Theorem 1.2 (Gerstenhaber--Rothaus, Pestov): Kervaire--Laudenbach for hyperlinear groups.
  - Theorem 1.3: the covering form.
- **Abstracts only.**
  - S. Gersten, arXiv:1501.06875v3: a finite subcomplex of an aspherical 2-complex is aspherical
    iff `cd π_1 ≤ 2`.
  - A. Kar, N. Nikolov, arXiv:1801.04484: 2D problems (D2, relation gap). Nothing on ε-maps or
    `H_L`.
  - I. J. Leary, arXiv:1512.06609v4: uncountably many groups of type FP. Nothing decided on cd
    versus gd.
  - J. Howie, Math. Proc. Cambridge Philos. Soc. 127 (1999): a plus-construction reading of
    Theorem 8.7.
  - E. Pasku, arXiv:2107.12293: abstract only, **unverified**, unrefereed. Not used.
- **Titles only, bodies unread.**
  - arXiv:1911.03457: the Eilenberg--Ganea problem for families.
  - arXiv:2302.09686 and arXiv:2509.14615: cohomological dimension of group homomorphisms.
  - Berrick--Hillman (2019): content **unverified**.
- **Verdict.** No source seen, including those dated 2023--2026, settles the Eilenberg--Ganea
  conjecture, the ε-map conjecture, or `gd H_L`.

## 3. What was proved

These are complete proofs, modulo the pinned Nitsche--Thom Theorem 1.2 and recalled standard
topology. The artifact section is given for each.

1. **Lemma 1, coarse lifting (§2).**
   - Let `δ` be a Lebesgue number of the open vertex-star cover of `L`, and `g: |L| → |K|` a
     continuous surjection onto a finite simplicial complex with fibers of diameter `< δ`.
   - Then there is a simplicial `λ: K' → L` with `λ ∘ g ≃ id_L`, so `SL(2,5) ↪ π_1(K)` and `λ_*`
     is onto.
   - No extension over skeleta is needed: `λ(u)` is the vertex whose open star contains
     `g^{-1}(St u)`, and the straight-line homotopy runs inside carriers.
2. **Proposition Q (§3; claim `subcomplex-pi1-kernels-vanish-in-hyperlinear-quotients`).**
   - Let `Y` be a contractible 2-complex and `K ⊆ Z ⊆ Y` finite connected subcomplexes with
     `H_1(K) → H_1(Z)` injective. Every homomorphism `ρ` from `π_1(K)` to a hyperlinear group kills
     `ker(π_1 K → π_1 Z)`.
   - If `H_1(K) = 0`, every such `ρ` is trivial.
   - Proof: `H_2(Z, K) = 0`, and the exponent-sum matrix of the relative normal form is injective.
     Push the words along `ρ` and apply Nitsche--Thom 1.2 with `G := Q`.
   - This strengthens claim A, which is the case `ρ = id`.
3. **The statement NE (§4).** No surjective PL map `|L| → |K|` with fibers `< ε` has a finite
   subcomplex `K` of a contractible simplicial 2-complex as its image. Four implications are
   proved:
   - NE ⇒ `gd H_L = 3` (§4.1). The deck action is properly discontinuous, so `φ` has fibers of
     uniformly bounded diameter `D`. Rescaled shadows then give ε-maps onto `φ(S_(v,L))`.
   - ε-map conjecture + claim A ⇒ NE (§4.2). The cell-attachment model is transported into a
     contractible 2-complex by a pushout.
   - TF ⇒ NE (§4.3), by Lemma 1. Here TF is "finite subcomplexes of contractible 2-complexes have
     torsion-free `π_1`".
   - Whitehead ⇒ TF (§4.4). Asphericity gives `cd ≤ 2`, and `cd Z/p = ∞`.
4. **Consequences for images (§5).** Write `m = rank H_1(K)`.
   - Acyclic images (`m = 0`) are excluded unconditionally. `λ_*` is a nontrivial finite quotient,
     contradicting Q(b).
   - For `m ≥ 1`: for every nontrivial `β ∈ π_1(L)`, every finite subcomplex of `Y` in which
     `g(β)` dies kills a nonzero class of `H_1(K)`.
   - Lemma 3: `L ∪_λ Y' ≃ ∨^m S^2`.

Net effect on the graph:
- **Whitehead ⇒ TF ⇒ NE ⇒ `gd H_L = 3` ⇒ Eilenberg--Ganea fails.** The ε-map conjecture also
  implies NE.
- So the root's refutation path no longer needs the ε-map conjecture specifically. It needs only
  the weaker NE, which is itself implied by the weaker-than-Whitehead TF.

## 4. Approaches tried and where each dies

All of these attack NE in the remaining case `m ≥ 1` (artifact §6).

1. **Nitsche--Thom 1.3 on `Z/K`.** If `Z` kills `π_1(K)`, relative Hurewicz makes every class of
   `H_2(Z/K) ≅ Z^m` spherical. Spherical classes lift to every covering, so no covering has trivial
   `H_2`. Dies.
2. **Homotopy type of the pushout.** `L ∪ e^2`, attached along a non-central element of `SL(2,5)`,
   is `≃ S^2`, and `[L, ∨^m S^2] = 0` by Hopf. So `L ⊆ Z_λ ≃ ∨^m S^2` is consistent. Dies.
3. **Rank count for Nitsche--Thom 1.2.** Every enlargement killing `π_1(K)` has `ker E ≅ Z^m`,
   and 1.2 needs `ker E = 0`. Dies.
4. **Enlarge `K` to an acyclic `K⁺`.** Circular: extending `λ_*` requires solving the attaching
   words over `SL(2,5)` itself, and Q(b) says that always fails. Existence of `K⁺` inside `Y` was
   not established either. Dies.
5. **Control the null-homotopies.** One disc for one spine loop, whose support completes no relative
   cycle, would suffice. But nothing controls `Y`: if `gd H_L = 2`, `Y/H_L` has infinitely many
   cells. Dies.
6. **Correct `Y` by 2-cells.** The correcting loops are null-homotopic, so the new cells create
   `H_2`. Dies.
7. **Invariants.**
   - Gersten's criterion is silent, since `cd π_1(K) = ∞`.
   - `H^2(K; Z) = 0`, so characteristic classes vanish.
   - L²-invariants are dead (idea I5 of `research/artifacts/ideas-topology-2026-09-14.md`).
8. **Mapping cylinder.** `M_g ∪_K Y` is contractible and contains `L`, but it is 3-dimensional.
   The 2-dimensional replacement is a relative D2-type problem. Dies.
9. **TF directly.** The same support barrier as item 5. No source seen settles TF.

## 5. New graph nodes

**Claims.**
- `subcomplex-pi1-kernels-vanish-in-hyperlinear-quotients` (Q). Its proof route requires only
  `kervaire-laudenbach-holds-for-hyperlinear`.
- `spine-epsilon-images-avoid-contractible-2-complexes` (NE). OPEN, with an `## Attempts` section.
- `contractible-2-complex-subcomplexes-have-torsion-free-pi1` (TF). OPEN, with an `## Attempts`
  section.

**Routes.**
- `subcomplex-pi1-kernels-hyperlinear-quotients-proof` ⇒ Q.
- `spine-epsilon-images-avoiding-2-complexes-give-gd-three` ⇒
  `bestvina-brady-poincare-kernel-has-geometric-dimension-three`. Requires NE and
  `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`.
- `epsilon-map-conjecture-gives-spine-images-avoid-2-complexes` ⇒ NE. Requires the ε-map
  conjecture and claim A.
- `contractible-2-complex-torsion-free-gives-spine-images-avoid` ⇒ NE. Requires TF.
- `whitehead-conjecture-gives-torsion-free-subcomplex-pi1` ⇒ TF. Requires
  `whitehead-asphericity-conjecture`.

**Artifact.** `research/artifacts/eilenberg-ganea-frontier-2026-09-16.md`.

No existing node was edited.

## 6. Next steps

1. **Referee first.** Check §4.1 Steps 2--4 of the artifact:
   - the simplicial model of a 2-dimensional `K(H_L, 1)`;
   - Bestvina--Brady's quasi-isometry constants for shadows, independent of `s`;
   - the non-equivariant subdivision making `φ(S_(v,L))` a subcomplex.
   This is the load-bearing step of the new route to `gd H_L = 3`.
2. **TF against the literature.** Search the survey literature on Whitehead's asphericity question
   (Rosebrock's surveys; Bogley's chapter in *Two-dimensional homotopy and combinatorial group
   theory*) for torsion-freeness of fundamental groups of subcomplexes of contractible 2-complexes.
   These references were recalled, not fetched. If TF is known, the root is refuted.
3. **NE with `m ≥ 1`, in a controlled setting.**
   - Test NE when `Y` is additionally locally finite, or cocompact under a free action.
   - These special cases do not cover the Bestvina--Brady situation, since `H_L` is not finitely
     presented. They are a testing ground for the support barrier (item 5 of §4), which is where
     geometric control could enter.
4. **Experiment (not done).**
   - Enumerate small simplicial quotients `K` of flag triangulations of the Poincaré spine with fibers
     below the Lebesgue number and `H_1(K) ≠ 0`.
   - Test by computer whether they embed in small contractible 2-complexes (collapsible or
     Andrews--Curtis-trivial enlargements).
   - A positive hit would refute Whitehead's conjecture. A systematic failure is only evidence.
