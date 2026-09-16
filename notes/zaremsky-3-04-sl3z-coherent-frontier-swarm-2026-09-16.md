# Zaremsky 3.4 (is SL_3(Z) coherent?) — frontier swarm, 2026-09-16

Agent: hi-fron-zaremsky-3-04-sl3z-coherent. Angle: FRONTIER.

Hole locked and worked: `sl3z-contains-cd2-euler-positive-fibered-subgroup`
(criterion C1 for incoherence).

Full proofs: `research/artifacts/sl3z-normal-f2-obstruction-2026-09-16.md`.

## 1. Angle

I mapped the open holes under `sl3z-is-incoherent` and picked the one with the
best mix of leverage and tractability.

- The two live criteria are:
  - C1: a fibred cd-2 subgroup with `χ != 0`;
  - C2: a virtually RFRS cd-2 subgroup with `b_2^(2) > 0`.
- Both are existence statements about thin Zariski-dense subgroups, and no
  candidates are known.
- The C1 Attempts section (2026-09-13) names free-by-free `F_n x| F_m` as the
  candidate family and records "no obstruction to existence is known".
- This is the family where the literature has incoherence results
  (Kropholler–Walsh). So the highest-leverage question was which
  free-by-free groups can sit inside `SL_3(Z)` at all.

## 2. State of the art (sources, dated)

**External gate.** No source found states that `SL_3(Z)` is coherent or
incoherent. The question remains open.

- M. Zaremsky, *Some open problems* (list version of July 12, 2026; scratchpad
  copy fetched by the swarm 2026-09-16). Problem 3.4 "Is SL_3(Z) coherent?"
  carries no update annotation.
- D. D. Long, A. W. Reid, *Small subgroups of SL(3,Z)*, preprint dated August
  18, 2010, text read 2026-09-16 (download URL not recorded).
  - Theorem 4.1: `ρ_k(F)` has finite index in `SL(3,Z)` for
    `k = 0, 2, 3, 4, 5`.
  - Proposition 5.2: an incoherence strategy through Bieri's theorem.
  - Question 3: is some `ρ_k` faithful?
  - Section 6.1: `π_1` of closed surfaces embeds, and Goldman's Zariski-dense
    (3,3,4) triangle group.
- R. Kropholler, G. Walsh, *Incoherence and fibering of many free-by-free
  groups*, arXiv:1910.09601 (v3 2020-11-18, "To appear in Annales de
  l'Institut Fourier"). Abstract read 2026-09-16, body not read. The abstract
  says finite-index subgroups of `F_2 x| F_n` are incoherent.
- R. Kropholler, S. Vidussi, G. Walsh, arXiv:2005.01202, **withdrawn** (v3
  2021-10-01), citing an error in the proofs of Theorems 3.1 and 3.5. So
  incoherence of all free-by-free and surface-by-free groups is not
  established by that paper.
- D. Kochloukova, S. Vidussi, survey arXiv:2404.01447. Abstract read before a
  context reset. It does not settle incoherence of all free-by-free groups.
- Fisher–Linton–Sánchez-Peralta, arXiv:2603.16763, as used by the repository
  node `virtually-rfrs-cd2-coherence-characterization` (criterion C2). Not
  re-read here.
- R. Bieri, *Normal subgroups in duality groups and in groups of cohomological
  dimension 2*, JPAA 7 (1976). Known only through Long–Reid's quotation.
- K. Tsouvalas and R. Canary on projective Anosov subgroups of `SL(3,R)`
  (virtually free or virtually surface). **Unverified**: recalled from a
  reading before a context reset; the arXiv author page returned 404.

Web search budget was exhausted, so the gate used direct arXiv abstract pages
and author listings. The check was not exhaustive.

**In the repository before this session** (ESTABLISHED):

- `sl3z-infinite-order-centralizers-are-solvable`;
- `sl3z-products-of-infinite-subgroups-are-polycyclic`, which kills Stallings'
  `F_2 x F_2` mechanism;
- `sl3z-incoherence-witnesses-are-zariski-dense-thin`;
- `sl3z-infinite-index-normal-fibers-force-zariski-density`;
- the Wang-sequence route `sl3z-incoherent-via-euler-fibered-subgroup`.

## 3. What was proven

All proofs are in the artifact (Sections 2–7). They rest on graph imports
(I1, I2), classical imports (I3–I6: Nielsen generation and
`Out(F_2) ≅ GL_2(Z)`, virtual freeness of `GL_2(Z)`, Nielsen–Schreier,
P. Hall), and two literature quotes (I7, I8) used only by routes.

1. **Lemma S** (`sl3z-normal-subgroup-class-stabilizers-are-polycyclic`).
   Let `N ◁ G <= SL_3(Z)`. The stabilizer in `G/N` of the `N`-conjugacy class
   of an infinite-order `x in N` is `C_G(x)/C_N(x)`, which is polycyclic.
   - If some class has a finite orbit, `G/N` is virtually polycyclic.
   - If `G/N` is free, the stabilizers are trivial or `Z`.
   - For subgroups `A <= N`: `Stab_{G/N}([A]_N) ≅ N_G(A)/N_N(A)`.
2. **Lemma N.** Every automorphism of `F(a, b)` sends `[a, b]` to a conjugate
   of `[a, b]^{±1}`. Proof: check the three Nielsen generators. A word-level
   check is in `experiments/sl3z-normal-f2-obstruction-2026-09-16/`.
3. **Proposition A** (`sl3z-normal-f2-subgroups-have-virtually-cyclic-quotients`).
   Let `N ◁ G <= SL_3(Z)` with `N ≅ F_2`.
   - `C_G(N)` is finite, and the monodromy has finite kernel.
   - `G/N` is finite or virtually `Z`.
   - Infinite-order elements have infinite-order monodromy.
   - `G` is finitely presented, and either virtually `F_2` or virtually
     `F_2 x|_φ Z` with `φ` of infinite order in `Out(F_2)`.

   Proof idea: by Lemma N, the orbit of `[c]_N` has size at most 2. Lemma S
   makes an index-at-most-2 subgroup of `G/N` polycyclic, and it maps with
   finite kernel into the virtually free `GL_2(Z)`.
4. **Corollaries.**
   - A1: no `F_2`-by-(not virtually cyclic) subgroup, hence no `F_2 x| F_m`
     (`m >= 2`), `F_2 x| Z^2` or `F_2`-by-surface. This refutes the new claim
     `sl3z-contains-f2-by-free-subgroup`.
   - A2: no incoherence witness has a normal `F_2`.
   - A3: stabilizers of classes of rank-two subgroups are virtually cyclic.
   - A4: surface-with-boundary fibres with monodromy permuting the boundary
     classes force `G/N` to be virtually polycyclic.
   - A5: for `F_n x| F_m <= SL_3(Z)`, the stabilizers on element classes and on
     rank-two subgroup classes are cyclic.
5. **Criterion C3** (`sl3z-contains-cd2-group-with-fg-nonfree-normal-subgroup`,
   new OPEN claim). A finitely generated `G <= SL_3(Z)` with `cd G <= 2` and a
   finitely generated, non-free normal subgroup of infinite index.
   - C3 implies incoherence by Bieri's theorem
     (`sl3z-incoherent-via-bieri-normal-subgroup`, resting on Long–Reid's
     quotation).
   - C1 implies C3 (`sl3z-euler-fibered-subgroup-gives-bieri-witness`): a free
     fibre would make `G` the fundamental group of the mapping torus of a
     rose, so `χ(G) = 0`.
   - Long–Reid's Proposition 5.2 is an instance of C3, once "not free" is read
     as "not virtually free". Their proof passes to a torsion-free
     finite-index subgroup.

Nodes written: 4 claims (one of them refuted), 5 routes (one dead), and
1 artifact. No route has `requires: []`.

## 4. Approaches tried and where each dies

- **Import Kropholler–Walsh through an embedded `F_2 x| F_m`.** Dies:
  Proposition A. Recorded as the refuted claim
  `sl3z-contains-f2-by-free-subgroup` and the dead route
  `sl3z-incoherent-via-f2-by-free-subgroup`. This was the one family where an
  incoherence theorem is available (abstract-level) without Euler
  characteristic bookkeeping.
- **Free-by-free C1 candidates with fibre rank 2.** Dies: Corollary A1.
- **Surface-with-boundary-by-free candidates with geometric monodromy** (any
  fibre rank). Dies: Corollary A4. A boundary class has a finite orbit, so the
  quotient is virtually polycyclic, hence cyclic if free.
- **Non-hyperbolic `F_n x| F_m`, `n >= 3`, where a non-cyclic subgroup of the
  base fixes the class of an element or of a rank-two subgroup of the fibre.**
  Dies: Corollary A5.
- **Hyperbolic `F_n x| F_m`, `n >= 3`.** Survives. Both stabilizer conditions
  hold automatically: a nontrivial stabilizer would give `Z^2`, directly or
  through Lemma N. So Lemma S and Proposition A give nothing.
  - Canary–Tsouvalas (unverified) would force such a subgroup to be
    non-Anosov.
  - I did not find a further obstruction.
  - The C1 hole's older lead ("properness of the `Out(F_n)` action on
    projective Anosov representations") is consistent with this, but was
    not pursued.
- **Non-free fibres (C3 in general).** Survives. Lemma S constrains `(G, N)`
  only when `G/N` is large and some infinite-order class has a finite orbit.
  Proposition A does not apply.
- **Long–Reid `ρ_k` as a C3 source.** Survives only for unfaithful `ρ_k` with
  thin image of virtual cohomological dimension 2 and fibre image not
  virtually free. Their Theorem 4.1 kills `k = 0, 2, 3, 4, 5` (finite index in
  `SL(3,Z)`), and faithfulness kills C3 (fibre image `≅ F_2`). No
  computation of `vcd ρ_k(Γ)` was attempted.
- **Criterion C2 (virtually RFRS, `b_2^(2) > 0`).** Not attacked.
- **Direct coherence proof.** Not attempted. The repository's non-dense /
  tree-hierarchy results reduce it to Zariski-dense thin subgroups outside the
  hierarchy `H`, and nothing here enlarges `H`.

## 5. Next steps

1. **Verify the two literature imports used by routes.**
   - The hypothesis range of Bieri (JPAA 7, 1976): is `G` required to be of
     type `FP_2`?
   - The exact range of `n` in Kropholler–Walsh arXiv:1910.09601.
   - Neither changes Proposition A.
2. **Hyperbolic `F_n x| F_m <= SL_3(Z)`, `n >= 3`.**
   - Test whether Zariski-dense hyperbolic cd-2 thin subgroups of `SL_3(Z)`
     that are not virtually free or surface groups are ruled out, for example
     via the Canary–Tsouvalas classification (verify it first) plus a
     non-Anosov analysis.
   - The concrete sub-question: can a normal `F_n` (`n >= 3`) of a hyperbolic
     subgroup of `SL_3(Z)` have a free non-cyclic quotient? Lemma S gives no
     restriction here.
3. **Long–Reid C3 instances.** For `k` outside `{0, 2, 3, 4, 5}`:
   - decide whether `ρ_k` is unfaithful (Question 3);
   - estimate `vcd ρ_k(Γ)` and the index of `ρ_k(F)` in `ρ_k(Γ)`.
   - Theorem 5.1 of Long–Reid already gives failure of the finitely generated
     intersection property whenever `ρ_k(z)` has no power in `ρ_k(F)`.
4. **Surface-by-free with closed fibre.** Bieri already forbids a closed
   surface group from being normal of infinite index in a cd-2 group. In
   `SL_3(Z)` the cd-3 case (`π_1(S_g)`-by-`F_m`) is what matters for the
   Euler-characteristic mechanism in dimension 3; it was not examined.
5. **Lemma S for other small fibres.** Any normal subgroup `N` with a
   characteristic finite set of infinite-order conjugacy classes gives the
   same conclusion as Proposition A. Examples are `N = π_1` of a punctured
   surface where `Out(N)` preserves the punctures, and `N` a one-relator
   group. The artifact records only the `F_2` and bounded-surface cases.

## 6. Files

- Claims:
  - `research/sl3z-normal-subgroup-class-stabilizers-are-polycyclic.md`
  - `research/sl3z-normal-f2-subgroups-have-virtually-cyclic-quotients.md`
  - `research/sl3z-contains-f2-by-free-subgroup.md` (refuted)
  - `research/sl3z-contains-cd2-group-with-fg-nonfree-normal-subgroup.md` (open)
- Routes:
  - `research/sl3z-normal-subgroup-class-stabilizers-are-polycyclic-proof.md`
  - `research/sl3z-normal-f2-subgroups-have-virtually-cyclic-quotients-proof.md`
  - `research/sl3z-incoherent-via-f2-by-free-subgroup.md` (dead)
  - `research/sl3z-incoherent-via-bieri-normal-subgroup.md`
  - `research/sl3z-euler-fibered-subgroup-gives-bieri-witness.md`
- Artifact: `research/artifacts/sl3z-normal-f2-obstruction-2026-09-16.md`
- Experiment: `experiments/sl3z-normal-f2-obstruction-2026-09-16/lemma_n_check.py`
  and its `.out`.

Weakest points, for a referee to attack first:

- `Out(F_2) ≅ GL_2(Z)` and Nielsen generation (classical, recalled). They are
  used only through "`Out(F_2)` is virtually free" and "Lemma N holds on
  generators".
- The C3 route rests on Bieri via a quotation.
- The dead route rests on the Kropholler–Walsh abstract.
