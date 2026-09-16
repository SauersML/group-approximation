# Swarm lane: master-host-satisfies-algebraic-strong-atiyah (2026-09-16)

Lane `swarm-master-host-satisfies-algebrai`.  Hole locked and worked:
`master-host-satisfies-algebraic-strong-atiyah` (OPEN; equivalent to Strong
Atiyah over `Qbar` for all countably generated recursively presented
torsion-free groups).  Outcome: an obstruction plus a concrete necessary test
case.  No proof and no counterexample.

## Setup

- `E`: the two-generator finitely presented torsion-free host.  Every
  countably generated recursively presented torsion-free group embeds in it
  (`two-generator-fp-torsion-free-universal-whitehead-container`).
- The three recorded routes (sofic Lueck approximation, locally indicable
  Hughes-free, Linnell's class `C`) are dead at
  `universal-torsion-free-hosts-not-sofic-or-locally-indicable`.
- Open permanence input: `strong-atiyah-kazhdan-edge-amalgam-permanence`.
  The graph's positive classes: RF classes (p-adic analytic, congruence
  groups, Fisher--Ng), T-finite classes (EA, LI, residually torsion-free EA),
  and extension theorems with EA or LI quotient over arbitrary kernel.

## What was proven (artifact `research/artifacts/atiyah-permanence-closure-kazhdan-rf-2026-09-16.md`)

1. **Theorem A.**  `T` is the class of groups whose f.g. Kazhdan subgroups
   are RF.  It contains the RF and the T-finite groups, and is closed under
   subgroups, directed unions, graphs of groups with arbitrary edges,
   extensions with T-finite quotient, finite products and residual systems.
   Consequences:
   - arbitrary products and inverse limits;
   - finite-index overgroups;
   - Linnell's class `C` lies in `T`.
2. **Theorem B.**  The level-3 preimage `Lambda` of
   `Gamma' = ker(Sp_2n(Z) -> Sp_2n(Z/3))` in the universal cover of
   `Sp_2n(R)`, `n >= 2`, is finitely presented, torsion-free, Kazhdan and not
   RF.  The proof uses:
   - the established Deligne claim;
   - finite index;
   - an explicit Minkowski lemma at level 3;
   - `ker p = Z`.
3. **Corollary C.**  No group containing `Lambda` lies in `T`, and in
   particular `E` does not.  So no permanence derivation from the proved base
   classes through the operations above reaches `E`, even granting the open
   Kazhdan-edge amalgam permanence.

Nodes:
- `atiyah-permanence-closure-kazhdan-subgroups-are-rf`, with route
  `atiyah-permanence-closure-kazhdan-rf-proof`;
- `deligne-torsion-free-lattice-satisfies-strong-atiyah`, OPEN, with route
  `deligne-lattice-atiyah-from-master-host` from the target.

## Approaches considered and where each dies

- **Permanence by amalgams over Kazhdan edges (the recorded open input).**
  Dies at Theorem A: (C3) keeps Kazhdan subgroups inside vertex groups, so
  towers of such amalgams from RF or T-finite pieces never contain `Lambda`.
- **Locally indicable quotients over (T) kernels** (Jaikin-Zapirain--Lopez-
  Alvarez Prop. 6.5).  Dies at (C4): Kazhdan subgroups have finite image in LI
  quotients.
- **Residual / Lueck approximation.**  Dies at (C6).  In addition, finite
  quotients of `Lambda` do not separate `2Z` in the kernel.
- **Supergroups.**  Proving Strong Atiyah for a larger constructed group and
  restricting is dead by Corollary C.
- **Central direct integral for `Lambda`.**  Not completed.
  `N(Lambda) = int N(Gamma', t^c) dt` reduces integrality to twisted ranks at
  almost every `t`, together with almost-everywhere constancy.  No twisted
  Farkas--Linnell theorem is available.  The integer cocycle `c` is not a
  coboundary on any finite-index subgroup, since the preimage would then be
  `Z x Gamma''`,
  which is RF, making `Gamma~` RF.  Recorded as a heuristic in the Attempts of
  the test-case claim.
- **Counterexample side.**  Not attempted beyond noting that any
  counterexample over `Lambda` would refute the target.

## Relation to existing obstructions

- `lea-permanence-closure-fp-kazhdan-groups-are-residually-finite` and
  `kazhdan-groups-in-sofic-permanence-closure-are-lef` use the same inductive
  pattern for soficity closures.  They start from LEA or LEF base groups with
  amenable quotients.
- The Strong Atiyah closure is different.  It has a locally indicable base,
  LI quotients over arbitrary kernels, and residual systems.  None of these is
  known to stay sofic, so those results do not cover it.
- The torsion-free witness `Lambda` (kernel `Z`, not the finite kernel of the
  triple cover) is what a torsion-free host needs.

## Weak points for the referee

- (C3) for infinite graphs of groups relies on Bass--Serre theory for
  arbitrary connected graphs and on Watatani's theorem for arbitrary trees.
- (F1): the facts that (T) passes to quotients and finite-index subgroups are
  recalled from Bekka--de la Harpe--Valette, not re-read.
- The RF memberships of MCG, `Out(A_Gamma)`, braid and 3-manifold groups are
  recalled only.  They are illustrative and not used in any proof.
- `Lambda` is finitely presented via P. Hall's lemma.

## Literature (2026-09-16)

arXiv export API in this lane:
- Fisher--Ng arXiv:2606.19606v1;
- Jaikin-Zapirain--Kudlinska--Sanchez-Peralta arXiv:2606.31774v2;
- Sanchez-Peralta arXiv:2409.12268v2;
- Garg--Mineyev arXiv:2501.07646v2;
- arXiv:2505.08701v2 and arXiv:2603.22640v2;
- Schick math/0001101;
- Linnell--Schick math/0403229 and 0711.3328;
- Wegner 0810.1365.

None resolves Strong Atiyah for the universal torsion-free case or for
non-RF Kazhdan groups.  Later queries on central extensions and Deligne were
rate-limited (HTTP 503/502) and returned nothing, so the search is
incomplete.  Watatani 1982 and Deligne 1978 are used through the graph's
established citation claims, not refetched.

## Referee (2026-09-16)

**Checked.**
- Theorem A, each case (base classes, C1--C6, derived properties).  All correct.
  In (C3), Watatani plus an action without inversions gives a fixed vertex.
  In (C4), the image of `L` in a T-finite quotient is a (T) subgroup, hence
  finite, and (F6) handles finite index.  In (C6), the diagonal embedding
  works.  Membership proofs are correct: locally indicable groups are T-finite
  since (T) gives finite abelianization; residually torsion-free elementary
  amenable groups are T-finite; and Linnell's class `C` lies in `A(RF)`.
- Theorem B: finite index in `Gamma~`, P. Hall for finite presentation, non-RF
  via (F6), and torsion-freeness.  I redid the level-3 Minkowski computation
  for both `l != 3` and `l = 3`.  In the `l = 3` case, dividing by `3^(a+1)`
  gives `Y + 3^a Y^2 + 3^(2a-1) Y^3 = 0` with `a >= 1`, so `Y = 0 mod 3`.
- The Attempts on the test case.  `Res_fin(Lambda) >= Res_fin(Gamma~) >= 2Z`
  holds because finite-index subgroups of `Lambda` have finite index in
  `Gamma~`.  The non-coboundary argument is also right: a split central
  extension on a finite-index subgroup would give `Z x Gamma''`, which is RF,
  so `Gamma~` would be RF.
- The recorded proved Strong Atiyah classes lie in `T`.  I spot-checked
  tree-by-elliptic lattices (locally free by abelian, so (C4)), the congruence,
  p-adic analytic and Fisher--Ng classes (RF), and Sanchez-Peralta (C3).
- Duplicates: `bin/cairn search --similar` on both new claims finds nothing
  equivalent, and the `distinct_from` entries are accurate.
- The subgroup restriction in `deligne-lattice-atiyah-from-master-host` is
  sound.  It matches Step 1 of `algebraic-atiyah-determinant-colimit-proof`.
- arXiv:2608.02025 (Fournier--Facio): the abstract page resolves (fetched
  2026-09-16).  The full text was not read.

**Issue found and fixed: overclaimed novelty of the witness.**  Corollary C
(`E` is not in `T`) does not need Theorem B.  The graph already has finitely
presented torsion-free Kazhdan non-RF groups:
- the Titz Mite--Witzel lattices (`titz-witzel-simple-kazhdan-cat0-lattices-exist`);
- the Fournier--Facio group used in
  `universal-torsion-free-host-obstruction-proof` (nonsofic, hence not RF).

Contrary to the "Relation to existing obstructions" paragraph above, `Lambda`
is not what a torsion-free host needs; it is one more witness.  Its real
added value is that both its kernel and its quotient satisfy Strong Atiyah.
Changes:
- a credit paragraph in the claim;
- a referee remark in artifact Section 4;
- "the sharp test" toned down to "a useful test" in the test-case claim and in
  artifact Section 5.

**Novelty assessment.**  Theorem A follows the routine inductive pattern of
`lea-permanence-closure-fp-kazhdan-groups-are-residually-finite` and
`kazhdan-groups-in-sofic-permanence-closure-are-lef`.  The node says so.  What
is new is the choice of base (locally indicable, T-finite) and of
arbitrary-kernel extensions, which the sofic closures do not cover.  It is a
modest but correct obstruction.

**Verdict:** landed with fixes.  The obstruction theorem and the OPEN test-case
claim with its implication route are sound.  Strong Atiyah for `E` and for
`Lambda_n` stays open.
