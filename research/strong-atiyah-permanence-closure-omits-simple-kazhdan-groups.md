---
rg: 2
id: strong-atiyah-permanence-closure-omits-simple-kazhdan-groups
kind: claim
title: Simple Kazhdan lattices are atoms of every Strong Atiyah permanence closure, so extensions, colimits and limits of proved classes never reach the master host
distinct_from:
  atiyah-permanence-closure-kazhdan-subgroups-are-rf: that closes the class of groups whose Kazhdan subgroups are residually finite, which fails for central extensions with Kazhdan quotient (its Sharpness remark); this uses the invariant "contains a fixed finitely presented simple FA group", which survives arbitrary extensions, directed colimits with arbitrary maps and marked limits. So adding the Deligne lattice or any central-extension permanence does not reach the master host.
  sofic-permanence-closure-omits-simple-fa-nonsofic-groups: that is the same closure lemma in the sofic lane, applied to a hypothetical nonsofic simple FA group whose existence is open; this applies it to Strong Atiyah, where the atom exists (the Titz Mite--Witzel simple lattices lie outside every proved Strong Atiyah base class), and derives the host-independent gate.
  universal-torsion-free-hosts-not-sofic-or-locally-indicable: that excludes the master host from three specific classes; this excludes it from the closure of every class of groups without a Titz Mite--Witzel subgroup under all group-constructive permanence operations at once.
  atiyah-kazhdan-edge-blocks-both-permanence-routes: that says two proof frameworks fail at one Kazhdan-edge amalgam; this says that even granting every open permanence theorem, no permanence argument from the proved classes reaches the host.
---

**ESTABLISHED (unreviewed)** by [[strong-atiyah-simple-kazhdan-atoms-proof]].

Let `S` be an infinite, finitely presented, simple group with Serre's property
FA.  Consider the following operations on classes of groups:

- (O1) subgroups;
- (O2) directed colimits with arbitrary structure maps (directed unions are a
  special case);
- (O3) extensions with arbitrary kernel and quotient: `N ⊴ G` with `N` and
  `G/N` in the class, including central and finite-index extensions;
- (O4) fundamental groups of graphs of groups, with vertex groups in the
  class and any edge groups and edge maps;
- (O5) subdirect products: `G` with homomorphisms `pi_i: G -> G_i` into the
  class and `∩ ker pi_i = 1`.  This covers residual systems and restricted and
  unrestricted products; with (O3) it covers wreath products;
- (O6) limits in the space of finitely generated marked groups, and local
  embeddability into the class.

For a class `Y` let `A(Y)` be its closure under (O1)--(O6).

1. **Atomicity.**  If `S` embeds in a group of `A(Y)`, then `S` embeds in a
   group of `Y`.
2. **The atoms exist for Strong Atiyah.**  Let `S` be any of the five simple
   finite-index subgroups `Gamma^_i^q` of the Titz Mite--Witzel lattices
   (`titz-witzel-simple-kazhdan-cat0-lattices-exist`).  Then `S` is
   torsion-free, finitely presented, simple, infinite and Kazhdan.  It is not
   amenable, not residually finite and not locally indicable.  So
   `A(amenable ∪ RF ∪ LI)` contains no group with a subgroup isomorphic to `S`.
   This closure contains every group for which the graph records a proof of
   Strong Atiyah (list in the proof, Section 3).  It also contains the Deligne
   lattice `Lambda_n`, a central extension of a residually finite group.
3. **The master host lies outside.**  The master tester `E` of
   `master-host-satisfies-algebraic-strong-atiyah`, and every group containing
   all finitely presented torsion-free groups, contains `S`.  So `E` is not in
   `A(Y)` for any class `Y` of groups without a subgroup isomorphic to `S`.
   In particular these do not reach `E` from the proved classes, even in
   combination:
   - `strong-atiyah-kazhdan-edge-amalgam-permanence` (O4);
   - central `Z`-extension permanence, the loophole named in the Sharpness
     remark of `atiyah-permanence-closure-kazhdan-subgroups-are-rf` (O3);
   - adding `deligne-torsion-free-lattice-satisfies-strong-atiyah` to the base;
   - Det-colimit permanence (O2);
   - Lück-type approximation by residual systems (O5), and marked-limit
     approximation (O6).
4. **The gate.**  Any proof of `master-host-satisfies-algebraic-strong-atiyah`,
   or of Strong Atiyah over `Qbar` for all torsion-free groups, must at some
   leaf prove Strong Atiyah directly for a group that contains `S`.  By
   subgroup permanence this includes Strong Atiyah for `S` itself:
   `titz-witzel-simple-lattices-satisfy-strong-atiyah`.

## The exact failing step, by operation

- (O2): a finite presentation of `S` factors an embedding into a colimit
  through one stage.
- (O3): `S ∩ N` is normal in `S`, so it is `1` or `S`.
- (O4): FA makes `S` fix a vertex of the Bass--Serre tree.
- (O5): some projection is nontrivial on `S`, hence injective.
- (O6): a marked limit eventually contains a nontrivial quotient of `S`, which
  is `S` itself.

The only operations that can create `S` are quotients and direct proofs.
Permanence of Strong Atiyah to torsion-free quotients would already imply the
conjecture, since every countable torsion-free group is a quotient of a free
group.

## What dies at the atom, and what survives

Every direct method recorded on the graph dies at `S` at a named step
(proof, Section 5):
- no proper finite-index subgroup or quotient: Lück approximation, pro-`p`
  and Iwasawa algebras, congruence and virtually special methods;
- no proper normal subgroup: Linnell--Schick crossed-product induction and
  locally indicable extensions;
- perfect: Hughes-free division rings;
- FA: Bass--Serre and Cohn-coproduct reductions;
- isolated: approximation by marked groups.

What survives:
- approximations that are not by groups (sofic or hyperlinear; soficity of
  `S` is open, and soficity alone gives no integrality);
- the geometry of the exotic `C~_2` building;
- ring-theoretic arguments inside `Qbar[S]` itself.

**Calibration.**
- The congruence Kazhdan groups of `congruence-kazhdan-groups-satisfy-strong-atiyah`
  are residually finite, so they are in `A(RF)`.  The obstruction does not
  depend on property (T) alone.
- The Burger--Mozes simple lattices in `Aut(T_1) x Aut(T_2)` are finitely
  presented, torsion-free and simple, but they lack FA.  Their vertex
  stabilizers on `T_1` act freely on `T_2`, so they are graphs of finitely
  generated free groups and lie in `A(LI)` by (O4).  So FA cannot be dropped
  from item 1, and simplicity alone forces nothing.  This membership is only
  architectural: the graph records no proof of Strong Atiyah for these
  lattices, and (O4) over free edges is not a recorded permanence theorem.

**Scope.**  This is a statement about proof architecture.  It does not decide
Strong Atiyah for `S` or `E`.
