---
rg: 2
id: ck-envelope-simple-core-has-finite-bi-index
kind: claim
title: The normal-generator envelope can be chosen so that the simple core has finitely many double cosets
distinct_from:
  finite-infranormal-subgroup-is-normal: that concerns finite subgroups and their normalizers; this concerns finiteness of a DOUBLE COSET SPACE of an infinite, non-normal subgroup, where neither the subgroup nor its index is finite.
  ck-envelope-has-a-finitely-normally-generated-maximal-kernel: that asks for a compactness property of the normal lattice of the envelope; this asks for a finiteness property of the double coset space of one subgroup pair. The two are not the same statement. Correction 2026-09-17: this one implies that one for the same envelope, by bi-index-core-makes-normals-core-class-unions and by normally-generating-core-bi-index-bounds-normal-height. No converse is known.
  kazhdan-boone-higman-conjecture: that asks for finitely presented simple Kazhdan hosts; this asks for a finite bi-index core in a Kazhdan envelope. By ck-finite-bi-index-hole-is-kazhdan-boone-higman they are equivalent when the core is free, and this one implies that one in every reading.
  ring-elementary-bh-hosts-are-kazhdan: that is an established permanence lemma making ring-host Boone--Higman hosts Kazhdan; this is the open envelope statement, whose free-core reading those hosts would supply.
  simple-core-bi-index-counts-coset-action-pair-orbits: that PROVES the coset action is faithful and identifies its pair-orbits with double cosets, for any envelope; this asserts that the count can be made finite, which is the open part and is a statement about the construction rather than about the action.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
  - research/artifacts/ck-quotient-and-cover-bi-index-obstruction-2026-09-08.md
  - research/artifacts/finite-bi-index-normal-lattice-collapse-2026-09-17.md
---

The embedding of `chatterji-kassabov-normal-generator-embedding` can be
arranged so that, in addition to its stated conclusions, the simple core `S`
satisfies

    | S \ Gamma / S |  <  infinity .

Open over other envelopes and embeddings. The canonical corner and its
nontrivial quotients are excluded by explicit double-coset obstructions.

## Why it would finish

By `simple-core-bi-index-counts-coset-action-pair-orbits` the coset action
`Gamma` on `Gamma/S` is then faithful, has finitely generated point
stabilizer `S`, and has finitely many orbits on pairs, while `Gamma` is
finitely presented.  Those are exactly the hypotheses of
`twisted-brin-thompson-finite-presentation-criterion`, so `SV_Gamma` is a
finitely presented simple group, and it contains `Gamma`, hence `S`, hence
the original group.

The appeal of the route is that it never chooses a maximal normal subgroup
and never asks for a finite normal generating set.  It replaces the
normal-lattice question of
`ck-envelope-has-a-finitely-normally-generated-maximal-kernel` with a
double-coset question, which is a different kind of object with different
tools.

## Attempts

1. **Read it off the existing construction.**  *Fails immediately.*  The
   Chatterji--Kassabov proof controls a normal-generation relation and a
   presentation; it says nothing about `S \ Gamma / S`, and the intermediate
   objects — a group ring, a ring extension, an elementary matrix group —
   carry no double-coset bookkeeping to inspect.  With
   `universal-sandwich-ring-is-finitely-presented-and-injective` the envelope
   has an explicit matrix image `EL_4(U)`, so its double cosets are a
   concrete object to compute with. Finite presentation of that matrix
   image is not established; the finitely presented envelope is a marked
   cover as in [[ck-steinberg-marked-cover]]. The later double-coset
   obstruction applies to both the image and the marked cover.
2. **Derive finiteness from the normal-generation property.**  *No
   implication found.*  Normal generation constrains the normal closure of
   one element; a bi-index bound constrains the whole double coset space.
   The near-solution says every proper normal subgroup misses `S`, which is
   compatible with `S` being, for instance, of infinite index with
   infinitely many double cosets.
3. **Enlarge `S` until the bi-index drops.**  *Deferred, and the obvious
   version is self-defeating.*  Bi-index falls as the subgroup grows, and at
   `S = Gamma` it is 1 — but then the payoff is vacuous, because
   `simple-core-bi-index-counts-coset-action-pair-orbits` degenerates and one
   would already need `Gamma` simple.  A useful version would enlarge `S` to
   some intermediate subgroup that is still simple, or still finitely
   generated with the conjugation property the criterion needs; no such
   intermediate was identified.
4. **Use a different point set than `Gamma/S`.**  *Deferred.*  The criterion
   applies to any faithful action of `Gamma`, not only the coset action on
   `Gamma/S`.  Any faithful `Gamma`-set with finitely many pair-orbits and
   finitely generated point stabilizers would do, and the coset action is
   merely the first candidate because faithfulness is free there by the
   near-solution.  Searching the other faithful actions of `EL_4(U)` is
   untried.
5. **Quotient or cover the canonical corner arrangement.** Refuted by
   `ck-quotient-corner-has-infinite-bi-index`. In every nontrivial
   quotient the root image is the additive group of the infinite ring
   `U/lev(N)` and still separates corner double cosets. Marked covers
   map onto this infinite double-coset set, whether or not the roots lift
   as commuting subgroups. Finite-index enlargement of the stabilizer
   also preserves infinite bi-index. An infinite enlargement or a
   genuinely different marking is necessary for this kind of repair.
6. **Take a quotient of the marked cover whose map no longer descends to
   a nontrivial matrix quotient.** This remaining possibility is constrained
   by [[ck-cover-quotient-kernel-dichotomy]]: the entire new quotient must
   be the image of the covering kernel. If that kernel were solvable or
   locally finite, no proper quotient could repair the canonical coset
   action. These kernel properties are not established for the construction.
7. **Inverter biography: what a finite bi-index envelope is forced to be.**
   *Result: the hole collapses onto Kazhdan Boone--Higman.* By
   `bi-index-core-makes-normals-core-class-unions`, if
   `n, n' in N` lie in one double coset `SgS` with `N` proper normal, then
   `n' = a n b` forces `ab in N ∩ S = 1`. So `N` is a union of at most
   `r = |S\Gamma/S|` core classes and is finitely normally generated.
   Hence `Gamma` has Max-n, every proper quotient is finitely presented and
   Kazhdan with bi-index at most `r`, and `Gamma/M` is a finitely presented
   simple Kazhdan group containing `G`. By
   `ck-finite-bi-index-hole-is-kazhdan-boone-higman` the free-core reading
   of this hole is **equivalent** to `kazhdan-boone-higman-conjecture`. The
   reading without (T) is Boone--Higman itself. Every reading implies the
   conclusion of `ck-envelope-has-a-finitely-normally-generated-maximal-kernel`
   for the envelope it produces. The twisted Brin--Thompson step is idle.
   *Classes killed*, at clause 2 of the lemma:
   - envelopes with an infinite central subgroup, for example a marked cover
     with an infinite central covering kernel;
   - covers of `EL_n(U)` for a ring `U` without ACC on proper two-sided
     ideals;
   - fp envelopes with a non-finitely-presented proper quotient.
   In Attempt 6 the covering kernel of a finite bi-index cover must be
   finitely normally generated, so the elementary image would be finitely
   presented. Open side question: ACC for the two-sided ideals of the
   universal sandwich ring. See
   `research/artifacts/finite-bi-index-normal-lattice-collapse-2026-09-17.md`.
8. **Price the Kazhdan surcharge along every recorded host route
   (2026-09-17, swarm-0917 w5).** *Result: along the linear routes the
   surcharge is zero. The free-core hole costs exactly one Boone--Higman ring
   premise.* All three ring-host routes to Boone--Higman produce hosts that
   are quotients of, or isomorphic to, `EL_n(R)` with `n >= 3` and `R`
   finitely generated:
   - `(B ⊗ L)^x ≅ E_3(B ⊗ L)`;
   - `E_n(B ⊗ L)`;
   - `PEL_4(L)`.
   Ershov--Jaikin-Zapirain and quotient permanence of (T) make these hosts
   Kazhdan (established: `ring-elementary-bh-hosts-are-kazhdan`). This gives
   the new routes `kazhdan-boone-higman-via-central-simple-leavitt-tensor-host`,
   `kazhdan-boone-higman-via-elementary-leavitt-hosts` and
   `kazhdan-boone-higman-via-projective-ring-host`. Each has the same open
   premise as its Boone--Higman counterpart. Composed with
   `ck-finite-bi-index-hole-via-kazhdan-boone-higman`, each is a route to the
   free-core reading of this hole.
   *Where the surcharge is real:* only on Thompson-like hosts (twisted
   Brin--Thompson, Rover--Nekrashevych, shell or full groups), which are
   expected to be a-T-menable. So no dynamical host route to Boone--Higman
   can be upgraded to this hole without new (T) input.
   *Contrapositive:* a refutation of this hole in its free-core reading
   refutes all three ring premises at once:
   - `decidable-group-algebras-have-fp-central-simple-hosts`;
   - `simple-inputs-have-fp-elementary-leavitt-tensor-hosts`;
   - `decidable-group-ring-has-fp-projective-simple-host`.
   *Untouched:* the fixed-core reading, where the core is the
   Boone--Higman--Thompson envelope. A ring host `T` gives `S = Gamma = T`,
   not the prescribed core. The hole stays OPEN. See
   `research/artifacts/ring-hosts-are-kazhdan-2026-09-17.md`.
9. **Any universal-sandwich envelope, any marking, any core.** *Killed as a
   class* by [[sandwich-ring-envelopes-have-infinite-core-bi-index]] (c-ckbi,
   2026-09-17), adopting bus spark 0e1cd89b. The invariant is the normal
   height. By [[normally-generating-core-bi-index-bounds-normal-height]], if
   `N ∩ S = 1` for all proper normal `N` and `|S \ Gamma / S| = r`, then
   `N |-> NS` is strictly monotone along chains, by the modular law, into the
   intermediate subgroups. So every chain of proper normal subgroups has at
   most `r` members. Every envelope mapping onto `EL_n(R)` with `R` of infinite
   ideal length therefore has infinite core bi-index. `U` qualifies because
   `U/lU != 0` for every prime `l`, which gives the congruence chain
   `C(l_1 ... l_k U)`. This covers every marked cover from
   [[ck-steinberg-marked-cover]] and `EL_4(U)` itself, whatever core is used.
   It also corrects Attempt 2: finite bi-index does imply finite normal
   height, finitely normally generated proper normals, a finitely presented
   simple Kazhdan quotient containing `S`, and finite center. Survivors must
   avoid all ring quotients of infinite ideal length. Not covered are
   quotients where the covering kernel `K` has `KN = Gamma`, and the original
   CK subring `L`.
