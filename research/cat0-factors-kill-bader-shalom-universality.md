---
rg: 2
id: cat0-factors-kill-bader-shalom-universality
kind: claim
title: A Bader-Shalom lattice with one factor acting with compact point stabilizers on a finite-dimensional complete CAT(0) space contains no infinite finitely generated simple periodic group of subexponential growth, so the decidable golden-mean probe forces both factors of a universal lattice off all finite-dimensional CAT(0) spaces
distinct_from:
  decidable-simple-groups-embed-in-bader-shalom-lattices: that is the open universality statement P1; this is an established obstruction to it, which replaces its conditional Attempt 1(c) (both factors properly cocompact, Dehn function bound unpinned) by one factor with compact point stabilizers and a verbatim fixed point import.
  one-haagerup-factor-kills-bader-shalom-universality: that kills Haagerup factors with a Kazhdan probe and Delorme-Guichardet; this kills finite-dimensional CAT(0) factors, many of them non-Haagerup (Ã2 buildings, Kac-Moody buildings), with a periodic probe of intermediate growth and Izeki-Karlsson.
  two-dim-cat0-product-groups-are-torsion-locally-finite: that needs finite stabilizers in the discrete group on a product of 2-dimensional complexes and trees; this needs compact stabilizers in one non-discrete factor only, in any finite dimension, and uses injectivity of the Bader-Shalom projection for the rest.
  hyperbolic-kac-moody-lattices-are-torsion-locally-finite: that concerns Kac-Moody lattices with hyperbolic Weyl group and every finitely generated torsion subgroup; this concerns lattices in products with one finite-dimensional CAT(0) factor and simple torsion subgroups of subexponential growth.
  golden-mean-periodic-group-lies-in-a-contracting-rsg: that places the golden-mean group in a finitely presented simple group; this uses that placement only for the decidability of the probe.
---

**ESTABLISHED** through `cat0-factors-kill-bader-shalom-universality-proof`.

Let `Γ < G_1 × G_2` satisfy the hypotheses of
`bader-shalom-normal-subgroup-theorem` (`n = 2`). Say that a locally compact group
`G` is a **CAT(0)-compact factor** if it acts by isometries on some complete
CAT(0) space `Y` of finite dimension (in the sense of
`izeki-karlsson-torsion-groups-fix-cat0-points`) so that the stabilizer in `G` of
every point of `Y` is relatively compact in `G`. Continuity of the action is not
needed.

1. Let `Λ ≤ Γ` be a finitely generated torsion group of subexponential growth.
   For every `j` and every isometric action of `G_j` on a finite-dimensional
   complete CAT(0) space, `p_j(Λ)` fixes a point. If `G_j` is a CAT(0)-compact
   factor, then `p_j` embeds `Λ` in a compact subgroup of `G_j`.
2. If some `G_j` is a CAT(0)-compact factor, then `Γ` contains no infinite
   finitely generated simple group that is either periodic of subexponential
   growth or weakly Liouville.
3. Let `P = [F,F]`, the derived subgroup of Nekrashevych's golden-mean group
   (`nekrashevych-golden-mean-fragmentation-group-properties`). Then `P` is an
   infinite finitely generated simple periodic group of subexponential growth
   with solvable word problem. So `P` is an admissible input for P1.
4. Let `H_P` be the simple Kazhdan host of `P` from
   `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`. It has solvable word
   problem and contains `P`. If P1
   (`decidable-simple-groups-embed-in-bader-shalom-lattices`) holds for
   `S = H_P`, then the one lattice `Γ` hosting `H_P` has, on **each** side, a
   factor `G_i` that
   - is not Haagerup (`one-haagerup-factor-kills-bader-shalom-universality`);
   - is not a CAT(0)-compact factor (item 2);
   - contains the non-compact closed subgroups `cl p_i(H_P)` and `cl p_i(P)`,
     where `p_i(P)` fixes a point in every isometric action of `G_i` on a
     finite-dimensional complete CAT(0) space.

   If P1 holds only for `S = P`, the last two points still hold.

**Classes killed.** No factor on either side can be any of the following:
- a closed subgroup of the automorphism group of a locally finite Euclidean or
  hyperbolic building, e.g. Ã2 buildings, Fuchsian buildings, or the Davis
  realizations of Kac-Moody buildings over finite fields;
- a closed subgroup of the automorphism group of a finite-dimensional locally
  finite CAT(0) cube complex or tree;
- any locally compact group acting continuously and properly by isometries on a
  finite-dimensional complete CAT(0) space.

Many of these are not Haagerup, e.g. those with property (T) acting on Ã2
buildings, so they survive `one-haagerup-factor-kills-bader-shalom-universality`
and die here. Attempt 1(c) of the target needed both factors to act properly
cocompactly, plus an unpinned Dehn function bound. Here one factor with compact
point stabilizers suffices, with no cocompactness and no complexity argument.

**Trust.** Items 1-4 rest only on established nodes and the verbatim
Izeki-Karlsson import. The list of classes killed needs two further facts that
are not quoted here:
- point stabilizers in the automorphism group of a locally finite polyhedral
  complex, and in the isometry group of a proper metric space, are compact;
- such a finite-dimensional complex with finitely many shapes has finite
  dimension in the Izeki-Karlsson (Kleiner) sense.

These are the standard Arzelà-Ascoli fact and Kleiner's dimension theorem.

**Invariant and step.** The invariant is the fixed point property of a decidable
simple periodic probe of intermediate growth on finite-dimensional CAT(0)
spaces. Every member of the class dies at one step. The probe fixes a point in
the factor's space, so its image lies in a relatively compact stabilizer. NST
injectivity then gives a nontrivial map of a finitely generated infinite simple
group into a compact group, which minimal almost periodicity forbids.
