---
rg: 2
id: rips-segev-groups-satisfy-kaplansky-zero-divisor
kind: claim
title: The Rips--Segev torsion-free groups without unique products satisfy Kaplansky's zero-divisor conjecture
distinct_from:
  kaplansky-zero-divisor-conjecture: that is the conjecture for every torsion-free group; this is Steenbock's question for the Rips--Segev groups, the first torsion-free groups without unique products.
  cyclic-centralizer-groups-have-no-support-three-zero-divisors: that is the open support-three case over torsion-free hosts with cyclic centralizers, a class containing these groups; this asks for every support size, for this family only.
  marked-limits-of-special-groups-have-domain-group-rings: that is a sufficient criterion for the domain property; this is the instance of the conjecture that the criterion is aimed at.
---

**OPEN.** For every field `k` and every Rips--Segev torsion-free group `G`
without the unique product property, `k[G]` has no zero divisors.

**Source of the question.** Steenbock, arXiv:1307.0981, introduction,
verbatim: "Do Rips-Segev groups satisfy Kaplansky's zero-divisor conjecture?".
It is repeated as a problem in Arzhantseva--Steenbock, arXiv:1407.2441: "Do the
Rips-Segev groups without the unique product property satisfy the Kaplansky
zero-divisor conjecture?". Martin--Steenbock, arXiv:1409.3678, "Open problem":
"It is unknown whether these so called generalised Rips-Segev groups satisfy
the Kaplansky zero-divisor conjecture."

**Related nodes on main.**
- The support-three case for torsion-free hosts with cyclic centralizers, which
  include these torsion-free hyperbolic groups, is the OPEN
  `cyclic-centralizer-groups-have-no-support-three-zero-divisors`. Main has
  local constraints there (short cycles, quasimorphism bounds), not a proof.
- `zero-divisor-support-subgroup-host-constraints` applies.

## Attempts

1. **Cubulation (route `rips-segev-zero-divisor-via-cubulation`).** Needs the
   OPEN `rips-segev-groups-are-cocompactly-cubulated`. Martin--Steenbock's
   combination theorem covers only the classical `C'(1/6)` condition over free
   products. Steenbock (arXiv:1307.0981, introduction) notes that
   Rips--Segev relators "can have long common parts", so the classical theorem
   does not apply as stated. For the Kazhdan generalized examples of
   arXiv:1407.2441 this route is closed: those are infinite property (T)
   groups, hence not CAT(0)-cubical.
2. **Special marked limits (route `rips-segev-zero-divisor-via-special-marked-limits`).**
   Needs the OPEN `rips-segev-groups-are-marked-limits-of-special-groups`. It
   avoids cubulating the group itself. By
   `kazhdan-groups-map-trivially-to-torsion-free-special-groups` it cannot
   reach the Kazhdan generalized examples, so it is only a candidate for the
   original Rips--Segev presentations, which are not known to have property
   (T).
3. **Zero divisor on the encoded witness (killed; `rips-segev-witness-pairs-carry-no-zero-divisors`).**
   The natural candidate supports are Steenbock's non-unique-product pair
   `(A, {1,a,b,ab})`.
   - Over `F_2` they carry no zero-divisor pair in any torsion-free group,
     because `beta = (1+a)(1+b)` is a product of non-zero-divisors.
   - Over any field they carry none once one interior `a`-line index is free
     of the Step 1--2 gluings, assuming exact encoding (EE).
   - A counterexample in `k[G(Gamma)]` must use other supports, saturate every
     clean square with extra coincidences, or break (EE).
4. **Every support inside the witness (killed; `rips-segev-witness-supports-carry-no-zero-divisors`).**
   For small-cancellation graphs (`Gr'_*(1/8)`) with at most one pair of
   distinguished positions at distance one, this includes Steenbock's explicit
   families.
   - (EE) holds: a hanging `v b` is never a vertex of `Gamma`, by a van Kampen
     argument.
   - Every pair with `supp alpha` inside `A` and `supp beta` inside
     `{1,a,b,ab}` has `alpha beta != 0`, over any field.
   - A counterexample must put `alpha` or `beta` outside the witness.
5. **Support reduction to the witness (obstruction; `rips-segev-groups-embed-every-torsion-free-group`).**
   The relators read only `a` and `b`.  So the group over `G_1 * G_2` is the
   amalgam `G_1 *_{<a>} K_Gamma *_{<b>} G_2`, where `K_Gamma` is the core group
   over `<a> * <b>`.
   - Every finitely generated torsion-free `H` embeds in `H *_{<a>} K_Gamma`,
     which is a torsion-free generalized Rips--Segev group without unique
     products.  It is hyperbolic when `H` is.
   - For the generalized groups, with arbitrary torsion-free factors, this
     question is equivalent to the full conjecture.  One finitely presented
     generalized group `U *_{<a>} K_Gamma` tests it.
   - A support-reduction lemma that is uniform in the factors is equivalent to
     the conjecture.  It fails at supports in one coset pair `(gH, Hh)`, whose
     coincidences have faceless van Kampen diagrams.
   - What remains is the core groups `K_Gamma` over `F_2`, which is Steenbock's
     original question.  The domain-factor case follows from that together with
     a domain-combination theorem over cyclic amalgams.
6. **Two-layer elements in the core (partial; `rips-segev-core-large-gap-two-layer-elements-are-regular`, obstruction `rips-segev-port-data-cannot-exclude-balanced-divisors`).**
   Take `beta = u + w b` with `u, w` in `k[<a>]`.  A zero product gives a
   finite configuration of `<a>`-cosets with in- and out-ports.  Walking along
   the extreme ports gives a positive relation `b a^{n_1} ... b a^{n_L} = 1`
   whose exponents all lie on one side of the degree offset
   `deg_+ w - deg_+ u` (or `deg_- w - deg_- u`).
   - A small-cancellation count shows that every positive relation has an
     exponent in the difference set `Delta` of the relator exponents.
   - So `beta` is regular in `k[K_Gamma]`, and in every generalized
     Rips--Segev group, when an offset lies outside `[min Delta, max Delta]`.
   - Port data alone cannot go further.  The graph `Gamma` itself gives a
     port configuration with offsets `(0,0)`, which covers the witness
     `{1,a,b,ab}`.  For Steenbock's graphs, its relator cycles give positive
     relations with all exponents `<= -10` and with all exponents `>= 99900`.
     So the walk step fails for offsets in `[-10, 99900]`.
   - What remains is the balanced and intermediate range.  It needs the
     coefficients themselves, not supports or extreme degrees.  The
     extremal-coset route of this lane is dead there.
