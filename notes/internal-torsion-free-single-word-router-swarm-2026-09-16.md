# internal-torsion-free-single-word-router: swarm session 2026-09-16

Agent: swarm-internal-torsion-free-single-w.  Lock taken on
`internal-torsion-free-single-word-router`, ttl 180m.

## 1. Setup

The target hole (root, OPEN) asks for an in-repository construction.  Its
input is a finitely presented, torsion-free, acylindrically hyperbolic `E`,
an element `d != 1`, and a finite protected set `P` containing `d`.  Its
output is `q : E ->> Q` with:

* `Q` nontrivial, two-generated, finitely presented, torsion-free and
  acylindrically hyperbolic;
* `q` injective on `P`;
* `normalClosure_Q(q(d)) = Q`, which is (TFR3).

No cited small-cancellation theorem may be a premise.  A formalized
normal-form/Greendlinger argument is acceptable.

Consumers:

* `property-t-free-torsion-free-via-intrinsic-seed`, which needs
  `torsion-free-fp-ah-mf-radical-seed`;
* `property-t-free-torsion-free-via-bs-radical-tether`, which routes
  `(A, d)` with `A = <E, t | d t d^-1 = t^2>` and `d` in `Rad_MF(A)`.

Both finish through `torsion-free-mf-radical-routing-saturation`.

Paper-level substitute: `two-generated-single-element-hull-router`.  It uses
Hull's Theorem 7.1 twice and gives outputs that are only acylindrically
hyperbolic (`hull-quotients-are-not-word-hyperbolic`).

Elementary regimes recorded in the graph:

* free-group `GreendlingerGate` (`SmallCancellationRouter.lean`,
  `greendlinger-free-product-lemma`), used by `free-group-avatar-router` in
  the Kazhdan lane;
* the free-product syllable version, whose factor embedding is already
  obstructed for the partner datum by
  `free-product-router-factor-embedding-obstruction`.

A full internal proof of the target is a formalization of relative small
cancellation over acylindrically hyperbolic groups.  That is far beyond one
session.  The session aimed instead at determining which elementary
architectures could possibly work.

## 2. What was proven

The full proofs are in
`research/artifacts/torsion-free-router-nonhyperbolic-output-2026-09-16.md`.

**New claim `torsion-free-router-forces-nonhyperbolic-output`**, with route
`torsion-free-router-forces-nonhyperbolic-output-proof`.

* **Embedding lemma (internal, complete).**  A homomorphism
  `f : BS(1,m) -> H` (`|m| >= 2`) with `f(t)` of infinite order is injective.
  The proof uses the model `Z[1/|m|] x| Z`: a kernel element `(r, k)` yields
  the commutator `(m^k - 1, 0)` in the kernel, and nonzero kernel elements of
  `Z[1/|m|]` conjugate to a power of `t`.  The model isomorphism is proved by
  a normal form `a^-j t^n a^k`.
* **Theorem A.**  Suppose `x d x^-1 = d^m` in `E` with `|m| >= 2`.  Then
  every valid output contains `BS(1,m) = <q(x), q(d)>`.  Hence it is not
  word-hyperbolic (Fact H, imported inline) and not a classical `C'(1/6)`
  group without proper powers.  If the output is a free-product quotient with
  factor embedding and `q` the factor map, then `E ≅ Q` and
  `normalClosure_E(d) = E`.
* **Test instance.**  `E_1 = <a, t, s | a t a^-1 = t^2>`, `d = t`,
  `P = {t}`:
  * finitely presented;
  * torsion-free, as an HNN extension of `F(t, s)` (`hnn-torsion-theorem`);
  * acylindrically hyperbolic, by the Bass--Serre tree of `BS(1,2) * Z` with
    trivial edge stabilizers, explicit acylindricity constants, the
    loxodromic `ts`, the free subgroup `<a, s>` and Osin's trichotomy;
  * `E_1/<<t>> = F_2`.

  So on this legitimate input both classical Greendlinger regimes fail, as
  does any hyperbolic-output architecture.
* **Theorem A'.**  If `d` is in `Rad_MF(E)`, then any valid output has full
  MF radical, so it is not MF, not residually finite, and not classical
  `C'(1/6)`.  A hyperbolic output would witness `non-mf-hyperbolic-group`.

**New claim `avatar-router-has-no-nontrivial-kazhdan-instance`**, with route
`-proof`, which invalidates `free-group-avatar-router`.

* **Theorem B.**  Every homomorphism from a Kazhdan group to a finite
  classical `C'(1/6)` group without proper powers is trivial.  The chain is:
  * Wise cubulation (proper, cocompact, so finite-dimensional);
  * the Niblo--Reeves fixed point;
  * a finite cube stabilizer;
  * torsion-freeness.
* **Consequence.**  The avatar route's clause 3 makes the Kazhdan partner
  surject onto the `C'(1/6)` avatar quotient, so the quotient is trivial and
  the protected element dies.  The route has no instance.
  `bespoke-routing-lemma` keeps `small-cancellation-router-spec-proof`.

**Computation.**  The script
`experiments/torsion-free-router-nonhyperbolic-output-2026-09-16/bs_model_check.py`
(output in `bs_model_check.out`) verifies the Section 1 identities with exact
rationals for `m = 2, 3, -2, -3`.

Neither result refutes the target.  For `(E_1, t, {t})` the paper-level Hull
router gives valid, non-hyperbolic outputs.

## 3. Approaches tried and where each dies

1. **Partner-free free-group avatar router.**  Present
   `Q = F(y_1, y_2)/<<R>>` with avatar words for the generators of `E`,
   tying relators putting `y_j` in `<<q(d)>>`, and `GreendlingerGate` for
   survival and torsion-freeness.
   *Dies at Theorem A(c).*  On `(E_1, t, {t})` every valid output contains
   `BS(1,2)`, while the output of this architecture is hyperbolic.  The
   conclusion does not depend on how the piece ledger is chosen.  It dies
   again at Theorem A'(d) for every MF-radical input.
2. **Classical free-product syllable `C'(1/6)` over `E * H`, with `q` the
   factor map.**
   *Dies at factor embedding* (Theorem A(d)).  It would force `E ≅ Q` and
   `normalClosure_E(d) = E`, which is false for `E_1`.  This is the
   partner-free analogue of `free-product-router-factor-embedding-obstruction`.
3. **Gadget absorption.**  Take `K = <x, w, y | x w x^-1 = w^2, w y w^-1 = y^2>`.
   Then `K/<<x>> = 1`: killing `x` gives `w = w^2`, so `w = 1`, then
   `y = y^2`, so `y = 1`.  So `x` normally generates `K`.  Amalgamate `d`
   with `x` to put the whole gadget inside `<<d>>`.
   *Dies* because pulling the generators of `E` into `<<d>>` requires relators
   identifying them with gadget elements.  That is the router problem again.
   Torsion-freeness, survival of `P`, two-generation and acylindrical
   hyperbolicity of the result all need a small-cancellation theorem; the
   gadget does not supply one.  Recorded as an idea only.
4. **Formalize Hull's route.**  Only a paper-level account is available:
   two applications of Hull's Theorem 7.1, as in
   `two-generated-single-element-hull-router`.  This requires hyperbolically
   embedded subgroups, relative isoperimetric functions and Hull's
   small-cancellation lemmas.  *Out of scope for a session.*  Theorem A shows
   this, or some other theory that tolerates non-hyperbolic subgroups, is
   unavoidable.
5. **Kazhdan-lane cross-check.**  While checking which architecture the
   graph calls "working" (`free-product-router-factor-embedding-obstruction`
   points to the avatar presentation), I found that the avatar route is
   uninstantiable (Theorem B) and invalidated it.
   `small-cancellation-router-spec-proof`, the other route to
   `bespoke-routing-lemma`, freezes an interface and machine-checks
   sufficiency.  I did not audit it.
6. **Attempts to refute the target.**  None succeeded.  For `E_1`, the
   paper-level Hull outputs exist.  I see no elementary invariant that every
   torsion-free, acylindrically hyperbolic, finitely presented input
   transmits to a two-generated normally-generated quotient and that
   obstructs existence.  Theorem A' only shows that outputs for MF-radical
   inputs are not residually finite, which is exactly what the consumers
   want.

## 4. Literature consulted

**External gate.**  The literature gate was attempted and the tooling
failed:

* the WebSearch budget was exhausted in this session;
* `export.arxiv.org` returned HTTP 429;
* PDF text extraction was unavailable (no `pdftotext`, and `pypdf` crashed).

So **no 2024--2026 sweep was performed**, and no novelty claim is made.
Sources actually consulted:

* D. Hull, *Small cancellation in acylindrically hyperbolic groups*,
  arXiv:1308.4345 (v1 2013-08-20, v2 2015-05-21).  Consulted through the
  abstract and the graph's quotations in
  `notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md`.
* D. Osin, *Acylindrically hyperbolic groups*, arXiv:1304.1246 (v1
  2013-04-04, revised 2015-04-16), Theorem 1.1 (trichotomy).  Consulted
  through Hull's Theorem 2.3 as quoted in the same notes file, §6.8.
* Wikipedia, *Hyperbolic group*, fetched 2026-09-16.  Verbatim: "The
  Baumslag–Solitar groups B(m,n) and any group that contains a subgroup
  isomorphic to some B(m,n) fail to be hyperbolic".  The neighbouring `Z^2`
  sentence cites Bridson--Haefliger and Ghys--de la Harpe.
* Wikipedia, *Baumslag–Solitar group*, fetched 2026-09-16.  Nothing relevant
  beyond the definition.

**Through established repository citation nodes** (quotations already in
the graph; not re-fetched):

* Gruber, arXiv:1210.0178;
* Wise, *Cubulating small cancellation groups*, GAFA 14 (2004);
* Agol, *The virtual Haken conjecture*, Doc. Math. 18 (2013);
* Haglund--Wise, *Special cube complexes*, GAFA 17 (2008);
* Niblo--Reeves, *Groups acting on CAT(0) cube complexes*, G&T 1 (1997),
  Theorem B;
* Martin--Steenbock, arXiv:1409.3678 (via
  `cprime-one-sixth-presentations-are-hyperlinear-proof`).

**Classical, not re-read:**

* Serre, *Trees* (Bass--Serre tree of a free product; axis dichotomy);
* Bridson--Haefliger (CAT(0) convexity; undistorted cyclic subgroups of
  hyperbolic groups);
* Ghys--de la Harpe, Ch. 8;
* Gromov, *Hyperbolic groups* (1987).

## 5. Suggested next moves

* **Retarget the formalization program.**  The internal router has to be a
  small-cancellation theory relative to a non-hyperbolic ambient group,
  either Hull/Dahmani--Guirardel--Osin style, or free-product style in which
  `q` is not the factor map.  Recording this would help anyone planning the
  Lean workstream: the "W3 finite word combinatorics" plan attached to the
  avatar route cannot be adapted to the torsion-free lane.
* **Internal testbed.**  Construct, by hand and with complete proofs, one
  valid output for `(E_1, t, {t})`.  It would be a two-generated, finitely
  presented, torsion-free, acylindrically hyperbolic group normally generated
  by an element conjugate to its own square.  One idea is to look among
  two-generator presentations `<t, u | u t u^-1 = t^2, r>` with a second
  relator `r` making `u` lie in `<<t>>`, where torsion-freeness is provable
  by an HNN or amalgam decomposition rather than by small cancellation.  No
  candidate was checked this session.
* **Weakest point to attack first:** Fact H is imported inline rather than
  through a citation node.  A citation node for "hyperbolic groups contain
  no `BS(1,m)`, `|m| >= 2`", quoting Bridson--Haefliger III.Gamma, would
  remove it.
