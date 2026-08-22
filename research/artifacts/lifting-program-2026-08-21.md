# The lifting program toward a non-hyperlinear group — 2026-08-21

One-session consolidation of the lifting-hypothesis architecture, written
as the routes and fences landed.  All node ids are live in the graph;
literature statements were verified against the cited PDFs on this date.

## The mechanism

Everything runs on one lemma and one invisibility.

- `kazhdan-almost-invariant-corner-near-invariant-projection` — under a
  GENUINE representation of a Kazhdan group, an almost-invariant
  finite-rank corner is `(11/kappa) eta`-close in normalized HS to an
  exactly invariant one of the same normalized rank; lazy averages keep
  operator-norm control, a spectral cut at 1/2 gives the projection.
  Ultraproduct corollary: on representation lifts the relative commutant
  is the ultraproduct of the levelwise commutants
  (`at-op62-holds-for-representation-lifts` — Alekseev--Thom OP 6.2 for
  representation lifts; open content = everywhere-inexact lifts).
- Deligne invisibility (`deligne-triple-cover-fd-central-invisibility`):
  no nonzero finite-dimensional projective representation exists in the
  nontrivial mod-three sectors of `Sp_4(Z)` (and mod-`N`, `N` odd `>= 3`).

Corner lemma + Stinespring turns ucp lifts into genuine representations;
property (T) turns corners exact; invisibility then forbids the result in
twisted sectors and produces congruence representations in untwisted ones.

## The theorems

1. `kazhdan-weak-ucp-stability-is-flexible-stability` — for (T) groups,
   Dogon's weak ucp-stability = flexible HS-stability on hyperlinear
   approximations.  (Dogon's Thm 1.6 hypothesis is not weaker than his
   Thm 1.3's on any group either applies to.)
2. `kazhdan-subgroup-weak-ucp-exactifies-microstates` — subgroup form:
   HNN/wreath microstates become exact on a weakly ucp-stable Kazhdan
   subgroup; confines RCC enemies to the Lambda-exact face; the
   `l^2(A/C)` leak survives (host-side consumption stays impossible).
3. `non-rf-kazhdan-weak-ucp-iff-non-hyperlinear` — for non-RF Kazhdan
   groups: weakly ucp-stable = flexibly stable on hyperlinear
   approximations = NOT hyperlinear.
4. `llp-non-rf-kazhdan-group-is-non-hyperlinear` — LLP of the full
   algebra of a non-RF Kazhdan group makes the group itself the witness
   (sharpens Fournier-Facio--Willett Question 1.9: no `H_2` needed).
5. `twin-lattices-exclude-known-llp-fences` — twin building (and single
   building) lattices contain NO known LLP-failure group: flat-torus
   rigidity kills the cohomological pairs (`Z^2 x| Sigma`, `SL_n(Z)`,
   Sym^2), finite asymptotic dimension + property A kills the
   Osajda-type expander groups; affine types die by ISW's ring fence, so
   the candidacy = compact hyperbolic Kac--Moody types.
6. `twisted-generator-liftability-implies-e3-nonhyperlinear` — the
   Maslov-sector generator-liftability assertion TGL1 is GOAL-HARD:
   equivalent to the alpha-fibre having no matricial model, implies
   non-hyperlinearity of Deligne's `E_3`.  No QWEP backdoor: global
   lifts force WEP (hyperfiniteness), and CE gives QWEP but no local
   lifts (Junge--Pisier).

## The holes (each alone reaches the goal)

- `sl3-z-weakly-ucp-stable` — flexible stability of `SL_3(Z)` on
  separating sequences; consumed through the thin co-dense pair
  (`non-hyperlinear-from-sl3-z-weak-ucp-stability`).
- `non-rf-kazhdan-group-with-llp-full-c-star-algebra` — candidates:
  simple Kazhdan Kac--Moody lattices (forced witnesses:
  `kac-moody-lattice-is-non-hyperlinear-or-llp-failure`; every known
  refutation mechanism provably unavailable; the positive question =
  LLP permanence for nonpositively curved triangles of
  finite-dimensional algebras), and the Deligne lattice (Packer--Raeburn
  fibration; FFW Question 1.12 collapses the candidates).
- `sp2g-z-full-c-star-algebra-has-llp` — alive only at `g = 2`; LP
  already fails (ISW Ex 1.3(i)), so a yes would also separate LLP from
  LP; consumed by `non-hyperlinear-from-sp2g-llp` (Dogon Cor 1.9,
  Deligne witness) and, with
  `sp4-mod3-twisted-fibres-have-llp` (no-f.d.-rep algebras, both tools
  mute, FFW Q1.12's sharpest instance), by
  `non-hyperlinear-from-e3-fibre-llp` — which also certifies the Deligne
  Maslov lane (`deligne-sector-gap-is-exactly-nonhyperlinearity`) and
  carries the property (T) Connes-embedding problem on the same fibres.
- `maslov-sector-tracial-generator-ucp-liftability` (peers') — goal-hard
  by theorem 6; consumed by
  `non-hyperlinear-from-twisted-generator-liftability` and by the peers'
  `brown-ucp-generator-lift-closes-maslov-gap`.

## Dead and decided

- `sp4-metaplectic-class-pointwise-coboundary-limit` — decided negative
  (coboundaries are Tychonoff-compact, hence pointwise closed); the
  constant-class ISW attack is dead for every group; the ISW mechanism
  needs distinct realizable classes accumulating at the trivial class,
  which the Deligne circle cannot supply.
- Five stale refutations stamped (`refuted_by:`), one wrong arXiv id
  fixed after verifying all 245 cited ids against the arXiv API, two
  committed over-cap ids repaired, `tools/graph_audit.py` added (and
  extended by the fleet).

## Sources verified at PDF level this date

Dogon arXiv:2211.10492v3 (Defs 1.2/1.4/1.5, Thm 1.3/1.6, Cor 1.9, Prop
1.11, Section 6); Ioana--Spaas--Wiersma arXiv:2006.01874 (Thm A, Cor B,
Cor E, Ex 1.3, Rmk 1.2); Fournier-Facio--Willett arXiv:2603.18456v2
(Thm 1.1, Qns 1.9/1.10/1.12, Rmk 3.8, Cor 3.17, Prop 3.35/Cor 3.36, Thm
3.39); Caprace--Remy arXiv:math/0607664 (simplicity theorem, simple
Kazhdan group corollary, Howe--Moore caution); Alekseev--Thom
arXiv:2608.05362 (statement level, OP 6.2 via the peers' node).
