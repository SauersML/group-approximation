# STW 99-problems: the gates atlas (2026-08-30)

*The campaign's structural output in one page: the open mass of the 99
concentrates onto seven precisely-stated gates.  Solving a gate
settles everything listed under it, by routes already on main.  The
literature surface of the survey (v2, addenda through April 2026) is
fully imported; everything below is genuinely open mathematics.*

## Solved / refuted outright (on main)

X(1) NO (literal group: factorization property + non-QD trace);
XIX NO (Toms); XX YES (Vaccaro); LV YES (KMS-temperature separation,
this session); LXII YES (Szabo); LXXXIX YES (AGKP); XCVIII∞ YES
(Hirshberg--Phillips).  Closed to a named residue: XV (gate 1),
XVI (gates 2/2'), LVIII (higher K-stability + non-simple),
XLVI (unital unit-positioning).

## Gate 1 — self-Künneth for strongly self-absorbing algebras

*Does every SSA `D` satisfy the Künneth exact sequence for `(D, D)`?*
Settles: XV in full (`ssa-kunneth-forces-solid-k-theory`: K-theory is
then `(Z[J^{-1}],0)` or `(0,0)`, and `K = 0` forces `D ≅ O_2`).
Feeds XIII.  Weaker than II and IV; a failure is itself a UCT-level
counterexample.

## Gate 2 — SSA embeddability (Problem XIV(2)) and 2' — J-smooth QD

*(2) Does every SSA `D ≇ O_2` embed unitally into `(Q ⊗ O_∞)_ω`?
(2') Does every `J`-divisible finite SSA admit matrix models of pure
`J`-number sizes?*  With gate 1, these settle XIII (hence XIV, XV,
XVI in full, VI-modulo-II's-role, LVII's SSA face): XIII factors as
gates 1 + 2 + 2' exactly.  The `O_2`-exclusion in (2) is K-forced
(`embeddable-unit-class-non-torsion`); (2') is canonical by the
extraction lemma (co-`J` model sizes are invariant data).

## Gate 3 — equivariant glueing (CPoU over wild tracial boundaries)

*Construct `G`-invariant complemented partitions of unity over
non-compact / infinite-dimensional extremal trace boundaries.*
Settles: XXXIX (Szabo's conjecture) hence XXXVIII; the trace half of
XLII; LIV via Takai duality (wild-boundary trace-scaling Rokhlin);
advances LI/LIII.  The non-equivariant sibling (selection /
centralization over wild boundaries) is the shared content of XXI,
XXVIII, XXX (Perera--Rordam central divisibility), and the
Matui--Sato finite-boundary theorems are its solved compact cells.

## Gate 4 — comparison vs divisibility

*XXVII(1): strict comparison ⟹ pure; XXVI: Cu-regular ⟹ Z-stable.*
Together they ARE Toms--Winter XVIII
(`stw99-xxvi-xxvii-imply-xviii` + `stw99-xviii-implies-xxvi`);
XXV ⟺ "sr1 + unique trace ⟹ comparison"; XXIII ⟹ XXVII(1).  The
Toms 2026 counterexample cannot touch this gate
(`toms-gamma-counterexample-fails-strict-comparison`), and the
Villadsen side is fenced by the mod-`ell` compact/soft divider
no-gos: the open edge is soft dividers of unbounded rank.

## Gate 5 — X(2): quasidiagonality of the hyperfinite trace

*Is `τ_R` quasidiagonal?*  Equivalent to: every trace with injective
GNS closure is quasidiagonal.  Settles: IX(1)
(`stw99-x2-implies-ix1`), VII-simple
(`stw99-ix1-implies-vii-simple`), XIV(1) (`stw99-x2-implies-xiv1`),
and "every trace on every separable nuclear algebra is QD".  The
X(1) counterexample is provably outside every route here.  All known
non-MF groups and all non-injective-GNS traces are excluded as
witnesses by this session's invisibility theorems; a negative answer
needs a fundamentally new witness inside `R`.

## Gate 6 — LXVI: a non-multiplicity finiteness certificate

*Build a simple unital finite non-stably-finite algebra containing
CAR unitally.*  Fenced: Euler/Hall multiplicity mechanisms, finite
Watatani index, ALL group crossed products of CAR, tensor seeds,
ultraproduct assembly — each provably cannot work.  Equivalent to a
coherent dyadic V-chain on a finite-but-not-stably-finite simple
algebra.

## Gate 7 — Global Glimm (LXXIII)

*No finite-dimensional representations ⟹ full square-zero elements at
every scale.*  Settles: LXXX (`stw99-lxxiii-implies-lxxx`, via
Rordam--Winter's single dimension-drop criterion), the load-bearing
half of LXV, and (with wpi) the (V)-half of LXXII, whose
counterexample profile is narrowed to rotation-type non-cancellation
(TV Question 5.4 sharpened).  Positive corners: dimension zero, sr1,
chain ideal lattices.

## What is NOT behind a gate

The computation problems (XXXVII, XLII, LXXXV, L), the classification
challenges (XXXIV, XLI, LIII, LIV, LVI), the range problems (XLIII,
XLIV, XLV, LXX, LXXI), the dichotomies (XXIX--XXXI, LXXIV via LX),
the Cartan problems (XLVII--XLIX), the K1 problems (LIX--LXI), the
perturbation problem (XCIX), and the group problems (XC--XCIII) each
carry their own fenced frontier on their nodes; several
(LII-Blackadar, LXIII/LXIV, XLIX) have designated kill-shot
experiments recorded.

## Update (pushes 45–59): solved cells landed after the atlas

* Gate 3 (glueing): its entire solved locus is now ONE formal cell,
  `uniform-gamma-on-finite-dim-boundaries` (no comparison
  hypothesis); XXI and XXVIII hold outright there.  The
  noncommutative dynamics cluster XXXVIII/XXXIX/LI/LIII is uniformly
  split: purely infinite halves SOLVED
  (`stw99-*-holds-on-kirchberg-targets` ×4), stably finite halves =
  the gate.
* Gate 4 (comparison/divisibility): new solved cell
  `stw99-xviii-holds-on-rr0-lfnd-locus` (Toms--Winter for real rank
  zero + locally finite nuclear dimension, trace simplex
  unconstrained), by composing the fleet's RR0-divisibility theorem
  with Winter.
* Gate 5 (X(2)): `x2-witnesses-are-never-group-shaped` — witnesses
  cannot be group algebras, amenable crossed products, or carry
  nonamenable δ_e-tuples; the X(1) technology is provably useless
  here.  X(2) → IX(1) → VII-simple is wired
  (`stw99-x2-implies-ix1`, `stw99-ix1-implies-vii-simple`).
* Commutative dynamics: XXXII carries its strongest cells
  (Kerr--Naryshkin elementary amenable; GGKN paradoxical towers);
  XXXIII its founding and strongest cells (Glasner--Weiss Cantor-`Z`;
  Naryshkin polynomial growth).
* Group problems: XC/XCI hold on linear groups
  (`stw99-xci-holds-for-linear-groups`, BKKO + Vigdorovich).
* Other problems: LXXV's known arcs formalized (`Z`-stable ⟹
  Cu-regular; FND ⟹ pure), pinning three open arcs; LXXXVI's known
  half formalized (polynomial growth ⟹ finite dr); LXI's corona cell
  (Gabe--Ruiz); XLVI's stable half
  (`stable-classifiable-algebras-are-z-crossed-products`); LXXXII's
  subhomogeneous cell and LXXXIII's stably-finite-graph work are in
  the peer stw82/stw83 lanes.
* New original theorems since the atlas:
  `cantor-diagonal-algebras-are-two-generated` (settling STW's Cartan
  generation question on the principal Cantor class, scope-corrected),
  the `ssa-kunneth` upgrade closing XV modulo self-Künneth
  (torsion-freeness via degree-one Künneth), and the
  `embeddable-unit-class-non-torsion` lemma forcing the `O_2`
  exclusion in XIV(2).
