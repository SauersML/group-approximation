# Archived survey: conditional routes to non-hyperlinearity

This date-sensitive literature synthesis is useful context, not a standalone
Cairn proposition.  It is preserved as an artifact instead of being assigned
an artificial dependency-free proof route.

**Established by citation (survey).**  As of 2026-08, no non-hyperlinear
group is known (IAS lecture, "why are there still no known non-hyperlinear
groups").  Every published route reduces existence to an open stability
question of the same shape:

- **Dogon, arXiv:2211.10492.**  For a countable property (T) group `Gamma`
  with a suitable central extension by a countable abelian `A`, if `Gamma`
  is flexibly HS-stable -- or merely *weakly ucp-stable* (Thm 1.6, weaker,
  after Ioana--Spaas--Wiersma) -- then a non-hyperlinear group exists.
  Applied to `Sp_(2g)(Z)` (which has (T) and `pi_1(Sp_(2g)(R)) = Z`), to
  generic Gromov-density-`(1/3,1/2)` random groups, and to all infinitely
  presented (T) groups.  HS analogue of Bowen--Burton (P-stability of
  `PSL_n(Z)` and non-sofic groups).
- **Dogon--Vigdorovich, arXiv:2506.20843.**  If `SL_2(Z[1/p])` (property
  (T;FD), not (T)) is flexibly HS-stable, then it has a non-hyperlinear
  finite central extension; reduced to the Iwahori local-global question.
- **This graph's relative-commutant route.**
  `relative-commutant-collapse-for-sl2-pair` /
  `sl3-pair-relative-commutant-route`: the co-dense Kazhdan HNN extension
  is non-hyperlinear once `pi(C)' cap M = pi(A)' cap M` in the matrix
  ultraproduct -- a statement that needs neither central extensions nor the
  `pi_1` condition, unifying with Alekseev--Thom OP 6.2 and the Kun--Thom
  lane, for the explicit commensurated pairs `SL_2(Z) <= SL_2(Z[1/2])` and
  `SL_3(Z) <= SL_3(Z[1/2])`.

**The shared open core.**  Flexible HS-stability (or weak ucp-stability) of
an infinite (T)/(T;FD) group is not known for ANY such group; an infinite
hyperlinear (T) group is not even locally HS-stable, so these questions ask
for stability against the (T) obstruction, which is exactly why they are
hard.  The character/trace side is settled everywhere by rigidity (limits
of finite-dimensional traces), and for `SL_2(Z[1/2])` even the abelian
solenoid dynamics is settled (single automorphism, dense periodic
measures); the irreducibly open part is the correction of NON-hyperfinite
asymptotic representations, equivalently the relative-commutant collapse
`(RCC)`.

**Progress recorded in this graph (2026-08-21).**  The NEAR sector of the
Dogon--Vigdorovich question is now a theorem
(`iwahori-uniform-infinitesimal-rigidity` + `iwahori-newton-closes-near-sector`):
representations within a fixed tube of the compatible locus obey
`D(pi) <= C def(pi)`.  Only the far sector (`iwahori-outlier-repair`, an
operator/relative-commutant statement) remains, and it is the same `(RCC)`.

**Breakout additions (2026-08-21).**  The projective trace-square route
`projective-trace-square-transfer-for-sl3-pair` weakens RCC at its conclusion:
the HNN proof only needs `[t,h]` asymptotically scalar, because modulus-one
trace already contradicts the regular character.  Independently,
`algebraic-compact-action-envelope-for-non-ce-relation` avoids the shared
stability core altogether: a compact-abelian algebraic crossed-product
envelope of the known non-CE relation factor is automatically a canonical
semidirect-product group factor by Pontryagin duality.  These are therefore
not additional instances of the published flexible-stability condition
surveyed above.

## Attempts

- **Weak ucp-stability and LLP (Dogon 2211.10492, Section 1).**  `LLP =>
  weakly ucp-stable` (Kirchberg LLP groups are weakly ucp-stable, via
  Ioana--Spaas--Wiersma + Choi--Effros); amenable groups are weakly
  ucp-stable.  Prop 1.11: a hyperlinear (T) group that is weakly ucp-stable
  is residually finite (Becker--Lubotzky extended).  Consequences for this
  program: (i) `SL_2(Z[1/2])` is RF with (T;FD), so Prop 1.11 poses NO
  obstruction to its weak ucp-stability; (ii) BUT no infinite (T) group
  (e.g. `Sp_(2g)(Z)`) is KNOWN to have LLP or to be weakly ucp-stable -- if
  one were, the goal would already be solved -- so LLP is not a shortcut,
  it is the same open difficulty in different words; (iii) whether the
  relative-commutant / HNN route weakens from flexible HS-stability to weak
  ucp-stability is worth checking, but Dogon's Thm 1.6 weak-ucp version is
  proved only for the (T) central-extension route via ISW20 cohomological
  ucp machinery, not by the elementary projection argument, so a weak-ucp
  HNN theorem would need that machinery too.
- **Where to spend effort.**  Since all routes share the stability/ucp
  core, effort concentrates on `(RCC)` for a commensurated arithmetic pair
  (Popa deformation/rigidity, proper proximality) or on a direct
  construction of a flexibly stable (T;FD) group, not on multiplying
  conditional routes.

## The published attack toolkit (2026-08-21, two independent agent surveys)

No published group is a ready host (`no-published-unconditional-codense-stable-host`),
so the goal needs a new flexible-stability theorem for one congruence-rigid
group.  The candidate hosts, all with the SAME single open hypothesis and
everything else published: `SL_2(Z[1/p])` (DV question), `SL_2(Z[1/pq])`,
`SL_3(Z[1/p]) supset SL_3(Z)`, `Sp_4(Z)`, and the plain lattice `SL_n(Z)`
(`n >= 3`) with a thin co-dense subgroup (`sln-z-thin-codense-tau-pair`,
NEW -- covered by neither Dogon nor Dogon--Vigdorovich).  The sharpest
published tools toward proving such a stability theorem / closing the far
sector:

- **de la Salle, arXiv:2204.07084.**  Thm 1.4: every FINITE group is
  flexibly stable with a LINEAR dimension-free modulus (169 eps), defect
  averaged over the group, target ANY tracial von Neumann algebra (so it
  runs inside the matrix ultraproduct).  Lemma 1.7: the correction can be
  made compatible with a subgroup on which the map is multiplicative (the
  tool for the joint root/involution exactification of the (SR2)
  coordinates).  Cor 1.8: almost-commuting finite-group homomorphisms are
  near exactly-commuting ones.  Consequence: the far sector reduces, with
  published constants, to LENGTH CONTROL for the congruence relator family
  against Taback's exponential Dehn function (arXiv:math/0302191).
- **Dogon--Vidick, arXiv:2607.20135 (Jul 2026).**  Polynomial HS-stability
  of the lamplighter via an EFFECTIVE tower decomposition for approximately
  invariant measures with periodic points -- the approximate-measure-
  rigidity technology for exactly the Schmidt/DCC class of `x4` on the
  2-adic solenoid.  Best import: make the `BS(1,4)` skeleton polynomial-
  effective, setting the scale `M` for the length-control estimate.
- **NOT available (checked):** quantitative character rigidity for
  `SL_2(Z[1/p])` (Peterson--Thom's quantitative section needs Ozawa T_Q,
  `m >= 3`, Haagerup targets); Frobenius-norm lattice (in)stability (BLSW,
  Fournier-Facio) is the wrong norm (a normalized-HS microstate has
  Frobenius defect `sqrt(d) t -> infinity`); effective `xa xb` rigidity
  (BLMV) needs exact invariance under two commuting maps.

The single highest-leverage write-up is the `SL_n(Z)` host route: it converts
the program's only open hypothesis into the flexible HS-stability of the
most-studied lattice, on which any future progress (either direction)
resolves the conditional, and it has a permutation twin (flexible
P-stability of `SL_n(Z)` implies non-sofic, HS analogue of Bowen--Burton).
