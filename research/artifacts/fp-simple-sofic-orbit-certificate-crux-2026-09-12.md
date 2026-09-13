# The amenable orbit certificate for finitely presented simple sofic groups: barrier map and the finite presentation crux

Lane `ex-fp-simple-sofic`, 2026-09-12. This backs the Attempts of
`fp-simple-group-in-amenable-orbit-full-group`,
`labbe-shift-derived-full-group-is-finitely-presented` and
`penrose-derived-full-group-is-finitely-presented`. Nothing here settles
`hyperlinear-fp-infinite-simple-group`. Statements marked **(proved on main)** have
routes; those marked **(remark)** are not established.

## 1. Where the root stands

A group realized nontrivially by bounded piecewise translations of an essentially
free measure-preserving amenable action is sofic
(`amenable-orbit-full-group-subgroups-are-sofic`, proved on main). The root therefore
follows from finite presentation of any one of:

- `D([[Z^2 ~ Omega_U]])`, Labbé's 19-tile Wang shift
  (`labbe-shift-derived-full-group-is-finitely-presented`);
- `D(𝒫)`, the Penrose tiling group of Chornyi--Juschenko--Nekrashevych, which is the
  full group of a free translation action of `Z^2 ⊕ Z/5` on a cut torus
  (`penrose-derived-full-group-is-finitely-presented`).

Neither route needs amenability. That is the point: amenability of the Penrose group is
open (ChJN line 95), and amenability of Labbé's group is open
(`labbe-shift-derived-full-group-is-amenable`).

## 2. Barrier map (proved on main)

A finitely presented infinite simple group `S` with a nontrivial realization
`rho : S -> W(Lambda ~ X)` cannot:

| Class | Mechanism | Node |
|---|---|---|
| contain Thompson's `V` | the fixed-point character is trivial plus regular (Dudko--Medynets), so `rho` is free off its fixed set, so `V` is amenable | `stabilizer-rigid-groups-avoid-amenable-orbit-full-groups` |
| have property (T) | Følner indicators are almost invariant, so orbits are finite a.e. | `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf` |
| be non-amenable with only trivial ergodic IRS | free off its fixed points, then amenable | `irs-rigid-nonamenable-groups-avoid-amenable-orbit-full-groups` |
| live in the full group of a subshift with periodic approximations | generators fix finite orbits of the SFT neighbourhood | `periodic-approximable-subshifts-host-no-fp-simple-group` |

Families excluded:
- by the first row: Higman--Thompson, Brin--Thompson, Röver--Nekrashevych groups, Matui's SFT
  full groups and Leavitt unit groups, in so far as they contain `V`;
- by the second row: Kazhdan Kac--Moody lattices and Titz Mite--Witzel kernels;
- by the third row: IRS-rigid Kac--Moody lattices;
- by the fourth row: all minimal `Z`-subshift groups.

Not excluded: lattices in products of trees (Haagerup, no recorded IRS
classification), Thompson's `T`, and Lodha's circle groups (no character classification
recorded).

**Structural necessary condition.** A non-amenable witness has a nontrivial ergodic IRS
with amenable orbital Schreier graphs, and polynomial growth when `Lambda = Z^d`. In the
graph and in the sources read by this lane, we found no finitely presented infinite simple
group with a nontrivial IRS; this is a bounded check, not a literature verification. A
finite presentation of either candidate would give one.

## 3. Why the known finite-presentation methods do not reach the candidates

Every finite-presentation theorem for full groups found in the sources rides on
compression:
- Matui's type `F_∞` for one-sided SFTs, via Brown's criterion on expansions;
- Li's Garside-category method for products of one-sided SFTs;
- Nekrashevych's expanding maps and contracting groupoids;
- Belk--Bleak--Matucci--Zaremsky's hyperbolic groupoids.

In each, a clopen set holds two disjoint copies of itself. An invariant probability
measure of full support forbids this (`amenable-full-group-forces-invariant-measure`).
Nekrashevych arXiv:2509.05524 proves finite presentation (line 3359) only after adding
the shift to a contracting shift-invariant groupoid, which destroys the invariant
measure, and remarks (line 3362): "Full groups of shift-invariant groupoids, on the
other hand, are rarely finitely presented."

## 4. The marked-group picture

**Isolation lemma** (on main, in `minimal-free-sft-full-group-pattern-models-are-exact`).
A finitely generated infinite simple group is finitely presented iff it is isolated among
marked groups.

**Spatial approximants collapse** (on main). Rule groups on validly coloured `Z^d`-sets
reproduce the marked group exactly, so no approximant is a Z^d-set with a valid colouring.

**Remark (non-SFT systems).**
- *Setting.* Let `X` be a free minimal `Z^d`-subshift that is not of finite type, `S` a
  finite generating set of `D([[X]])` given by rules of radius `R`, and `X_N` the SFT
  whose allowed `N`-patterns are `L_N(X)`.
- *Rule groups on the approximations.* For `N` large the rules of `S` act on `X_N` by
  bijections. Let `G_N` be the group they generate.
- *Convergence.* A word of length `l` evaluated on `X_N`, with `N >= lR + R`, reads only
  patterns in `L(X)`. So it is trivial on `X_N` iff trivial on `X`. Hence
  `G_N -> D([[X]])` in the space of marked groups.
- *Consequence.* If `D([[X]])` is finitely presented, the restriction `G_N -> D([[X]])`
  is an isomorphism for all large `N`. A proof that some word is trivial on `X` but not
  on `X_N`, for infinitely many `N`, would prove "finite presentation forces finite
  type" for `Z^d`.
- *Why the obvious commutator attack stalls.* Any forbidden pattern of `X_N` has diameter
  above `N`. So every element detecting it has rule radius above `N`, and its action on
  `X_N` near the pattern is not controlled by `X`.
- *Scope.* For an SFT `X`, `X_N = X` and the remark is vacuous. That is why Labbé's and
  the Penrose systems survive.

## 5. Homology (remark, partly unverified)

- **Li's exact sequence** (Li, Corollary 6.14, quoted as `th:Li` in arXiv:2509.05524)
  holds for minimal ample groupoids with comparison:
  `H_2(A(G)) -> H_2(G) -> H_0(G; Z/2) -> H_1(F(G)) -> H_1(G) -> 0`.
  - For `G = Z^2 ~ Omega_U`, `H_2(G) = C(Omega_U, Z)^(Z^2) = Z`, so the sequence cannot
    show that `H_2(A(G))` is infinitely generated.
- **Unverified heuristic.** If Li's full infinite-loop-space theorem identifies `H_2(A(G))`
  with `pi_2` of the groupoid's algebraic K-theory spectrum, then the
  Atiyah--Hirzebruch terms are `H_2(G)`, `H_1(G; Z/2)` and `H_0(G; Z/2)`. For
  substitution tilings these are finitely generated (Anderson--Putnam cohomology), so
  homology gives no obstruction for Labbé or Penrose. For aperiodic SFTs with infinitely
  generated Čech cohomology it might. Neither step was checked.

## 6. The scale-climbing mechanism, and what finite presentation would need

**Finite generation** (ChJN arXiv:1602.04255, Section "A finite generating set").
- *Generators.* `D([[Z^d]])` is generated by the coordinate 3-cycles `T_(pi, (0, e_i, -e_i))`
  on cylinders of patches `pi` with support `B(R)`.
- *Scale climbing.* The group generated by `𝒯_R` contains `𝒯_(R+1)` once `R >= R_1 + 2`,
  where `R_1` comes from Lemma `lem:incompatible` (patches separating each point from its
  nearby translates). Relations among coarse 3-cycles thus produce all finer ones.

**What a finite presentation needs.** The same climbing for relations. Fine 3-cycles with
disjoint cylinders must commute, and the alternating-group relations must hold on fine
multisections; all of this must follow from finitely many relations at bounded radius.
- Conjugation preserves the measure of supports, so fine relations are never conjugates
  of coarse ones.
- They must come from products and commutator identities.
- In the compressible case, conjugation by compressions supplies them for free.

**What non-finite presentation needs.** A non-spatial family of marked groups converging
to the candidate (Section 4). Equivalently, a sequence of relations at growing scale that
does not follow from relations at bounded scale. An infinitely generated `H_2` would give
one.

## 7. Suggested sub-questions for a family of lanes

1. **Relation climbing.** For Labbé's shift, find a finite set of relators among the
   `𝒯_R` (with `R = R_1 + 2`) that implies commutation of all disjoint fine coordinate
   3-cycles. A proof would be a landmark. A computational probe on MSI could test the
   relators of radius at most `r` against short consequences, using exact rule groups on
   finite patches as the calculator.
2. **Obstruction.** Construct for each `N` a group with the same generators satisfying
   every relator of length at most `N`, in which some fine commutation fails. Its action
   cannot be a valid Z^2-colouring, by Section 4.
3. **IRS side.** Decide whether some finitely presented infinite simple group has a
   nontrivial ergodic IRS. If every such group is IRS-rigid, then `D(𝒫)` and
   `D([[Omega_U]])` are not finitely presented, since both have nontrivial IRSs, and the
   certificate only reaches amenable groups.
4. **Finite type for Penrose.** Check whether the `Z^2 ⊕ Z/5` coding of the Penrose hull is
   an SFT. If it is not, Section 4's remark becomes the relevant attack.
5. **Lattices in products of trees.** Find or prove an IRS or character classification for
   Burger--Mozes lattices. That would decide whether they can live in the certificate.
