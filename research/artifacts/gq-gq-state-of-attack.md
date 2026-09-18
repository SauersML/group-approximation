# State of the attack on GL_n(Q) (gq swarm): snapshot 1

Compiled by lane `gq-writeup` on 2026-09-17 at 22:48 local time, from the lane boards and the gq landings on
origin/main. It contains no claims of its own. Every item is attributed to the lane that recorded it.
Items marked *board* have not landed as Cairn nodes.

**Target.** Root `gl-n-q-embeds-in-fp-simple-group` (OPEN, landed 2598812b3). For n ≥ 2, the countable group
GL_n(Q) embeds in a finitely presented simple group. This is BBMZ arXiv:2306.16356v3, Problem 5.3(5) and p. 7.
Companion target G′ is Problem 2.7: an explicit, natural finitely presented group containing GL_n(Q).

**Landed so far (gq).**
- `2598812b3` (team-lead): the root, and the correction to `rational-linear-groups-satisfy-boone-higman` and
  `char-two-linear-groups-satisfy-boone-higman` (the survey's item 5.3(5) is open for GL_n(Q) itself).
- `75e692ae0` (gq-lit-hosts): `research/artifacts/gq-gq-lit-hosts.md`, sections 1–2. It gives the exact
  hypotheses of the host theorems for germ extensions and type (A) actions.

No gq claim node is ESTABLISHED yet, and no result has been sent to the referees.

## Standing obstructions (root node)

- **O1.** The divisible group (Q,+) lies in GL_n(Q), so no residually finite group contains GL_n(Q). That rules
  out linear, self-similar and tree hosts at every intermediate stage.
- **O2.** For n ≥ 3, SL_3(Z) excludes V and VA as hosts.
- **O3.** Q is not a subgroup of V.

## Reductions recorded in the literature extraction (gq-lit-hosts, artifact §1–§2; lane remarks, not nodes)

- **Type (A) route.** Zaremsky's Corollary B does not need the subgroup to be finitely generated. So G reduces
  to the **A-target**: some finitely presented Γ ⊇ GL_n(Q), or Γ ⊇ SL_{n+1}(Q), acting faithfully on a set with
  finitely generated point stabilizers and finitely many orbits of 2-element subsets. By O1, Γ is not
  residually finite.
- **Germ-extension route.** Over B = V, Belk–Hyde–Matucci's Theorem 2.1 is needed only at level 2. Divisibility
  must then sit in the germ groups or the SingFix groups, because V contains no Q. Simplicity holds only for
  G′. Since SL_m(Q) is perfect and GL_n(Q) ↪ SL_{n+1}(Q), it is enough to put SL_{n+1}(Q) inside a finitely
  presented finite germ extension whose G′ is also finitely presented.
- **Related obstruction.** Fournier-Facio–Kropholler–Lyman–Zaremsky, arXiv:2506.02319, prove non-FP∞
  stabilizers for oligomorphic actions of linear groups. This constrains only the actor, and here the actor
  cannot be linear anyway.

## By family: approaches and first falsifiable steps (from the boards)

### A. Germ extensions and VA-type hosts
- **gq-va-gl2** (obstruction). BS(1,2) ≤ Aff(Q) ≤ GL_2(Q) and BS(1,4) ≤ SL_2(Q). The lane tests whether BS(1,n)
  can sit in VA. Its idea: VA's germ groups look like T̄, subgroups of T̄ with trivial centre embed in T ≤ V, and V
  has no distorted cyclic subgroups. *Needs:* an exact description of VA's germ groups at singular points (it
  is reading arXiv:2407.03149 itself).
- **gq-va-affq** (construction). Build new finite germ extensions whose germ groups at ±∞ are of affine type,
  containing Aff(Q). Its split: gq-va-gl2 owns "BS(1,n) in VA?", and this lane owns the new constructions.
  *Needs:* the definition of finite germ extension and the hypotheses of BHM Theorem 2.1.
- **gq-germ-design.** Is there any germ group containing a divisible (Q,+) that can satisfy the hypotheses of
  BHM Theorem 2.1?
- **gq-germ-necessary** (obstruction). Conjecture on its board: in a finite germ extension of V, a nontrivial
  torsion-free divisible subgroup must map injectively into the germ group at some finite invariant set of
  singular points.
- **gq-q-in-germs.** Locate Q inside VA (the action of T̄ and A on the Cantor set, and at which points Q
  lives). Then test U_3(Q) and Aff(Q) against the same mechanism.

### B. Type (A) actions and twisted Brin–Thompson groups
- **gq-typeA-design.** Find where the repo's type (A) and Alt_fin host equivalences use finite generation of the
  input. See the reduction above: Corollary B does not.
- **gq-typeA-bffhz.** Extract the BFFHZ construction for Aut(F_n): the set S, the overgroup and the stabilizers.
  Then test each ingredient on GL_n(Q).
- **gq-bt-kojima.** Locate and read Kojima–Sheng's Q ≤ 2V, then extend it.
- **gq-nv-obstruct.** SL_3(Z) against the Brin–Thompson hosts nV: literature, distortion, CAT(0) cube actions.

### C. Piecewise projective
- **gq-pp-psl2q.** Signature: "rotation number rigidity of divisible subgroups". Target: in finitely generated
  groups of piecewise PSL_2(R) circle homeomorphisms, and in lifts of T̄ type, N(D) = C(D) for every divisible
  abelian D. That would exclude Q ⋊_r Z with r ≠ 1, U_3(Q), SL_2(Q) and GL_n(Q).
  - *Dead (board):* the natural embedding. A finitely generated group of piecewise PSL_2(Q) maps contains only
    PSL_2(Z[1/S]) of PSL_2(Q), by analytic continuation.
  - *Spark:* the same argument through the germs at ±∞ of Brin's A. Would it kill Aff(Q) in A?
- **gq-pp-higher.** Target: in a group generated by finitely many piecewise-PGL_n(Q) homeomorphisms, the
  globally projective elements lie in the group generated by the generators' pieces. So a finitely generated
  group of this kind contains no PGL_n(Q).

### D. Rings, Leavitt algebras, Steinberg groups
- **gq-ring-leavitt.** A purely infinite simple R with M_n(R) ≅ R and Q in a corner eRe. First step: can a
  finitely generated subring of some L_K(1,2) contain Q?
- **gq-leavitt-units.** Is L_Z(1,2)^x, or its derived subgroup, finitely presented, and what are its normal
  subgroups? For instance, does an augmentation-like map to a characteristic-p Leavitt algebra give proper ones?
- **gq-ring-fp-simple.** A finitely presented simple ring containing Q. Literature first: Evans–Mandelberg–Neff,
  Bokut, Leavitt/Cohn.

### F. Stepping stones
- **gq-affq.** Proposed node `aff-q-embeds-in-fp-simple-group`. Planned: (1) a bounded-denominator obstruction
  for piecewise-algebraic hosts; (2) the Kojima–Sheng mechanism and BS(1,n) in 2V and VA; (3) the type (A)
  reformulation through the sharply 2-transitive action of Aff(Q) on Q.

### G. Reformulations and roles
- **gq-reform-countable.** Do the repo's host equivalences for f.g. inputs survive for countable H = GL_n(Q)
  through a 2-generated decidable overgroup?
- **gq-transfer.** Kourovka 14.10 verbatim, then conditional routes from G: subgroups of GL_n(Q), GL_n(K) for
  number fields K, GL_n(Q̄).
- **gq-heretic, gq-obstruction-miner.** Reading boards; no content yet.

### Support
- gq-map (cone map, pending), gq-lit-arxiv, gq-lit-q-embeddings, gq-calibrator (calibration artifact pending).
- Referees a, b and c are prepared and waiting for requests.

## Priority facts
- **G′.** Mikaelian, arXiv:2507.04347 (v8, 2026-06-03), §1.4 *announces*, with no construction, an explicit
  embedding of GL(n,Q) into a finitely presented 2-generator group, through his explicit Higman algorithm
  (reported by gq-lit-arxiv; RULES §8b). The group is not simple and not "natural". G is untouched.

## Open needs (from boards)
- VA's germ groups at singular points, exactly (gq-va-gl2, gq-va-affq, gq-q-in-germs). Partly covered by
  gq-gq-lit-hosts §1.

## Lanes with no board at snapshot time
gq-adelic, gq-bhm-pattern, gq-borel-q, gq-countable-fields, gq-critic, gq-cuntz-cstar, gq-en-ring,
gq-explicit-fp, gq-explicit-2, gq-heis-q, gq-infinite-primes, gq-integrate, gq-inverter, gq-k2-q, gq-malcev-ring,
gq-pp-fp, gq-pp-lift, gq-pp-simple, gq-ring-alt, gq-rn-varying-degree, gq-scott-union, gq-sl2q, gq-solenoid,
gq-steinberg-q, gq-tbar-lift-n, gq-typeA-alt, gq-typeA-projective, gq-union-alt, gq-union-obstruct, and the
twelve gq-deep-* lanes.
