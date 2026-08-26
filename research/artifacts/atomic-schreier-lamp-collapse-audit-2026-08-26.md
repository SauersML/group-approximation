# Atomic Schreier lamp collapse — ingestion audit, 2026-08-26

Source: user-supplied dossier, "property-(T)-free direction / Noncommutative
Reservoir PCP", pasted 2026-08-26.  Seven sections.  This file records what was
re-derived, what was already in the graph, and two mathematical corrections the
dossier needs before its §3 endpoint is usable.

## Verdict by section

| § | Dossier content | Verdict |
|---|---|---|
| 1 | Clifford Cook--Levin gate matrices, `rank R_C = m + UNSAT_C` | TRUE, elementary, NEW as a gate-additive statement; landed as `affine-gate-matrix-rank-counts-violated-gates`.  Its step to representation multiplicity is blocked by an obstruction the graph already carries. |
| 2 | Perron--Frobenius capacity endpoint `kappa y.x <= y.eps` | TRUE and ALREADY IN THE GRAPH.  `atlas-fractional-pauli-return-network` clause 2 is literally `B^T y >= (1+kappa) y`, and the atlas lane (`atlas-supercritical-pauli-branching-cycle`, `atlas-supercritical-from-pauli-recurrence`, `exact-corona-branching-dimension-collapse`) carries the whole mechanism.  Nothing authored. |
| 3 | Atomic Schreier collapse without property (T) | Inequality TRUE; its **conclusion is already established** as `infinite-schreier-pvm-transport-kills-finite-mark`, the worked example has a **false invariance step**, and the endpoint carries a **mandatory non-sofic input**.  Corrected, narrowed to what is new, and landed. |
| 4 | "Noncommutative Reservoir PCP" as the missing theorem | ALREADY the graph's `multiplicity-return-transducer` (same five clauses, same "clause 4 carries the whole difficulty" analysis) plus `extensive-cosystolic-index-defect`.  Nothing authored. |
| 5 | Signed-character / parallelogram decoder is close; bounded-character-code no-go blocks capacity | ALREADY IN THE GRAPH, correctly described. |
| 6 | Proposed architecture (reversible computation to operator LTC to rank to branching to PF) | This is a restatement of §§1--5; no new obligation. |
| 7 | Multiplicity-register LTC target theorem | Same statement as `multiplicity-return-transducer`, at lower resolution (it omits the fixed-packet-scale clause, which is the clause that does the work). |

Literature: `arXiv:2507.22444` (Taller--Vidick) was already imported and
source-checked on 2026-08-20 (`taller-vidick-entangled-long-code-citation`),
including the perfect-completeness remark the dossier quotes, and the
`epsilon = 0` implication is `perfect-lcs-gap-implies-nonhyperlinear`.  No new
citation was needed and none was added.

## Collision — the mass bound is already in the graph

The dossier's `(10)`, `sum over Omega of q_chi <= (2/kappa) sum_s L_s`, is
`(ISP3)` of `infinite-schreier-pvm-transport-kills-finite-mark`, established
in the affine-Leavitt lane.  The two leakage functionals are literally equal:

```text
sum over chi of || U_s P_chi U_s^* - P_(s chi) ||_2^2 = 2 L_s,
```

so `E_PVM = (2/D) sum_s L_s`, and with `gamma = 1 - rho` the two conclusions
`mu <= E_PVM/(2 gamma)` and `sum_Omega q_chi <= (2/kappa) sum_s L_s`,
`kappa = 2 D (1 - rho)`, are the same inequality.  The duplicate detector did
not see it -- disjoint vocabulary, no title overlap -- so the first draft of
this ingestion carried a second, redundant proof of an established theorem.
It was retired before the commit and its consumers were retargeted, per the
merge-on-sight rule.

What survives as new is what the existing node ASSUMES:

- `(ISP1)`, the bottom spectral gap of the orbit graph, is a hypothesis there.
  `kesten-amenable-stabilizer-uniform-gap` discharges it, with one constant
  `gamma = 1 - rho(A,S)` valid on every orbit with an amenable stabilizer.
- the dictionary and the amplitude form
  (`lamp-character-transport-bounds-schreier-dirichlet`) make the two
  vocabularies interchangeable and give the estimate its classical reading.

Likewise the dossier's decoding ask is half-established already:
`all-abelian-uniform-hs-rounding-gives-global-pvm` (Akhtiamov--Dogon) rounds
any uniformly all-pairs-multiplicative map on a countable abelian group to an
exact representation in the same dimension, with a finite-support joint PVM in
exponent two.  So the open hole is exposure plus actor covariance, not
diagonalization.

## Correction 1 — the negative sector is not invariant

The dossier applies its Schreier gap (9) to `h.1_Omega` with
`Omega = {chi : chi(w) = -1}`, `w = m_e m_a`.  That set is **not** invariant
under the actor.  With `(s.chi)(m_x) = chi(m_(s^(-1) x))`,

```text
(s.chi)(w) = chi(m_(s^(-1))) chi(m_(s^(-1) a)),
```

which is unrelated to `chi(w)`.  Invariance is load bearing: the restriction
step needs `1_Omega(s chi) = 1_Omega(chi)` to get
`||f - sf||_2 <= ||h - sh||_2`.

The repair is to use the left-invariant saturation

```text
Omega = {chi : chi o R_a =/= chi},
```

`R_a` the right translation `x |-> xa`, which commutes with the left action.
It contains `{chi(w) = -1}` (take `s = e`), so the mass bound survives, and it
excludes exactly the constants, so every one of its points still has a proper
stabilizer.  Landed as `tarski-lamp-nonconstant-sector-has-amenable-stabilizers`.

## Correction 2 — the endpoint is refuted by any sofic actor

The dossier's endpoint hypothesis ("finite microstates rounded to a single
global finite character table with actor leakage tending to zero") is stated
with no modulus in the relator defect.  In that form it is vacuous exactly when
the group is not hyperlinear, hence equivalent to the target -- the
restatement-dressed-as-reduction pattern.  Restated with a modulus
(`L_s <= C_s Def(U)` at every defect below a threshold) it becomes a genuine
reduction, and then it is **falsifiable and false for every sofic actor**:

- `gkp-sofic-action-toolkit`: the regular action of a sofic group is sofic.
- `gkp-wreath-permanence-theorem` (GKP Theorem 3.6): a generalized wreath
  product of sofic groups over a sofic action is sofic.

So `A` sofic makes `C_2 wr A` sofic, hence hyperlinear, hence supplied with
microstates of vanishing defect in which the marked involution stays separated
-- contradicting the leakage bound through the atomic mass `1/2`.  The
consequence is recorded as `sofic-actor-refutes-lamp-character-transport` and
is the mandatory falsification test on the open hole.

This does not kill the route (nothing does: every route to the goal entails a
non-sofic group).  What it kills is the claim that the endpoint is *short*.
The dossier's own summary says property (T) was replaced by Perron--Frobenius
growth of a finite computation graph; in §3 what was actually replaced is the
**amplifier**, while the step property (T) was used for -- turning
almost-invariance into invariance, i.e. the rounding -- is untouched and is
where the entire difficulty now sits, now carrying a non-soficity obligation
about the specific actor.

Two further limits on §3, recorded on the open node: a Tarski monster is
infinitely presented, so this endpoint can never be the fixed-finite-template
statement §4 asks for; and the abelian half of the rounding is the only half
the almost-commuting literature reaches.

## What was landed

Established, with direct-proof or citation routes:
`affine-gate-matrix-rank-counts-violated-gates`,
`lamp-character-transport-bounds-schreier-dirichlet`,
`kesten-amenable-stabilizer-uniform-gap`,
`tarski-lamp-nonconstant-sector-has-amenable-stabilizers`,
`sofic-actor-refutes-lamp-character-transport`.

Retired before landing, as a duplicate of
`infinite-schreier-pvm-transport-kills-finite-mark`:
`amenable-stabilizer-gap-bounds-atomic-character-mass` and its route
`atomic-character-mass-from-kesten-gap`.  Nothing outside this lane ever
referenced them.

Open, with the goal route:
`defect-controlled-lamp-character-transport`, feeding
`non-hyperlinear-group` through `nonhyperlinear-from-atomic-lamp-collapse`.
