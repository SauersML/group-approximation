# Finite relator reservoirs, packet feasibility, and the window no-go (2026-08-23)

Ingestion record for a dossier proposing a new compactness reduction for the
local-ucp-splitting hole
`triangle-relator-extension-admits-local-ucp-sections`, plus one correction to
the Harris region.  Everything below was re-derived here before being written
into a node; the derivations are reproduced in the `-proof` routes, not in this
file.

## What was accepted, and at what strength

| dossier item | node | strength |
|---|---|---|
| finite-reservoir compactness lemma | `finite-reservoir-compactness-lifts-ucp-repairs` | ESTABLISHED, self-contained, RFD as an explicit hypothesis |
| finite fd-representation packets are always repairable | `fd-representation-packets-never-obstruct-ucp-sections` | ESTABLISHED, self-contained |
| explicit ucp section of the finite face, exact on one edge | `explicit-finite-face-ucp-section-is-edge-equivariant` | ESTABLISHED, self-contained; strengthened to right-module linearity |
| orthogonal-position / window sections collapse to a Folner vector | `position-window-ucp-sections-collapse-to-folner-vectors` | ESTABLISHED, self-contained |
| finite relator-reservoir conjecture | `finite-relator-reservoir-repairs-every-fd-packet` | OPEN, with `## Attempts` |
| `LP(S_A) <=> LLP(A)` for the Harris system | `harris-lp-to-llp-implication-is-one-directional` | the equivalence is WITHDRAWN; only `LP => LLP` survives |

## Two corrections made to the dossier itself

1. **The window no-go and the explicit face section are the same computation.**
   The dossier presents them as independent (its items 3 and 4).  They are
   not: the explicit face section

   ```text
   Theta(u_p)=|P|^(-1) sum_(x in P) u_(sigma(x))^* u_(sigma(xp))
   ```

   *is* an instance of the forbidden shape `(2)`, with `c_g=|P|^(-1/2)` and
   the position index running over the finite group `P=P_13`.  It survives
   exactly because the scalar vector `z` it produces is the normalized
   indicator of a finite group, which *is* invariant under every right
   translation.  So the no-go is sharp in the right variable: window sections
   exist on finite faces and provably nowhere else.  Both nodes record this;
   it is what makes them consistent rather than contradictory, and it is the
   precise sense in which the defect is "concentrated on one edge".

2. **The face section is strengthened.**  The dossier records
   `Theta(u_h)=u_h` for `h in P_1` under a right `P_1`-equivariant set
   section.  The same computation gives `Theta(a b)=Theta(a) b` for all
   `b in C^*(P_1)`: `Theta` is a right `C^*(P_1)`-module map, not merely a
   map fixing `C^*(P_1)` pointwise.

## Scope limits recorded, not asserted away

- The reservoir lemma is stated with **RFD of `A` as a hypothesis**, because
  RFD is used twice (to norm the reservoir by finitely many finite-dimensional
  representations, and to detect positivity in `A`) and is not free.  Its
  instantiation at `A=C^*(G_0)` goes through the separate citation node
  `virtually-free-full-algebras-are-rfd`, so the literature dependence stays
  visible rather than being absorbed into a lemma advertised as general.
- The dossier states the conjecture for *group-word* systems
  `E_F=span{u_g : g in F}`.  Local liftability quantifies over **all**
  finite-dimensional operator systems of the quotient, and reducing the
  general case to a dense directed family of group-word systems is not a
  recorded step.  `finite-relator-reservoir-repairs-every-fd-packet` is
  therefore stated for arbitrary finite-dimensional `E`, and the group-word
  case is recorded in its `## Attempts` as the concrete attack together with
  the missing reduction.

## The Harris correction

The dossier reports that Harris, arXiv:2607.11001v1, explicitly remarks that
the converse of Proposition 3.4(2) fails even under hyperrigidity.  That
remark is **not** what the correction node rests on: the primary PDFs are not
in this tree and were not re-read this date, so the reported remark is carried
as an attributed report only.  What the node proves is weaker and
self-contained, and it is enough: the derivation previously recorded for the
converse is invalid, because LLP of `A` constrains only ucp maps *defined on*
`A` (equivalently on `M_k(A)`), while LP of `S_A` quantifies over every ucp map
*out of* `S_A` into a quotient, and no such map need extend to the ambient
algebra.  Hyperrigidity does not close that gap: it constrains ucp maps on
`C^*(S)` that agree with a representation on `S`, not ucp maps out of `S`.

Consequently:

- `LP(S_A) => LLP(A)` (Harris Proposition 3.4(2), plus matrix/corner
  permanence) stands, and every route that consumes it is unaffected --
  `nonhyperlinear-from-three-dimensional-hyperrigid-lp`,
  `km-harris-maximal-matrix-range-collapse` and
  `harris-lp-is-maximal-matrix-range-collapse` all use only this direction.
- `LLP(A) => LP(S_A)` is withdrawn.  The practical consequence is a priority
  change, not a cascade change: the Harris target is now *potentially strictly
  stronger* than the ambient LLP it is meant to abbreviate, so
  `explicit-prs-harris-three-dimensional-system-has-lp` is no longer a free
  reformulation of the LLP family and should not be preferred to the ambient
  target on the grounds of being "the same problem, smaller".

Nodes edited for this: `llp-failure-has-three-dimensional-hyperrigid-witness`,
`lp-of-harris-generator-system-forces-nonhyperlinear`,
`explicit-prs-harris-three-dimensional-system-has-lp`, and section 2 of
`research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md`.

## What this does and does not do for the goal

It puts the **first route** into
`triangle-relator-extension-admits-local-ucp-sections`, which until now was a
frontier hole with no live routes at all.  The route's open leaf is a
bounded-word-depth statement about the finitely generated relator ideal, and
it is genuinely weaker information than the target in one direction only: the
reservoir conjecture implies local splitting, and local splitting does *not*
imply the reservoir conjecture (a ucp section's correction lies in the closed
ideal `I_N`, not in any finite span of `u_a(u_(n_j)-1)u_b`).  So this is a
reduction, not a restatement.  It supplies no non-hyperlinear group.
