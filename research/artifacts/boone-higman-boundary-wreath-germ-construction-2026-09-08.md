# Boundary-orbit wreath products through finite germ extensions

The Cairn proof in `boundary-orbit-cyclic-wreath-germ-proof` constructs a
finitely presented simple envelope for

    Z wr_(G*0^infinity) G

when G is a finitely generated contracting self-similar tree group.
The construction works directly if G has an infinite-order element;
otherwise taking the product with the binary adding-machine group
provides one, and the original wreath product embeds in the enlarged
one. The universal Boone--Higman conjecture remains OPEN.

## What the construction adds

An extra alphabet letter # lets the actor act only before the first #.
A recurring lamp applies an infinite-order actor element on the side
cones 0^j*#*C. Conjugating the lamp follows a boundary ray. Two rays
share only their initial side cones; inspecting a deeper side cone
separates their lamp exponents. This proves faithfulness of the wreath
product, including independence of every finitely supported lamp vector.

The full group of these maps is a finite germ extension of the
contracting actor's Rover--Nekrashevych group. A lamp adds one cyclic
isotropy germ at its limiting ray. It commutes there with the original
isotropy germs, so the relative germ quotient is Z. Taking all allowed
singular germs of a stabilizer gives a map into a finite-rank free
abelian group, with kernel a rational-point stabilizer of the base.

The additional stabilizer argument is carried by
`contracting-srn-stabilizer-ascending-hnn-proof`. After choosing a
clopen neighborhood with the right number of complementary cones, a
pure prefix map contracts it cofinally to the finite rational set.
The neighborhood kernel plus this contraction is an ascending HNN
extension of a finitely presented copy of the base. The remaining
germ quotient is free abelian up to finite index. This proves finite
presentation of those stabilizers, which is the hypothesis needed
for the finite-germ theorem at F_2.

The proof also establishes finite presentation of finite pointwise
stabilizers in the extended actor. Its action on the dense singular
orbit is faithful and highly transitive. Cairn's existing twisted
Brin--Thompson criterion then supplies simplicity and finite
presentation simultaneously.

## Source boundaries

The source imports are precisely identified in the proof routes:

- [Belk--Matucci](https://eprints.gla.ac.uk/349706/2/349706.pdf):
  finite presentation of the contracting base, cone interpolation,
  and finite-index pure prefix cyclic germs. Their Proposition 6
  states finite generation of rational-set stabilizers. The stronger
  conclusion here has its own HNN proof.
- [Belk--Hyde--Matucci, Theorem 2.1](https://arxiv.org/html/2407.03149v1#S2.SS1):
  the finite germ extension criterion, used with n=2 after checking
  its individual hypotheses.
- `twisted-brin-thompson-finite-presentation-criterion`: the existing
  source-backed finiteness and simplicity theorem at the final step.

The construction does not establish the full statement of Theorem D
of arXiv:2609.01868v1, whose projection argument is audited separately.
It supplies an independent proof for the boundary-orbit family, without
the disputed global projection. All cyclic quotients here are formed
inside point isotropy germ groups. There is no homomorphism forgetting
nontrivial lamp homeomorphisms while preserving every prefix map.
No claim of publication novelty or resolution of a previously open
family is made.

## Why the final simple envelope uses the action criterion

The unreplicated actor E has an explicit surjection to Z, proved in
`boundary-orbit-wreath-section-charge-proof`: take total lamp exponent
in each regular-table coefficient and sum over the table. The lamp
recursion preserves this sum under leaf expansion, so it is a
well-defined character of E. Thus E's commutator subgroup has infinite
index; finite presentation of E alone does not settle its finiteness.
The faithful action criterion avoids needing that extra assertion.

This is not a disproof of the altered-representation argument in
[arXiv:2609.01868v1, Section 5.2.2](https://arxiv.org/html/2609.01868v1#S5.SS2.SSS2).
That section repeats every state r times and changes the alphabet.
After repetition the lamp's sum of section charges is r instead of
1, so the character above no longer extends by table summation.
Finite presentation for our original actor does not automatically
transfer to the actor defined by this altered tree action. The
boundary proof here uses its original action throughout.

## Distance from the universal goal

No embedding of every group with solvable word problem into these
wreath products has been proved. There is a concrete reason that
cannot simply be assumed: these input wreath products are residually
finite. Given a nonidentity element, its nontrivial G component is
detected on a finite tree level. If the G component is trivial, choose
a level separating its finitely many nonzero lamp rays and reduce
their integer coefficients modulo a prime not dividing a selected
coefficient. The map to the finite wreath product on that level,
which sums coefficients when rays have the same prefix, detects it.
This is a homomorphism because taking prefixes is equivariant for
the finite-level actor quotient.

Residual finiteness passes to subgroups, whereas the original goal
includes groups with solvable word problem that are not residually
finite. Thus these input wreath products alone are not universal
hosts. The simple envelopes are larger groups, and nothing here
classifies all their subgroups or proves them universal either.

A subsequent complexity argument in
`research/artifacts/boone-higman-finite-state-and-shell-germ-limits-2026-09-08.md`
rules out universality of the intermediate rational actors E themselves:
some decidable finitely presented residually finite groups admit no
rational embedding. The argument does not assert that the final
twisted Brin--Thompson envelopes have rational actions.

This is mathematical proof text in Cairn, not a Lean certificate.
No GPU computation establishes these results. The previously attempted
Civo provisioning did not create an instance; recorded GPU spending
remains zero. Structural CI validates graph wiring and the existing
finite controls, not these infinite-group arguments.

## Validation

The principal construction is commit `fce60d763`, and the integer
character is commit `3ca0811f7`. Both reached main. The initial remote
checks were stopped by two existing central-three-cycle node IDs
exceeding the schema limit, followed by a filename/ID mismatch during
repair. Commits `7048ec1d0` and `2056c4989` repaired those identifiers
and their references; their mathematical contents were unchanged.

[Research run 34291167326](https://github.com/SauersML/group-approximation/actions/runs/34291167326)
completed successfully on main integration
`de914a9f379150474847384537608679110559bc`. The downloaded evidence is
retained in `.cairn/bh-boundary-wreath-check-20260908/`.

Inspection of the exported `node_status` fields gives ESTABLISHED for
the rational-stabilizer claim, the boundary-wreath embedding claim,
and the integer-character claim. The universal
`boone-higman-conjecture` remains OPEN. The run also passed the existing
source-syntax checks and exact finite controls. These are graph and
control checks, not machine verification of the new mathematical proofs.
