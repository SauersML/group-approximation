# Relative automorphism finite-presentation obstruction

Date: 2026-09-08. The Boone--Higman conjecture remains open in this work.

The proposed repair was to choose a decidable simple MIF core, so that
the BFFHZ evaluation action would have no kernel. A finite-relator lifting
argument instead shows that this repair cannot manufacture finite
presentation: any finitely presented subgroup of Aut_G(G*F_n) containing
the canonical translations of a finitely generated G forces G itself to
be finitely presented.

The complete argument is retained in
`research/relative-automorphism-finite-relator-lifting-proof.md`. Its
essential step selects finitely many base relators which make lifts of
the proposed host's generators into automorphisms, and which enforce its
finite presentation. The translations then force every remaining base
relator to follow from those finitely many. Lifting generators without
also enforcing inverse identities would not justify the argument.

There is an explicit counterexample to the repository's universal
computable-core claim: take the twisted Brin--Thompson group for the
regular Z-action on Z. It is finitely generated, infinite, simple, MIF,
and has a decidable word problem, but its infinitely many pair orbits
prevent finite presentation. Its relative automorphism action is faithful,
so its action image cannot be finitely presented. The core construction
and its word algorithm are in
`research/regular-cyclic-twisted-core-proof.md`; the deduction is in
`research/bffhz-computable-core-counterexample-proof.md`.

## Consequences for the active goal

- `bffhz-action-image-is-finitely-presented` is refuted in its stated
  universal, computably presented-core scope.
- `boone-higman-via-bffhz-action-image` consequently has a refuted
  prerequisite and is no longer a live proof route.
- For every finitely generated infinite simple MIF base, finite
  presentation of this faithful action image is equivalent to finite
  presentation of the base. Taking a smaller subgroup of the relative
  automorphism group containing the same translations cannot avoid the
  obstruction.
- A selective construction using non-MIF cores is not excluded. Neither
  are other actions or embeddings. No such construction is supplied here.
- The published BFFHZ Question 3.2 concerns finitely presented bases;
  its unresolved cases are not answered by this counterexample.

## Sources and verification scope

The core uses [Belk--Zaremsky](https://eprints.gla.ac.uk/280398/1/280398.pdf),
Section 1, Theorem A and Theorem 3.4, for its definition, finite generation
and simplicity. The non-finite-presentation deduction uses
[Zaremsky's Theorem A](https://arxiv.org/html/2405.18354v2).
[BFFHZ](https://arxiv.org/html/2503.21882v2) supplies the high-transitivity
and MIF facts in its introduction, the sufficient presentation condition
in Proposition 1.1, and faithfulness in Lemma 2.2.

The lifting argument and explicit word algorithm are written mathematical
arguments, not Lean certificates. No novelty claim is made. Cairn's
structural checks validate dependency and refutation bookkeeping; they
do not mechanically verify these proofs. No local code or build was run
for this work. No GPU computation contributed to this result.

## Remote validation

The mathematical changes were committed as `147b04cb9`; the redundant,
incorrectly typed `invalidates` edge was removed in `1ccbfe33d`. The
claim's `refuted_by` edge supplies the refutation. The first workflow run
`34287709316` caught that schema mistake before exporting results.

The corrected integration at main commit
`14f4b79fbc4799ead2219ffc9adac35f19e68d0a` passed
[research check 34287804077](https://github.com/SauersML/group-approximation/actions/runs/34287804077).
Downloaded outputs are retained under
`.cairn/bh-automorphism-check-20260908/`. The inspected `node_status`
fields, distinct from the CLI's generic `status: ok`, are:

| Node | Cairn status |
| --- | --- |
| relative-automorphism-fp-host-reflects-base-presentation | ESTABLISHED |
| regular-cyclic-twisted-core-is-decidable-mif-non-fp | ESTABLISHED |
| bffhz-computable-core-fp-upgrade-is-false | ESTABLISHED |
| bffhz-action-image-is-finitely-presented | REFUTED |
| boone-higman-via-bffhz-action-image | INVALIDATED |
| boone-higman-conjecture | OPEN |

These statuses confirm the intended graph bookkeeping, not independent
mathematical or Lean verification. Existing exact finite controls also
passed; they do not test the new infinite-group arguments.

## Follow-up literature located

A fresh search located Almeida--Dantas--de Oliveira-Tosti,
[arXiv:2609.01868v1](https://arxiv.org/html/2609.01868v1), submitted
September 1, 2026, which was not yet cited in the research directory.
Theorem D gives finitely presented simple envelopes for specified
permutational wreath products with free abelian lamps and a non-torsion
contracting self-similar actor, subject to Theorem A's subgroup conditions.
The introduction and theorem statement were inspected. The proof and
precise applicability to our remaining constructions have not been audited,
so this source is a follow-up candidate, not a new established Cairn
premise or a universal embedding theorem. In particular, its own
Question 1.1 leaves a specified wreath product over PSL_2(Z[1/2]) open.

Follow-up: the Section 5.2.1 projection step was subsequently checked
against the PDF and audited in
`research/artifacts/boone-higman-wreath-projection-audit-2026-09-08.md`.
That audit rules out the required coefficient-forgetting full-group map;
Theorem D remains unimported rather than being marked false.
