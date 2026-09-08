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
