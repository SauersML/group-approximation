# One-relator soficity: proved families and remaining scope

The universal assertion that every one-relator group is sofic is not
proved or disproved by this work. Its Cairn claim remains open.

## Written results

1. Strictly triangular chains of relations
   `c_i^(-1)x_i^(l_i)c_i=x_i^(k_i)` are sofic when each `c_i` is conjugate
   to a nonzero power of a strictly later generator by a word using only
   later generators. The proof checks the infinite cyclic edge maps at
   every finite attachment and proves passage to the directed colimit.
2. With `a_j=b^(-j)ab^j`, every
   `G(w;l,k)=<a,b | (a^l)^(a^w)=a^k>` is sofic when `w=b^d V(a_j:j>0)`,
   `d>0`, and `l,k!=0`.
3. For all `p,q,s in Z` and all `l,k!=0`, the group
   `G(b^p a^s b^q;l,k)` is sofic. The proof treats each of the three
   least-index roles, all index collisions, and all zero block/end
   exponents. In particular it proves `G(b^(-1)ab^2;1,2)` sofic.

Conjugation means `x^y=y^(-1)xy`. The last specific example is the question
in the introduction of
[Berlai, arXiv:2502.05064v1](https://arxiv.org/html/2502.05064v1).
The deductions above are accompanied by full written arguments; no claim
of literature priority or Lean formalization is made.

The proofs are in
[the triangular-chain artifact](../research/artifacts/triangular-bs-chain-proof-2026-09-07.md)
and [the one-relator artifact](../research/artifacts/mixed-conjugator-one-relator-proof-2026-09-07.md).
They use the established sofic permanence theorems precisely cited there.
The kernel is identified by inverse presentation maps, not just by a
surjection from an approximable group.

## Verification

The deterministic
[replay](../experiments/one_relator_cyclic_peeling_check.py) passed all
3,920 single-block parameter choices, 11,760 shifted Schreier identities,
1,800 one-sided identities, 64 attachment-identity sets, 360 finite
dependency schedules, and five negative controls. See its
[report](../research/artifacts/one-relator-cyclic-peeling-replay-2026-09-07.json).

The independent height-scan and free-reduction checks verify finite
identities. They do not certify soficity, injectivity of amalgam factors,
or an infinite-group theorem. Those steps have written proofs using
normal forms and the cited permanence results. Cairn checks dependency
consistency, not mathematical validity.

The initial and expanded changed-file Cairn checks returned no findings.
The [final validation record](../research/artifacts/one-relator-cairn-validation-2026-09-07.json)
lists the resulting claim statuses and hashes
the proof and replay files. The three new one-relator conclusions are
established in the graph; the full conjecture and the generic Magnus and
Linton targets remain open. The existing `bin/cairn` integration is used
without modifying Cairn's implementation.

## Attempt toward the universal statement

The starting Magnus decomposition has nonamenable free overlap groups.
For the families proved here, a different construction removes that
particular obstacle by adjoining a single generator over cyclic groups.
Each use of the new construction requires an exact presentation identity
and a nonzero-power infinite-order witness for its edge; abstract
soficity of the window groups would not suffice.

For a concrete limit of the present argument, take the indexed word
`w=a_1 a_0 a_1`, where `a_0=a` and `a_1=b^(-1)ab`. In `F(a,b)` this is

    w = b^(-1)ab a b^(-1)ab.

It has zero `b`-exponent and is neither a single `a`-block word nor one
of the strictly positive-height words in Theorem A as written. Rewriting
`G(w;1,2)` makes the new least-index letter occur repeatedly in the
conjugating word as well as in the powered base. The three constructions
in Section 4 of the proof do not supply a single cyclic attachment for
this relator. This is a recorded failed application of this method, not
a proof of nonsoficity, a claim of intrinsic nonmembership in the proved
isomorphism classes, or a claim that the example is open in all literature.

Even proving all nested Baumslag presentations sofic would leave the
separate task of handling arbitrary one-relator words. No such reduction
is asserted. The universal question therefore stays open.

## Published checkpoints

- `3d3d58ebd208d2a7315908e175e703a9d5d55754`: triangular-chain theorem,
  full proof, and Cairn claim/route.
- `c9db663eb9cda7bb7d9a115d6cfef78729e1a00a`: one-sided and single-block
  theorems, exact replay, and integration with existing root/lane notes.

Both checkpoints were advanced onto `main` with fast-forward-only ref
updates, preserving concurrent work. The second checkpoint's GitHub
Actions jobs were cancelled or skipped as `main` advanced; no successful
Lean CI result for these research proofs is claimed.
