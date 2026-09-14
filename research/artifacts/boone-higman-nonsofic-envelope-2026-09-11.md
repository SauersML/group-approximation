# Boone--Higman forces a finitely presented simple nonsofic group, 2026-09-11

Companion to `research/artifacts/boone-higman-mf-radical-bridge-2026-09-11.md`.
The conjecture remains open. This record proves a second consequence of it, in
the subject this repository is named after.

## The statement

```text
Boone-Higman  ==>  there is a finitely presented simple nonsofic group.
```

Recorded as the root `fp-simple-nonsofic-group` with the route
`fp-simple-nonsofic-from-boone-higman`.

## Why it is four established facts and one permanence lemma

Let `R = L_(F_2)(1,2)` and `H = EL_12(R)`.

1. `binary-leavitt-elementary-group-is-simple`: `EL_n(R) = GL_n(R)` is
   nontrivial and simple for every `n >= 3`. So `H` is simple.
2. `d-ary-leavitt-groups-nonsofic-over-finite-fields`: for a finite field and
   an algebra with a `d`-ary Leavitt family, every `EL_{m+1}` with `m >= 1` is
   nonsofic (`aryLeavitt_elementary_not_isSofic`). So `H` is nonsofic. This is
   kernel-checked.
3. `rank-twelve-leavitt-elementary-wp-decidable` (landed today): `H` is
   infinite, finitely generated, and has decidable word problem, hence is
   recursively presented.
4. `sofic-passes-to-subgroups` (new): soficity passes along injective
   homomorphisms — `isSofic_of_injective` in
   `GroupApproximation/Sofic/SoficTransfer.lean`, kernel-checked. So
   nonsoficity is inherited by every overgroup.

By 1--3, `H` is an admissible Boone--Higman input. The conjecture embeds it in
a finitely presented simple `K`; by 4, `K` is nonsofic.

Fact 4 was already used inline by three routes
(`universal-leavitt-el4-nonsofic-proof`,
`d-ary-leavitt-nonsofic-via-binary-corner`,
`hereditary-nonsofic-descent-proof`). It is stated as its own claim now
because this route applies it to an envelope no construction here produces,
so the permanence step can no longer live inside somebody else's derivation.

## The gap this measures

Each pair of the three adjectives is already realized:

| finitely presented | simple | nonsofic | realized by |
|---|---|---|---|
| yes | no | yes | `finitely-presented-nonsofic-group-exists` (established, kernel-checked) |
| no | yes | yes | `EL_12(L_(F_2)(1,2))`, by facts 1--3 above |
| yes | yes | unknown | every Thompson-like group in the graph |

So the entire distance between this repository and a finitely presented simple
nonsofic group is **a finite presentation of one finitely generated simple
nonsofic group it already owns**. That is exactly an instance of
Boone--Higman, which is why the implication is not a coincidence: it says the
conjecture is at least as strong as producing an object the non-MF programme
wants for its own reasons.

## Two consequences for how to attack things

**Negative side of Boone--Higman.** Proving that every finitely presented
simple group is sofic would refute the conjecture. Together with the MF
version in the companion artifact, the conjecture now has two independent
approximation-theoretic attacks on its negative side, neither passing through
a decidability argument or an embedding argument.

**Cheapest open question in the table.** Nothing in this graph asserts
soficity or nonsoficity of `V`, of `nV`, of a twisted Brin--Thompson group, or
of a Röver--Nekrashevych group. Settling any one of them is a self-contained
question; a nonsofic answer for any single one establishes
`fp-simple-nonsofic-group` outright, with no Boone--Higman needed. It is not
blocked by anything recorded here, and it is the concrete next step for this
lane.

## What is deliberately not claimed

Full MF radical and nonsoficity are independent conditions here.
`simple-sofic-total-mf-radical` is a sofic group with total MF radical, so no
argument in either artifact upgrades an MF statement to a soficity statement
or the reverse. The two conclusions share a witness only because `H` happens
to satisfy both hypotheses.

Nonsoficity is also not known to pass to quotients
(`sofic-quotient-nonclosure` records the failure of quotient permanence), so
the maximal-quotient manoeuvre that works in the MF lane does not transfer:
even a finitely presented simple quotient of the existing finite-table cover
would need its nonsoficity proved separately.

## Verification boundary

Facts 1, 2 and 4 are kernel-checked in the development; fact 3 and the
deduction are written proofs landed today. No Lean certificate is claimed for
the new nodes, and no computation was run for this step: the content is a
permanence lemma and a specialization, neither of which gives signal from a
computer.

## Addendum, same day: both targets established, contrapositive attacks closed

Khanh, arXiv:2609.08428v1, Theorem 6.1, which the literature lane verified from
the full paper, makes the binary Leavitt unit group finitely presented. It is
already simple, nonsofic and full-MF-radical here, so it witnesses both
`fp-simple-full-mf-radical-group` and `fp-simple-nonsofic-group` directly. The
Boone--Higman routes recorded above remain valid second derivations.

This record called the contrapositive the usable direction. That is withdrawn.
Both statements are true, so their negations cannot refute Boone--Higman. What
survives is only that a universal construction must carry these properties on
the envelopes of inputs that have them.
