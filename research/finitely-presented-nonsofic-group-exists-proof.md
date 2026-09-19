---
rg: 2
id: finitely-presented-nonsofic-group-exists-proof
kind: route
title: Cover the finitely generated witness by a finite table
target: finitely-presented-nonsofic-group-exists
requires: [universal-leavitt-el4-nonsofic]
artifacts:
  - GroupApproximation/Covers/TableCover.lean
  - GroupApproximation/Endpoint/MainResults.lean
---

## Why sufficient

The prerequisite gives a finitely generated group `G` that is not sofic.
Choose a finite table `F_0` and `epsilon>0` witnessing this failure. The
construction in `Covers/TableCover` enlarges `F_0` to a finite table `F`
containing a finite generating set and forms the finitely presented table
group `H = tableGroup F h_1`.

The load-bearing step is direct. `tableGroup_no_model` sends any
`epsilon`-model of `H`'s distinguished table through `pullbackTableModel` to
an `epsilon`-model of the forbidden table in `G`. Hence `H`'s distinguished
table has no `epsilon`-model. If `H` were sofic,
`tableModel_of_isSofic` would supply such a model, contradicting
`tableGroup_no_model`; this is exactly `tableGroup_not_isSofic`.

The canonical table-evaluation homomorphism `H -> G` is surjective because
`F` contains a generating set. That epimorphism proves the cover assertion
and, in the strengthened endpoint, infinitude. It is not used to prove that
`H` is nonsofic: arbitrary sofic quotient permanence is false by
[[sofic-quotient-nonclosure]].

## Not a restatement

The prerequisite is about one explicit elementary group and does not mention
presentations; a finitely generated nonsofic group is not a finitely presented
one, and the gap between them is exactly the cover construction -- which is a
theorem about arbitrary finitely generated nonsofic groups and would be worth
having even if this witness were replaced.
