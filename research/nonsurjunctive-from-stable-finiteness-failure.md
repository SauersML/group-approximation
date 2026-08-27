---
rg: 2
id: nonsurjunctive-from-stable-finiteness-failure
kind: route
title: Feed a one-sided inverse over F_2 into the linear-automaton criterion
target: leavitt-unit-group-nonsurjunctive
requires: [stable-finiteness-failure-refutes-surjunctivity, leavitt-group-algebra-not-stably-finite]
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

## Why sufficient

`stable-finiteness-failure-refutes-surjunctivity` is stated for an arbitrary
group, an arbitrary finite field and an arbitrary finite matrix size.
Instantiate it at `k = F_2` and `G = L_(F_2)(1,2)^x`; the matrices supplied by
`leavitt-group-algebra-not-stably-finite` are exactly its hypothesis at that
`n`.  The conclusion is an injective non-surjective linear cellular automaton
on the full shift over the finite alphabet `F_2^n`, which is the target.

The prerequisite is the matrix statement, not the scalar one, because that is
what the criterion consumes: a failure at some `n >= 2` serves here just as
well as a Kaplansky counterexample.  The scalar lane reaches it through
`stably-finite-failure-from-direct-finiteness-failure`.

## The only live route

This is the only live route to the target in this graph.  The dynamical
material the repository already owns — the strict self-embedding of the proper
subshift `X` — cannot substitute for it; see
`subshift-self-embedding-carries-no-surjunctivity-content`, which kills the
route that tries.

It is not a restatement of the target.  The target quantifies over all finite
alphabets and all cellular automata, including nonlinear ones, while the
prerequisite is a purely algebraic statement about one group algebra.  A proof
of the target need not go through it — a nonlinear construction would bypass
group-ring finiteness entirely — so this route is a genuine narrowing rather
than the only conceivable one.

## Direction of travel

The negative implication used by this route is one-way, but the positive
implication in the old text was backwards.  Bradford--Fournier-Facio,
Corollary 3.25, proves that every surjunctive group satisfies Kaplansky **stable**
finiteness over every field.  Consequently

    Surj(G)  =>  SF(k[G])  =>  DF(k[G]).

For the present Leavitt unit group,
`leavitt-stable-finiteness-equals-direct-finiteness` strengthens the right-hand
side to `SF(F_2[G]) <=> DF(F_2[G])`.  Thus a scalar one-sided inverse still
refutes Gottschalk exactly as this route says, and conversely a proof that `G`
is surjunctive would automatically prove both stable and direct finiteness of
`F_2[G]`.

What does **not** reverse is the last step: stable/direct finiteness of the
group algebra gives linear/additive surjunctivity, not full surjunctivity for
arbitrary finite alphabets and nonlinear local rules.  Thus the Kaplansky lane
can refute Gottschalk, but a positive solution of the ring problem would leave
the genuinely nonlinear Gottschalk problem alive.
