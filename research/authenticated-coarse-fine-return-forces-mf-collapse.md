---
rg: 2
id: authenticated-coarse-fine-return-forces-mf-collapse
kind: claim
title: One authenticated coarse-to-fine return row forces total MF collapse, with no Kazhdan and no stability hypothesis
distinct_from:
  compression-defect-dies-in-mf-under-mark-stability: that removes property (T) by substituting a GLOBAL analytic hypothesis, point-norm stability, and repairs the approximants; this removes it by substituting a FINITE-COORDINATE syntactic one, a single operator-norm support row, and repairs nothing.
  spectral-recurrence-power-return-non-mf-criterion: that freezes a coordinate and defeats it by finite spectral recurrence of a conjugacy-to-power return, and its open half is a uniform return CONSTANT over unboundedly many words; this needs one fixed word at one fixed cell and defeats the coordinate by a rank count.
  opnorm-coordinatewise-capacity-diagonal: that defeats a frozen coordinate by exposing challenges of unbounded finite-dimensional capacity, so its open half is a self-hashing finite syntax; this exposes exactly one challenge, of fixed size, and needs no capacity growth at all.
  hs-collapse-sign-twist-non-mf: that converts a strict normalized-HS involutive collapse into operator-norm non-MF through a central sign-twist HNN wrapper; this never enters the 2-norm and adjoins nothing to the presentation.
  four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap: that needs all four returned two-qubit Pauli words simultaneously target-Pauli and confined to one source factor, and pays a normalized-HS constant; this needs one coarse corner, one fine corner and one return word, and pays the rank threshold 1.
---

**ESTABLISHED.**  Let `Gamma=<S|R>` be finitely presented, let `z != 1` in
`Gamma`, and write

```text
Def_R(U)=max_(rho in R) ||rho(U)-I||_op                    (AMR0)
```

for a finite-dimensional unitary tuple `U` indexed by `S`.  Fix integers
`r<s`, a fixed finite packet of `r by r` and `s by s` matrix-unit templates,
and a fixed return word `J`.  Say `(Gamma,z)` has an **authenticated
coarse-to-fine return** if there is a modulus `omega(t)->0` such that for
every `U` with `Def_R(U)` small enough and `z(U)` bounded away from `I`, one
obtains, after an `o(1)` operator-norm perturbation of the fixed packet
alone:

1. a **nonzero** projection `P`;
2. an exact `r by r` matrix-unit system on `P`, with minimal corner `e`;
3. an exact `s by s` matrix-unit system on the **same** `P`, with minimal
   corner `f`;
4. the evaluated unitary `J(U)`, satisfying

```text
||(1-f)J(U)e||_op <= omega(Def_R(U)).                      (AMR)
```

Then

```text
z in Rad_MF(Gamma),                                        (AMR2)
```

so `Gamma` is not MF; and if `<<z>>_Gamma=Gamma` then

```text
Rad_MF(Gamma)=Gamma,                                       (AMR3)
```

i.e. every norm-matrix-corona representation of `Gamma` is trivial.

No property `(T)`, no spectral gap, no Kazhdan subgroup, no trace, no
normalized rank, no matricial stability, no torsion, no central element and
no depth growth appear in the hypotheses.

## Where the difficulty is, stated exactly

Clauses 1--3 are **not** three separate analytic burdens.

* **Exactification is free.**  By
  `opnorm-packet-exactification-is-dimension-free`, an operator-norm
  `delta`-approximate packet rounds to an exact one with a modulus depending
  only on `r` and `s`, and two packets whose approximate identities are
  `delta`-close are carried onto one common `P` by a unitary `1+O(delta)`.
  Fixed-word telescoping charges the return row only `O(delta)` for this.
  The audit that first proposed this theorem listed exactification as a
  hypothesis; it is a consequence.
* **The whole burden is the common identity.**  What must be recovered from
  the relators is that the coarse and fine approximate packets have
  approximately equal identities.  That is an **additive** statement about
  operators, and a Steinberg/root presentation encodes coefficient addition
  as multiplication inside a root subgroup, never as an operator sum.
  `rectangular-escape` is exactly the model in which the two identities
  differ, by trading label dimension against spectator multiplicity.

## The endpoint is a rank count, and that has a consequence for how to read it

By `rank-deficient-return-row-has-operator-norm-one`, once both packets are
exact on a common nonzero `P` the row `(AMR)` is not merely hard to satisfy:
its left-hand side equals `1` for **every** unitary whatsoever.  Two things
follow, and both matter.

First, the theorem is immediate -- the route is four lines.  Second, the
hypothesis can only ever be discharged as a **derivation from the relators**.
There is no model exhibiting it, no partial numerical evidence for it, and
its antecedent is empty the moment it is proved.  That is the ordinary shape
of a relator-contradiction argument, but it means no progress toward
`(AMR)` can be measured by finding better carriers; progress is measured only
by how much of the common-identity recovery has been derived.

## Robustness of the endpoint under polar correction

The rank count does not require `J(U)` to be exactly unitary.  By `(SVP4)` of
`rank-deficient-return-has-a-singular-value-plateau`, if the evaluated return
`T` only satisfies `||T^*T-1||_op<=eps<1` then at least `rank(e)-rank(f)`
singular values of `(1-f)Te` are at least `sqrt(1-eps)`, so

```text
||(1-f)Te||_op >= sqrt(1-eps).
```

A decoder may therefore hand over an approximate isometry, or polar-correct
its return, without losing the obstruction: `(AMR)` need only be violated
below `sqrt(1-eps)` rather than below `1`.  This matters because a
finite-coordinate selector is naturally extracted as a Gram/polar object
rather than as an exactly evaluated group word.

## Why this is the property-(T)-free replacement worth running

The slogan "full orthogonal self-copy plus commutator calculus plus normal
generation" is **not sufficient**, and Cairn already refutes it three ways:
`bare-self-copy-mf-calibration` (exact finite-dimensional sterility, and even
equality of the parent and child generated C*-algebras, does not give MF
sterility); `fixed-mark-forbids-uniform-clifford-table-area` (no uniformly
bounded full Clifford table exists for a fixed nontrivial mark); and the
observation that arbitrarily deep exact packets --
`leavitt-prefixes-form-exponential-heisenberg-packet` -- only force the
matrix dimension up, which an MF approximation is free to supply.

The missing third clause is a **finite-coordinate same-reservoir return**,
and this node is its cheapest correct form.  Its Leavitt instance is
`opnorm-leavitt-coarse-fine-return-row`; the algebraic inputs that instance
needs are already established
(`iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart` for the full
matrix chart, `one-coarse-to-fine-prefix-isometry-closes-the-reservoir` for
the fixed three-elementary return word, and
`full-leavitt-idempotent-defect-saturation` for `(AMR3)`).
