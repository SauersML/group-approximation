---
rg: 2
id: hyperlinear-quotient-permanence-equivalence
kind: claim
title: Universal hyperlinearity is exactly arbitrary-quotient permanence, equivalently the idempotent boundary of the CEP
distinct_from:
  non-hyperlinear-group: that claim asks for one explicit nonhyperlinear group; this one is the structural equivalence saying what such a group is equivalent to, and it is proved
  mf-hyperlinear-of-finite-normal-quotient: that transports hyperlinearity across a *finite* normal kernel, a genuine permanence lemma; this claim says that the *arbitrary*-kernel version is not a lemma at all but the whole universal problem
  hyperlinear-nonsofic-group: that is Q3.4, about hyperlinear groups failing soficity; this is about whether nonhyperlinear groups exist at all, a different question with a different answer set
artifacts:
  - GroupApproximation/Sofic/HyperlinearReduction.lean
  - docs/FALSE_PROJECTIVE_UNITARY_GROUP_SHORTCUT.md
---

ESTABLISHED, formalized.  `GroupApproximation/Sofic/HyperlinearReduction.lean`
carries three statements, none of which had a node before 2026-08-18:

```text
all_groups_isHyperlinear_iff_quotient_closed
    (forall H, IsHyperlinear H)
      <-> (hyperlinearity passes to every surjective image)

exists_not_isHyperlinear_iff_exists_hyperlinear_quotient
    (exists H, not IsHyperlinear H)
      <-> (some hyperlinear group has a nonhyperlinear quotient;
           forward, the source may be taken free)

exists_not_isHyperlinear_iff_exists_fg
    (exists H, not IsHyperlinear H)
      <-> (exists a finitely generated such H)
```

The proofs are three lines of content each: every group is a quotient of the
free group on its own underlying type, free groups are sofic hence
hyperlinear, and hyperlinearity is a local property.

## Why this is the useful statement, not a triviality

It fixes the price of every "natural representation" shortcut.  A recurring
proposal is: take a non-Connes-embeddable finite factor `M`, find a group
`G` mapping onto something built from `M`, and conclude that `G` is
nonhyperlinear.  The equivalence says the last step is not a permanence
lemma one may hope to prove in passing -- **unrestricted quotient permanence
is the entire universal-hyperlinearity problem**.  Anything that would
transport Connes embeddability along an arbitrary surjection has already
answered the question.

`docs/FALSE_PROJECTIVE_UNITARY_GROUP_SHORTCUT.md` works one instance out in
full (the abstract group `PU(M)`), and isolates the same boundary in trace
language: hyperlinearity of a discrete group `G` asks for matrix
approximation of its **regular character**

```text
delta_e(g) = 1 if g = e, else 0,
```

while a finite-factor representation supplies instead the **natural
character** `u |-> tau_M(u)`.  There is no general theorem converting the
second into the first.  That gap is what this program means by *trace
selection*, and it is where the `PU(M)`, IRS and full-group routes all stop.

## The idempotent restatement

Fix `G = F_r/N` and pull the regular character of `G` back to `F_r`:

```text
tau_N(w) = 1 if w in N, else 0.
```

Characters of `F_r` multiply pointwise (pointwise product of normalized
central positive-definite functions = character of the tensor product), and
in that semigroup

```text
tau_N^2 = tau_N.
```

Conversely a `{0,1}`-valued character is the indicator of a normal subgroup.
So the normal-subgroup characters are exactly the **idempotents** of the
character semigroup of `F_r`, and by the equivalence above

```text
every group is hyperlinear
  <->  every idempotent character of every free group has matrix microstates.
```

This is strictly weaker than the Connes Embedding Problem, and the
distinction is the reason the universal question survived `MIP^*=RE`.  That
theorem refutes CEP by producing non-embeddable traces; it says nothing about
the idempotent boundary `tau^2 = tau`, and the geometry in which bad traces
populate the interior while every `0/1` idempotent stays embeddable is not
excluded by anything known.  Recorded here so that "CEP is false, so surely
some group is nonhyperlinear" is never used as a step.

See `diracization-gap-equals-nonhyperlinear-group` for what a *mechanism*
mapping general traces onto idempotent ones has to supply, and
`character-diracization-limit` for the canonical such mechanism.
