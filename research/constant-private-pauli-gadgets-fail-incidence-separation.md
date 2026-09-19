---
rg: 2
id: constant-private-pauli-gadgets-fail-incidence-separation
kind: claim
title: Private constant-size Pauli gadgets do not repair mixed-incidence separation
distinct_from:
  finite-offset-pauli-rectangles-violate-relative-gr-sixth: that treats one direct pair edge and obtains a repeated pair/equality turn; this treats arbitrary finite-template private two-terminal subdivisions, including Magic-Square and Heisenberg sign gadgets.
  complete-pauli-rectangles-defeat-three-p-balance: that treats the unmodified four-pair contour; this proves bounded subdivisions leave the ordinary imbalance and also violate the relative one-sixth condition.
  sparse-ports-either-lose-soundness-or-repeat-relative-pieces: that inserts growing equality-only regions; this allows private internal pair vertices but proves constant size and finitely many templates cannot make them unique.
---

Consider the occurrence-cloud reduction of growing complete logical Pauli
tables.  Give every logical pair incidence private endpoint occurrences and
replace that incidence by a two-terminal gadget chosen from a fixed finite
list of finite labeled templates.  Assume:

1. the X and Z equality clouds are unchanged;
2. a designated reduced terminal path in a template has relative length
   `ell>=1` over `H_X*H_Z*F(P)` and robustly decodes the required endpoint
   commute/anticommute sign on the same Hilbert space;
3. all edge labels and all gadget templates come from fixed finite sets.

Then this replacement cannot satisfy the mixed-contour hypotheses of either
`relative-c-sixth-pauli-incidence-labeling` or
`balanced-pauli-incidence-labeling`.

For the relative statement, finitely color every logical edge by its oriented
terminal-path template.  Every sufficiently large finitely colored complete
bipartite graph contains a monochromatic `K_(2,2)`.  Its four private gadgets
close through two X-equality paths and two Z-equality paths.  After equality
paths are contracted to peripheral syllables, the resulting contour has
relative length at most

```text
4 ell + 4.                                                   (CPG1)
```

If the contour is not essential and cyclically reduced, the target labeling
already fails.  Otherwise the same oriented terminal word occurs at two
distinct gadget immersions, so it is a graphical piece of length `ell`.  For
`ell>=2`, free-product `Gr'(1/6)` would require

```text
ell < (4 ell + 4)/6,
```

which is equivalent to `ell<2`, a contradiction.  When `ell=1`, the repeated
terminal/peripheral turn is a piece of length two on a contour of length at
most eight, exactly the obstruction in
`finite-offset-pauli-rectangles-violate-relative-gr-sixth`.

Making the sign local by a central square, a Magic-Square cell, or a finite
Heisenberg packet does not change the conclusion.  If its bounded contour is
one of the new graphical relators, its repeated private copies themselves
create a repeated piece.  If the contour is instead absorbed into a fixed
sign-safe base group, it contracts to one bounded pair syllable and returns
to the `ell=1` finite-offset obstruction.  Thus "private" is semantic
bookkeeping, not relative-label uniqueness.

The ordinary balanced-Greendlinger route also survives no such subdivision.
All four gadget contributions are bounded by one constant.  Choosing, as in
`complete-pauli-rectangles-defeat-three-p-balance`, one equality gap of length
one and an opposite gap of length tending to infinity still produces an
interval containing all but `O(1)` of the contour.  Its length fraction tends
to one.

The gadget may therefore preserve the Pauli dimension witness perfectly;
what it cannot preserve is the required Cayley separation.  Any remaining
mixed-incidence replacement must use unbounded, occurrence-distinguishing
structure together with a uniform same-Hilbert-space decoder, or must replace
the complete logical incidence table itself by a sparse robust dimension
witness.  Constant-size private subdivision is closed.
