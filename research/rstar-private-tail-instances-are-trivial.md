---
rg: 2
id: rstar-private-tail-instances-are-trivial
kind: claim
title: One-shared-three-private R-star syntax is always classically satisfiable
distinct_from:
  rstar-private-tail-fiberwise-cap-collapse: that modifies a supplied perfect representation under the private-tail hypothesis; this shows the same hypothesis destroys CSP soundness before operator theory enters.
  rstar-sunflower-neighborhoods-have-full-links: that computes extension links for one- and two-coordinate petals; this treats an entire instance whose every constraint has at most one nonprivate coordinate.
  culf-mastel-rstar-fixed-language-gap-is-published: that gives a hard fixed-language family with shared target variables; this rules out identifying that family with the private-tail syntax.
---

**ESTABLISHED SYNTAX FIREWALL.**  Let a finite `R_*` instance have at most
one variable in each context which occurs in any other context, with all
remaining coordinates occurrence-private.  Then every assignment to the
shared variables extends context by context to a classical satisfying
assignment of the whole instance.

Indeed every coordinate projection of `R_*` is surjective.  In the first
coordinate this is witnessed, for example, by

```text
0001 in R_* with x_1=0,       1011 in R_* with x_1=1.   (PTS1)
```

After fixing the sole shared coordinate of a context, choose any allowed
tuple in that fibre and assign its remaining values to the private variables.
No such choice can conflict with another context.  A context with no shared
coordinate is handled by choosing any member of `R_*`.

Thus this syntax has classical value one for every input and cannot carry a
nonhalting soundness gap.  Any hard fixed `R_*` reduction must reuse target
variables inside a gadget or place at least two nonprivate variables in some
target context.
