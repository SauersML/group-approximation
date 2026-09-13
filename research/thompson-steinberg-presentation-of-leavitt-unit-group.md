---
rg: 2
id: thompson-steinberg-presentation-of-leavitt-unit-group
kind: claim
title: The binary Leavitt unit group is Thompson's V plus one leaf transvection and one relator per cone configuration
distinct_from:
  leavitt-unit-group-steinberg-weyl-presentation: that is a seven-generator presentation built on S_5 acting on a five-leaf chart; this targets three generators, with Thompson's V replacing S_5 and letters absorbed into cone refinements.
  leavitt-unit-group-finitely-presented: that is bare finite presentability; this is a specific presentation shape whose relators are indexed by V-orbits of cone configurations.
---

**OPEN.** Let `V <= L^x` be Thompson's group (units `sum_i S[r_i]T[d_i]` for complete prefix
codes `(d_i)`, `(r_i)`) and `u = 1 + S[00]T[01]`. For disjoint cones `alpha, beta` whose union
is not everything, put `T(alpha,beta) = g u g^-1`, where `g in V` maps `00w -> alpha w` and
`01w -> beta w`.

**Claim.** `L^x` is presented by: generators of `V` together with `u`; a finite presentation
of `V`; `u^2`; `[u,h]` for `h` in a generating set of the subgroup of `V` fixing the cones `00`
and `01` pointwise (a copy of `V` acting on the cone `1`, so two relators); and one relator for
each `V`-orbit of cone configurations occurring in the families (L), (B), (C), (P), (Q) of
`leavitt-unit-group-steinberg-weyl-presentation`.

Target size: three generators (two for `V`, Bleak--Quick), and far fewer relators than sixty.
The letters `e, f, E, F` become refinements of cones, so the 25 coefficient pairs collapse to a
few configuration types.

## Attempts

1. **Design (2026-09-12, ex-free-objects).** The commutator relators give well-defined
   `T(alpha,beta)`: two choices of `g` differ by an element fixing `00` and `01` pointwise. Any
   `V`-identity used holds automatically, since `V`'s generators satisfy a complete
   presentation of `V`, and such identities can be checked exactly in `L^x`. Completeness would
   follow by Tietze from the sixty-relator presentation. Map `c, t` to `V`-words and `y_a` to
   `T(00 a, 01)` or `T(00, 01 a)`. Each of the sixty relators must then be derived from the
   configuration relators, transported by `V`. The (B) disjoint family, for example, is one
   configuration: four pairwise disjoint cones with nonempty complement.
   *Stops at:* the configuration census and the exact Bleak--Quick relators (not yet read from
   the source). Nothing is computed yet.
