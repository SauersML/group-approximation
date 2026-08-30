---
rg: 2
id: nonhyperlinear-from-finite-readable-translate-algebra
kind: route
title: Put the finite-orbit ZPC stabilizer quotient inside one fixed Higman universal group
target: non-hyperlinear-group
requires:
  - perfect-zpc-irs-quantum-gap-game
  - perfect-gap-zpc-has-finite-readable-translate-algebra
  - finite-readable-translate-algebra-groupifies-zpc-gap
  - mikaelian-explicit-higman-embedding
  - local-approximation-properties-are-marked-closed
---

Choose the perfect gap ZPC-IRS strategy with finite full readable translate
algebra.  The finite-orbit compiler constructs, from any atom orbit, a
finitely presented group `K_T` which is not hyperlinear.

The existential choice of the TailoredMIP instance does not prevent an
explicit endpoint.  Fix a computable enumeration of all finite group
presentations and form their recursively presented countable free product.
Each enumerated group embeds as a free factor.  Apply the explicit Mikaelian
Higman embedding once and for all to obtain a fixed finitely presented group
`V` containing that free product.  Thus `V` contains an isomorphic copy of
every finitely presented group, including `K_T`; this is Higman's universal
finitely presented host with a presentation fixed independently of the
unknown witness.

Hyperlinearity is a local approximation property and hence passes to
subgroups by `local-approximation-properties-are-marked-closed`.  If `V` were
hyperlinear, its subgroup `K_T` would be hyperlinear, contradiction.
Therefore the fixed explicit finitely presented group `V` is
nonhyperlinear.
