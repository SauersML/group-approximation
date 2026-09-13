---
rg: 2
id: finite-index-injections-into-braid-quotients-are-geometric
kind: claim
title: For n >= 4, every injection of a finite-index subgroup of B_n/Z(B_n) into B_n/Z(B_n) is conjugation by an extended mapping class
distinct_from:
  braid-groups-on-four-or-more-strands-are-not-self-similar: that is the self-similarity obstruction deduced from this rigidity; this is the imported rigidity theorem itself, about injective virtual endomorphisms of B_n modulo its center.
---

**ESTABLISHED (literature import).** Let `n >= 4`. Put
`Gamma = Mod^±(S_(0,n+1))`, the extended mapping class group of the sphere
with `n+1` punctures, and view `Q = B_n / Z(B_n)` as the finite-index subgroup
of orientation-preserving mapping classes fixing one puncture (`B_n / Z =
Mod(D_n)`, Bell–Margalit arXiv:math/0403145, §1).

Then for every finite-index subgroup `Lambda <= Q` and every injective
homomorphism `psi : Lambda -> Q` there is `phi` in `Gamma` with
`psi(x) = phi x phi^-1` for all `x` in `Lambda`.

It follows from the surface theorem because `Lambda` has finite index in
`Gamma`, and `psi` composed with `Q <= Gamma` is an injection into `Gamma`.
The surface `S_(0,n+1)` with `n+1 >= 5` is not one of the exceptional surfaces.
Source and exact statements: `finite-index-injections-into-braid-quotients-citation`.

The hypothesis `n >= 4` is sharp for this form. `B_3 / Z = PSL_2(Z)` is virtually
free, and conjugation by `diag(2,1)` on `Gamma_0(2)` is an injection that is
not a conjugation inside `PGL_2(Z)` (Korkmaz: `S_(0,4)` is exceptional).
