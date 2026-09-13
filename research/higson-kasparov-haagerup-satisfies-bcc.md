---
rg: 2
id: higson-kasparov-haagerup-satisfies-bcc
kind: claim
title: a-T-menable groups satisfy Baum--Connes with coefficients, and some are not exact
distinct_from:
  amenable-kernel-bc-transfer-and-ktop-half-exactness: that imports the Chabert--Echterhoff transfer along amenable normal subgroups and half-exactness of K^top; this imports the Higson--Kasparov isomorphism theorem for a-T-menable groups together with Osajda's non-exact Haagerup groups.
  a-t-menable-groups-have-no-rigid-compression-defect: that is about rigid pairs and compression defects inside a Haagerup group; this is about the reduced assembly map with coefficients for a Haagerup group.
---

**ESTABLISHED (citation)** by `higson-kasparov-haagerup-satisfies-bcc-citation`.

Groups are countable and discrete.

1. **Higson--Kasparov.** If `G` is a-T-menable (equivalently, has the Haagerup
   property), then `G` satisfies the Baum--Connes conjecture with coefficients:
   for every separable `G`-C*-algebra `A` the reduced assembly map

   ```text
   mu_(G,A) : K^top_*(G; A) -> K_*(A ⋊_r G)
   ```

   is an isomorphism, in both degrees. (In fact the strong Baum--Connes
   conjecture holds, which is strictly stronger.)

2. **Non-exactness is compatible with a-T-menability.** There exist finitely
   generated groups that are a-T-menable but **not exact** (no property A).
   Osajda's groups act properly on CAT(0) cube complexes, hence are a-T-menable,
   while the isometrically embedded family of relators has no property A, so the
   group is coarsely non-amenable. For a countable discrete group, property A is
   equivalent to exactness (Ozawa), so these groups are non-exact.

3. **Consequence.** The class of groups satisfying Baum--Connes with coefficients
   (BCC) is strictly larger than the class of exact groups: it contains non-exact
   a-T-menable groups. So "BCC holds for `G`" does not force `G` exact, and
   "`G` non-exact" does not force any coefficient failure for `G`.

**Model test.** Amenable groups are a-T-menable and exact; the two conditions are
independent in general, and item 2 realizes one non-implication with a single
family of examples.

**Why it matters here.** `k-inexact-module-triple-refutes-trivial-coefficient-bc`
turns a module K-defect over `G` into a trivial-coefficient counterexample. A
K-defect requires a coefficient failure of `G` itself (see
`bcc-groups-have-k-exact-module-triples`). This node supplies the exact class
that has **no** such failure, and shows that class already contains non-exact
groups, so non-exactness alone is not enough for the module route.
