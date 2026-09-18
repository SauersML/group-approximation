---
rg: 2
id: out-free-double-coset-finite-subgroups-have-dense-limit-sets
kind: claim
title: Every subgroup of Out(F_n), n at least three, with finitely many double cosets has limit set in the free factor boundary meeting every fully irreducible fixed pair, and densely so; finite generation is the only remaining obstruction to type (A) actions
requires:
  - limit-set-escaping-forces-infinitely-many-double-cosets
  - out-free-pair-finite-stabilizers-contain-fully-irreducibles
distinct_from:
  virtually-cyclic-out-free-subgroups-have-infinite-double-cosets: that excludes virtually cyclic subgroups by an axis argument; this excludes every subgroup whose limit set misses a fully irreducible fixed pair, which contains that case (limit set φ^±) and the bounded case (empty limit set).
  out-free-groups-satisfy-boone-higman: that is the open target; this does not decide whether Out(F_n) has a type (A) action, and records why no argument ignoring finite generation can.
---

**ESTABLISHED** for items 1 and 3 (lane proof; not reviewed; no priority
claimed). Item 2 depends on a cited standard fact.
- **Cited inputs, not read at source:**
  - Bestvina–Feighn arXiv:1107.3308: `FF_n` is hyperbolic, and fully
    irreducibles act loxodromically and are WPD.
  - Hull–Osin, "Transitivity degrees of countable groups and acylindrical
    hyperbolicity".
  - BFFHZ Remark 2.5, quoted on the root.
  - The double density of loxodromic fixed pairs for non-elementary actions.

**Statement.** Let `n ≥ 3`, `G = Out(F_n)` and `H ≤ G`.
1. **Every fixed pair.** If `H\G/H` is finite, then `Λ_H ⊆ ∂FF_n` contains `φ^+`
   or `φ^−` for every fully irreducible `φ`. The same holds in `FS_n`, or any
   hyperbolic `Out(F_n)`-graph, for its loxodromics.
2. **Density.** If `H\G/H` is finite, then `Λ_H` is dense in `∂FF_n`.
3. **Finite generation is essential.** Hull–Osin actions give point stabilizers
   of infinite index with exactly two double cosets. So no argument that ignores
   finite generation can show that `Out(F_n)` has no type (A) action.

**Proofs.**
- **Item 1** is the contrapositive of
  `limit-set-escaping-forces-infinitely-many-double-cosets`, for `X = FF_n`.
- **Item 2.**
  - The action of `G` on `FF_n` is cobounded and non-elementary. So its limit
    set is all of `∂FF_n`.
  - By double density, if the closure `Λ̄_H` misses a nonempty open set `U`,
    there is a fully irreducible with both fixed points in `U`. That
    contradicts item 1.
  - This is the one step that uses the cited density fact.
- **Item 3.**
  - `Out(F_n)` is acylindrically hyperbolic, since it has a WPD loxodromic on
    `FF_n`, and its finite radical is trivial. Hull–Osin then give a faithful
    highly transitive action.
  - BFFHZ Remark 2.5 records this for `Out(F_n)`.
  - Its point stabilizer `H` has infinite index and `H\G/H = {H, G∖H}`.

**Recovered cases.**
- **Bounded orbits,** with `Λ_H = ∅`: free factor stabilizers, non-filling
  classes and points of Outer space.
- **Virtually cyclic subgroups,** with `Λ_H = {φ^±}`: pick an independent `χ`.

**Verdict on the question "does Out(F_n) have a type (A) action?"**
- **Not decided.**
- **What any stabilizer must be.** Every hypothesis-free geometric obstruction
  now reduces to this: a type (A) point stabilizer `H` must be finitely
  generated, of infinite index, not commensurated, and have dense limit set in
  `∂FF_n`. It must also avoid every surface peripheral-structure stabilizer.
- **The two remaining directions:**
  - **Refute:** show that a finitely generated subgroup of `Out(F_n)` with
    finitely many double cosets has finite index. That would be a new rigidity
    theorem, and it must use finite generation (item 3).
  - **Construct:** a finitely generated subgroup with dense limit set and
    finitely many double cosets. A Dehn-filling-type finitely generated
    replacement for the Hull–Osin stabilizer, still unconstructed, is the
    natural attempt.
