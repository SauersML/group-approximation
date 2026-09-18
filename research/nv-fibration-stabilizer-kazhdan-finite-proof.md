---
rg: 2
id: nv-fibration-stabilizer-kazhdan-finite-proof
kind: route
title: The base map to |I|V has finite Kazhdan image, and the finite-index kernel lies in a finite product of copies of |J|V whose Kazhdan subgroups are finite by induction
target: kazhdan-subgroups-of-nv-fibration-stabilizers-are-finite
requires:
  - thompson-v-has-haagerup-property
  - kazhdan-subgroups-of-brin-thompson-groups-are-finite
artifacts:
  - research/artifacts/kazhdan-nv-displacement-gap-2026-09-17.md
---

Complete proof: artifact Section D. Imports: countable Kazhdan groups are finitely
generated; quotients and finite-index subgroups of Kazhdan groups are Kazhdan.

Induction on `n`, with `n = 1` from `thompson-v-has-haagerup-property`.

1. `g -> v` is a homomorphism `Stab_I -> |I|V` (on each piece of a brick partition of `g`,
   `v` is the prefix replacement of the `I`-words). The image of Kazhdan `K` is Kazhdan
   in `|I|V`, finite by induction; the kernel `K_1` has finite index and is Kazhdan.
2. A kernel element has the identity on `I`-words on each piece, so its fibre maps
   `φ_a ∈ |J|V` are constant on bricks of shape `D_g·1` in `C^I`. A finite generating set
   of `K_1` gives one brick partition `P` of `C^I`, and `K_1 <= Π_{B∈P} |J|V`.
3. Each factor image is a Kazhdan subgroup of `|J|V`, finite by induction, so `K_1` and
   `K` are finite. Conjugation preserves both (T) and finiteness.

**2026-09-18, referee: the induction is circular, and the second prerequisite was added for
it.** The statement being inducted is "Kazhdan subgroups of `Stab_I <= nV` are finite", but
Step 1 ("the image of `K` is a Kazhdan subgroup of `|I|V`, finite by induction") and Step 3
("each coordinate projection of `K_1` is a Kazhdan subgroup of `|J|V`, finite by induction")
invoke the strictly stronger statement "every Kazhdan subgroup of `mV` is finite" for
`m = |I|, |J| < n`. That is `kazhdan-subgroups-of-brin-thompson-groups-are-finite`, which is
OPEN for every `m >= 2`; only `m = 1` is available, from Farley. So the induction closes at
`n = 2` (where `|I| = |J| = 1`) and Step 3 first fails at `n = 3`.

The claim is not merely unproved but as strong as that open problem. For `n = 3`, `I = {1}`,
`J = {2,3}`, `Stab_{{1}}` contains `{g : g(x_1,x_2,x_3) = (x_1, psi(x_2,x_3)), psi ∈ 2V} = 1 x 2V`
(take `v = id`). So the statement at `n = 3` literally asserts that every Kazhdan subgroup of
`2V` is finite.

The other steps hold: `g -> v` is a well-defined homomorphism into `|I|V`; `φ_a ∈ |J|V` and is
constant on bricks of shape `D_g`; maps constant on a common refinement form a subgroup, so
`K_1 <= Π_{B∈P} |J|V`; (T) passes to quotients and finite-index subgroups; countable Kazhdan
groups are finitely generated; conjugation preserves (T) and finiteness. The defect is solely
the induction hypothesis. Compare the sibling
`kazhdan-subgroups-of-fibred-subgroups-of-nv-are-finite`, which treats the same group and
states the correct conditional form.
