---
rg: 2
id: z2-by-f3-bernoulli-lacks-degree-one-cocycle-expansion
kind: claim
title: The w-rigid group Z^2 x| F_3 has a Popa-superrigid Bernoulli shift without degree-one cocycle expansion
distinct_from:
  bernoulli-shifts-have-degree-one-cocycle-expansion: that is the open expansion property for Sp_4(Z), a property (T) group with no HNN splitting; this refutes the same property for a finitely presented w-rigid group whose rigid normal subgroup Z^2 is amenable.
  amenable-hnn-seams-break-bernoulli-degree-one-expansion: that is the general criterion with superrigidity as a hypothesis; this is a concrete w-rigid instance where Popa supplies it.
artifacts:
  - research/artifacts/bernoulli-degree-one-expansion-amenable-seam-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `z2-by-f3-bernoulli-lacks-degree-one-cocycle-expansion-proof`.

**The group.** `Gamma = Z^2 x|_phi F(t_1, t_2, t_3)` with `phi(t_1) = [[1,2],[0,1]]`, `phi(t_2) = [[1,0],[2,1]]`,
`phi(t_3) = [[1,1],[0,1]]`. Presentation: generators `e_1, e_2, t_1, t_2, t_3`; relators `[e_1, e_2]` and
`t_i e_j t_i^-1 = phi(t_i)(e_j)`.

**Statement.**
- `Gamma` is finitely presented and torsion-free, and `(Gamma, Z^2)` has relative property (T), so `Gamma` is w-rigid.
- Every measurable cocycle `Gamma x [0,1]^Gamma -> Z/2` is cohomologous to a homomorphism (Popa).
- Nevertheless the Bernoulli shift `[0,1]^Gamma` has **no** degree-one cocycle expansion with Z/2 coefficients.
  There are `c_n` with relator defects `-> 0` whose distance to every exact cocycle stays `>= kappa/(kappa + 16)`,
  where `kappa` is a Kesten constant of `Z^2 x| F(t_1, t_2)`.
- Equivalently, statement (ii) of `bernoulli-expansion-iff-ultrapower-cocycle-superrigidity` fails for `Gamma`: the
  Bernoulli ultrapower is not Z/2-cocycle superrigid.

**Where Popa's argument stops.** The untwisting over the normalizer uses weak mixing of the rigid normal subgroup.
For amenable `Z^2`, the Bernoulli ultrapower has eigenfunctions for every character, so that step fails there. So
Popa's hypotheses plus finite presentation do not imply degree-one expansion. Any proof for `Sp_4(Z)` must use more,
for instance property (T) of the whole group.

**Model test.**
- **Hypothesis side.** The character `chi = (e_1 -> 1, rest -> 0)` is a homomorphism of `Z^2 x| F(t_1, t_2)`, because
  both Sanov matrices are `= I mod 2`. It does not extend: every homomorphism of `Gamma` kills `e_1`, because `t_3`
  sends `e_2` to `e_1 + e_2`. Replacing `phi(t_3)` by a matrix `= I mod 2` makes `chi` extend, and the construction
  gives nothing.
- **Conclusion side.** The exact analogue is excluded, as it must be: no exact cocycle equals `chi` on the base,
  by Popa plus the spectral gap.
