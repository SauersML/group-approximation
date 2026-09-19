---
rg: 2
id: permanence-closure-radical-witnesses-have-lef-kernels-proof
kind: route
title: Transport LEF from the permanence closure to the kernel, then read off MF, the descent branch and the finite residual
target: permanence-closure-radical-witnesses-have-lef-kernels
requires:
  - kazhdan-groups-in-sofic-permanence-closure-are-lef
  - lef-implies-operator-mf
  - mapping-torus-mf-radical-descends-through-kernel-radical
  - mapping-torus-mf-radical-lies-in-finite-residual
  - finitely-presented-lef-groups-are-residually-finite
  - mf-positive-controls
---

Fix an exact witness `(G,K)`: `G = K ⋊_φ Z`, `K ≠ 1` finitely generated Kazhdan, and
`Rad_MF(G) = K × {0}`.

**(PW1).**
- `G ∈ 𝒫 ⇒ K ≤ G ∈ 𝒫`: trivial, since `K` is a subgroup of `G`.
- `K ≤ H ∈ 𝒫 ⇒ K LEF`: this is `kazhdan-groups-in-sofic-permanence-closure-are-lef`, because `K` is a
  finitely generated Kazhdan subgroup of a member of `𝒫`.
- `K LEF ⇒ G ∈ 𝒫`: `K` lies in the base of `𝒫`. `G` is an extension `1 → K → G → Z → 1` with `Z`
  amenable, so `G ∈ 𝒫` by the amenable-quotient-extension operation (O4).

None of these steps uses exactness.

**(PW2).**
- `K` is LEF, so it is operator-MF by `lef-implies-operator-mf`.
- The identity `K → K` is therefore an injective map to an MF group, and `Rad_MF(K) = 1`.
- In the notation of `mapping-torus-mf-radical-descends-through-kernel-radical` this gives `R = 1` and
  `Q = K`. Branch (DI) would need `R = K ≠ 1`, so the witness is of type (DX).
- Suppose `[φ]` had finite order in `Out(K)`. Then (MD5) would give `Rad_MF(G) = R × {0} = 1`,
  contradicting `Rad_MF(G) = K × {0} ≠ 1`. So `[φ]` has infinite order.

**(PW3).**
- By (FRB2) of `mapping-torus-mf-radical-lies-in-finite-residual`, `K` has no nontrivial finite quotient.
- Suppose `K` were finitely presented. It is LEF, so it would be residually finite by
  `finitely-presented-lef-groups-are-residually-finite`. A residually finite group with no nontrivial
  finite quotient is trivial, which contradicts `K ≠ 1`.
- Now suppose `G` is finitely presented. If `G` were LEF, it would be residually finite by the same
  theorem, hence MF by `mf-positive-controls`, so `Rad_MF(G) = 1`, again a contradiction. So `G` is not
  LEF, although `G ∈ 𝒫`.
- The finite automorphic presentation clause is the translation of finite presentation of `G` given in
  `fp-mapping-torus-iff-finite-automorphic-presentation`. It is recorded for orientation and is not used
  above.

**(PW4).** (EKL1) asserts that `Rad_MF(K ⋊_φ Z) = K × {0}` forces `K = 1` or `K` non-LEF, for every
finitely generated Kazhdan `K`. The witness has `K ≠ 1` and `K` LEF, so it refutes (EKL1).

**Complementary case.**
- If `K` is not LEF, then by (PW1) no member of `𝒫` contains `K`, and in particular `G ∉ 𝒫`.
- For a flagship witness `G` is sofic, so `K` is sofic, being a subgroup of `G`.
- Every permanence theorem listed in the claim produces a member of `𝒫` from amenable and LEF inputs.
  Their composites therefore cannot certify soficity of `G`.

**Consequences.**
- *Consequence 1.* (EKL1) quantifies over all finitely generated Kazhdan kernels. By (PW1), "some exact
  witness has LEF kernel" is equivalent to "some exact witness has `G ∈ 𝒫`".
- *Consequence 2.* A kernel with `Rad_MF(K) = K ≠ 1` contradicts (PW2), so it is not LEF, and by (PW1)
  it lies in no member of `𝒫`.
- *Consequence 3.* This is the route `torsion-free-sofic-exact-mf-radical-via-lef-kernel`. Soficity there
  is supplied by `sofic-kernel-amenable-quotient-permanence`, because LEF groups are sofic: a local
  embedding into a finite `F` followed by the left regular action of `F` is an exact sofic
  approximation on the window.
- *Consequence 4.* Given a flagship witness, `K` is torsion-free (because `G` is). By
  `fp-mapping-torus-iff-finite-automorphic-presentation`, `φ` has a finite automorphic presentation.
  So a witness with LEF kernel satisfies the OPEN claim of consequence 3, and every other witness is
  (W_out). The converse is the route.

**Model test.** Each model group is LEF, or a finite product of LEF groups with `Z`, so each lies in
`𝒫`. Its stated properties are the cited established claims.
