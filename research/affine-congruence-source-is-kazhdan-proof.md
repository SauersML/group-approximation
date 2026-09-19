---
rg: 2
id: affine-congruence-source-is-kazhdan-proof
kind: route
title: Add the finite-index Kazhdan certificate to the bare affine datum
target: affine-congruence-source-is-kazhdan
requires:
  - concrete-compression-source
  - literal-kazhdan-clifford-inputs
artifacts:
  - GroupApproximation/Sofic/LiteralAffineCongruenceKazhdan.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceTorsionFree.lean
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
---

## Why sufficient

`concrete-compression-source` already supplies, unconditionally and in Lean,
everything about the level-three affine source except property (T): the
injective dilation endomorphism, the omitted translation, the centralized
witness, the Britton-nontrivial marked commutator, torsion-freeness through
`hnn-torsion-theorem`, and finite presentation.

`literal-kazhdan-clifford-inputs` supplies property (T) of the affine **base**,
with a rational spectral gap of at least `1/500` certified against the literal
displayed relators rather than an abstract isomorphic presentation.

The only step between them is finite-index permanence.  `levelThree` is the
preimage of `Gamma(3)` under the linear-part homomorphism, so it is normal of
finite index `[SL_3(Z) : Gamma(3)]` in the base and contains every translation;
property (T) passes to finite-index subgroups, and finite presentation passes
to finite-index subgroups as well.  In Lean this is exactly

```text
p_hasKazhdanPropertyT =
  FiniteIndex.hasKazhdanPropertyT_of_finiteIndex levelThree
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT
```

with `p_isFinitelyPresented` the parallel statement.  Torsion-freeness of `P`
is independent of both and is `p_isPowerTorsionFree`, resting on Minkowski's
lemma for `Gamma(3)` (`Algebra/CongruenceTorsionFree.lean`) plus the elementary
semidirect-product argument: `(g,v)^n = 1` forces `g = 1`, then `n v = 0`.

Nothing here is a restatement of either prerequisite.  Both prerequisites can
hold with the level-three subgroup failing (T) — that is precisely what happens
for a subgroup of infinite index — so the finite-index step carries real
content, and it is the step that converts a bare compression datum into an
input the normal-Kazhdan detector accepts.

## Modulus

The dossier of the artifact dilates by `3` and gets index `27`; the certified
repository instance dilates by `2` and gets index `8`.  Any `m >= 2` works and
no downstream node depends on the choice, so the two are the same claim.
