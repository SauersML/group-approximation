---
rg: 2
id: property-t-free-seed-via-lifted-thompson-t
kind: route
title: The lifted Thompson group T-bar is the seed as soon as every corona representation kills its central translation
target: property-t-free-torsion-free-fp-non-mf-seed
requires:
  - lifted-thompson-t-is-not-mf
  - lifted-thompson-t-mf-radical-dichotomy
  - universal-mf-quotient
---

**Proof.**  Take `E = T̄` and `d = z`.
- By item 4 of `lifted-thompson-t-mf-radical-dichotomy`, `E` is finitely
  presented and torsion-free.
- By `lifted-thompson-t-is-not-mf`, `d in Rad_MF(E)`.  Also `d != 1`, since
  `z(0) = 1`.
- By `universal-mf-quotient`, `E` is not MF.

No step uses Property `(T)`.  The dichotomy is proved from simplicity of `T`,
perfectness of `T̄`, the dilation endomorphism and the rotation-centralizer
quotients.  The hole is required to avoid Property `(T)`.  So the output
satisfies the no-`(T)` clause of `property-t-free-torsion-free-fp-non-mf-seed`. ∎

## What this route changes

- **One hole instead of two.**  Items 2 and 3 of the dichotomy show that the
  single hole `lifted-thompson-t-is-not-mf` also forces `Rad_MF(V) = V`.
  That is the only hole of the wave-15 Thompson-`V` route to the
  binary-Leavitt endpoint, posted on the live bus as thompson-v-is-not-mf.
  So along this route the two deep inputs of
  `property-t-free-manuscript-results` share one prerequisite:

  ```text
  z in Rad_MF(T-bar)
     => T-bar full radical          (dichotomy, items 1-2)
     => torsion-free f.p. seed      (this route)
     => Rad_MF(T) = T => Rad_MF(V) = V
                                    (dichotomy, item 3)
     => binary-Leavitt endpoint     (V-route, live bus wave 15)
  ```

- Before this, the torsion-free seed had three open cones:
  - {Leavitt collapse, `full-mf-radical-abelianized-cover-is-not-mf`};
  - the Higman cone {`(TPC)`, `(CGC)`};
  - the virtual-torsion corner.

  None of them also settles the Leavitt endpoint.
- **Cost.**  The hole is at least as strong as "Thompson's `T` is not MF".  It
  is refuted by an MF model of `T`, of any single rotation centralizer
  `C_T(r_k)`, or of `2V`.  It is not a reformulation of the endpoint, since
  it names a specific group.
- **No central shortcut.**  One might hope that `z` could be radical while
  `T̄` is otherwise visible.  The dichotomy rules this out, and so no proof
  can produce `z in Rad_MF(T̄)` without also proving that `T` is not MF.
