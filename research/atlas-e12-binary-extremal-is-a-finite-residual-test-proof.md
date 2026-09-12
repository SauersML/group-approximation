---
rg: 2
id: atlas-e12-binary-extremal-is-a-finite-residual-test-proof
kind: route
title: Translate zero-one regular traces into three killed bridges and one surviving bridge
target: atlas-e12-binary-extremal-is-a-finite-residual-test
requires:
  - atlas-a4-finite-quotient-escape-fence
  - atlas-a8-minimal-four-transvection-cycle
artifacts:
  - experiments/atlas_a4_packet_19243_quotient.py
  - experiments/atlas_a8_minimal_transvection_cycle.py
---

In the left regular representation of a finite group `F`, the normalized
trace of a group element is one if the element is identity and zero otherwise.
Therefore

```text
e_ij=1-Re tau(lambda(w_ij))
```

equals zero exactly when `w_ij=1` in `F`, and equals one exactly when its
image is nonidentity.

Hence any finite quotient realizing `(E12-QUOT-2)` kills
`w_01,w_23,w_30`, so it factors through `Q_12`, while its image of `w_12`
survives.  Conversely any finite quotient of `Q_12` in which `w_12` survives
has exactly the four binary energies in `(E12-QUOT-2)` in its regular
representation.  This proves the equivalence with exclusion from the finite
residual.

The finite chart audit is independent.  Exact closure of the three displayed
transvections in `GL_4(F2)` gives `64` elements and excludes `t_12`.  Thus the
fact that all four transvections generate `A8` cannot by itself collapse the
omitted bridge after the other three chart maps are identified.

