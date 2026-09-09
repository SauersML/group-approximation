---
rg: 2
id: contragredient-period-two-wedge-excludes-corrected-deletion-splits
kind: route
title: Apply the inverse-adjoint automorphism and verify a binary period-two kernel
target: omega-corrected-deletion-has-contragredient-kernel
requires:
  - two-sided-omega-square-deletion-candidate-has-no-split
artifacts:
  - research/artifacts/kaplansky-contragredient-period-two-kernel-excludes-omega-split-2026-09-08.md
  - research/artifacts/kaplansky-two-sided-omega-square-period-four-kernel-2026-09-08.md
---

The Leavitt anti-involution swaps s_i and t_i. Composing it
with inversion gives a genuine unit-group automorphism theta,
which fixes the source and target projectors and sends
T_z^epsilon to T_(z^2)^(-epsilon).

For the inverse actor and z=omega^2, take the normalized source

    X=(beta+omega^2 alpha) tensor beta,
    Y=(alpha+omega^2 beta) tensor beta,
    alpha=(01)^infinity, beta=(10)^infinity.

The full plus and minus exterior coordinates reduce respectively
to v wedge omega^2v and v wedge v, with v=alpha+beta.
Scaling by omega^2 and applying the exact source normalization
gives the Frobenius-fixed actual source tensors

    X_T=beta tensor (alpha+omega beta), Y_T=X_T^sigma.

Their binary expansion has nine distinct wedges and lies in
im(f_0). Thus no left inverse exists for T_(omega^2)^(-1),
and the automorphism excludes T_omega^(+1). The earlier
period-four kernel and its automorphic image exclude the
other two parameter/orientation choices.

This preserves the proved ordinary exterior-square injectivity
as a separate necessary test that this candidate passes. It
does not assert surjectivity of that map or reverse its source
and target projectors.
