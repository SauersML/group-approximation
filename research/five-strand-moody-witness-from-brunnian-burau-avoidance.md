---
rg: 2
id: five-strand-moody-witness-from-brunnian-burau-avoidance
kind: route
title: "Five-strand Moody witnesses for Brunnian 4-braids follow from Brunnian Burau avoidance by push-orbit spanning"
target: brunnian-four-braids-have-five-strand-moody-witness
requires:
  - brunnian-four-braids-avoid-burau-kernel
  - moody-witness-exists-iff-outside-burau-kernel
---

- Let `1 ≠ Φ ∈ Brun_4`.
- By `brunnian-four-braids-avoid-burau-kernel`, `ρ_4(Φ) ≠ I`.
- By `moody-witness-exists-iff-outside-burau-kernel`, direction (1) ⇒ (2), there are `y ∈ B_4`
  and `Γ ∈ K_5` with `𝕄_{f(yΦy^{-1})·Γ} ≠ 𝕄_Γ`. This is the target with `k = 1`. ∎

Together with `brunnian-four-braids-avoid-burau-kernel-via-moody`, whose other two prerequisites
are established, this route makes the target and `brunnian-four-braids-avoid-burau-kernel`
equivalent. Proving the witness claim is exactly as hard as the Brunnian Burau statement, and so,
by `burau-four-faithful-iff-faithful-on-brunnian-braids`, as hard as faithfulness of the
4-strand Burau representation.
