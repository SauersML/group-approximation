---
rg: 2
id: brunnian-burau-kernel-mod-cyclotomic-products-nontrivial
kind: claim
title: "For every product F of cyclotomic polynomials avoiding Phi_3, some nontrivial Brunnian 4-braid has Burau matrix congruent to I mod F, so no fixed-modulus Moody certificate can prove the witness claim"
distinct_from:
  burau-minus-one-kernel-meets-brunnian-four-braids: that claim is the single case F = t+1; this claim covers every product of cyclotomic polynomials Phi_d with d != 3, to any multiplicity, and adds the uniform Moody obstruction
  parity-correcting-push-fails-for-a-brunnian-four-braid: that claim kills parity-clean intersection counts, which see only t = -1; this claim kills every certificate that reads Moody polynomials modulo a fixed cyclotomic product avoiding Phi_3
  brunnian-four-braids-have-five-strand-moody-witness: that claim is the existence of an exact witness; this claim shows that the witness cannot be detected modulo any fixed such F, and leaves that claim open
artifacts:
  - experiments/moody-witness-equivalence-2026-09-17/cyclotomic_jets.py
  - experiments/moody-witness-equivalence-2026-09-17/cyclotomic_jets.log
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

Let `F = ∏_{d ≠ 3} Φ_d^{m_d}` be any finite product of cyclotomic polynomials not divisible by
`Φ_3 = t² + t + 1`.

**Claim.**
1. **(Kernel mod `F`.)** There is `1 ≠ X_F ∈ Brun_4` with `ρ_4(X_F) ≡ I mod F·(t − 1)`.
2. **(Uniform Moody obstruction.)** For every `k ≥ 1`, every conjugate `Φ_0` of `X_F^k` in `B_4`,
   and every `Γ ∈ B_5` (in particular every `Γ ∈ K_5`), `𝕄_{f(Φ_0)·Γ} ≡ 𝕄_Γ mod F`. Notation is
   as in `brunnian-four-braids-have-five-strand-moody-witness`, and the congruence holds in both
   composition orders.

**What this kills.** Consider any certificate for `brunnian-four-braids-have-five-strand-moody-witness`,
or any other Moody-type witness for Brunnian 4-braids, that concludes `𝕄_{f(Φ_0)Γ} ≠ 𝕄_Γ` by
exhibiting a nonzero residue of the difference in `Z[t^{±1}]/(F)`, for one `F` fixed in advance
and independent of `Φ`, with `Φ_3 ∤ F`. Every such certificate fails at step "the residue is
nonzero" on `Φ = X_F`, whatever conjugate, power or push map it picks. The invariant is the
residue of `𝕄` modulo `F`. This class includes:
- parity-clean counts, which see `t = −1` only (`d = 2`, `m = 1`);
- evaluations at primitive `d`-th roots of unity for `d ≠ 3`, together with finitely many
  derivatives there;
- intersection data read in a finite cyclic cover of order `N` with `3 ∤ N`, that is modulo
  `t^N − 1`;
- all combinations of these, also after further reduction modulo a prime `p`.

A proof of the witness claim must therefore let the modulus depend on `Φ` (for instance
`F = ∏_{d | N} Φ_d` with `N` growing with the length of `Φ`), work exactly over `Z[t^{±1}]`, or
use `Φ_3`.
