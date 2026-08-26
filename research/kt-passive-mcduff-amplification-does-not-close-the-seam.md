---
rg: 2
id: kt-passive-mcduff-amplification-does-not-close-the-seam
kind: claim
title: Passive McDuff amplification does not close the Kun--Thom normalization seam
distinct_from:
  kt-internal-c-seam-has-a-kazhdan-gap: that treats finite matrix amplification; this treats tensoring by an arbitrary finite tracial spectator, including the hyperfinite factor used in a McDuff embedding.
  kt-extrinsic-c-seam-has-a-finite-satisfiability-criterion: that permits an arbitrary enlarged relative commutant with nontrivial Gamma dynamics; this rules out only the natural construction where the extra central-sequence factor is dynamically passive.
  kt-one-compressor-and-sl3-normalizer-lifts-paste: that constructs the CE amalgam by a free product; this proves that merely tensor-amplifying that construction cannot perform the quotient-kernel correction.
---

**ESTABLISHED MCDUFF FIREWALL.**  Let `Q` be any finite tracial von Neumann
algebra and tensor the canonical AFP paste with `Q`, embedding all actor and
base unitaries as `x tensor 1`.  Then for every
`xi in L^2(L(N) tensor Q)`,

```text
max_(gamma in KazhdanSet)
 ||xi(v_gamma tensor 1)-(rho_gamma tensor 1)xi||_2
 >= kappa ||xi||_2.                                    (KPM1)
```

In particular no unitary in the amplified relative commutant closes the
`C`-normalization seam.  This applies to `Q=R`: placing the AFP embedding in
one tensor factor of a McDuff target and taking a correction from an
independent hyperfinite central-sequence factor does nothing.

The conclusion is deliberately scoped.  An embedding into `R^omega` can
create an extrinsic relative commutant on which the two Gamma actions are
not the passive tensor action.  A positive construction must do exactly
that: supply a new Gamma bimodule containing the missing invariant vector.
McDuffness, diffuseness, or a freely available spectator factor by itself is
not enough.

DERIVATION
kt-passive-mcduff-seam-gap-proof
