---
rg: 2
id: finite-index-in-a-kernel-fg-near-host-passes-both-germ-gates
kind: claim
title: A near shift group of finite index in a finitely presented near group with finitely generated near-index kernel passes both germ gates
distinct_from:
  mz-envelope-fp-forces-two-sided-fg-near-index-kernel: that proves the two conditions (R_nu finitely presented, ker eta finitely generated) are necessary for the Mallery-Zaremsky germ group; this gives a sufficient way to verify both at once, by locating R_nu with finite index in a known host.
  a5-arithmetic-near-group-obeys-parity-charge-constraint: that places one explicit near group inside the host B_0, where it turned out to have infinite index; this says what finite index would have bought.
artifacts:
  - research/artifacts/gq-bh-bh-shell-arith-lsf-mixed-radix.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no novelty claimed).

Let `P` be infinite and finitely generated, `nu: P -> N` a bijection, and
`R_nu = <lambda(P), s>` the near shift group with near index `eta`. Suppose
`R_nu <= H <= NearSym(N)` where

- `H` is finitely presented,
- the near index `eta_H: H -> Z` has finitely generated kernel, and
- `[H : R_nu] < infinity`.

Then `R_nu` is finitely presented and `ker(eta)` is finitely generated. So:

1. The Mallery-Zaremsky germ group `E_nu(P)/FSym(N)` is finitely presented, by
   `mz-envelope-fp-forces-two-sided-fg-near-index-kernel` (its displayed
   equivalence), i.e. gates (G1) and (G2) hold.
2. The shell germ group `Q = <rho(P), tau>` is finitely presented, by
   `shell-germ-fp-is-an-ascending-hnn-gate` with the base `B = ker(eta)` itself
   (normal, so `B = s B s^-1` and the ascending union is `B`).

**Proof.** A finite-index subgroup of a finitely presented group is finitely
presented (Reidemeister–Schreier). `eta = eta_H` restricted to `R_nu`, and
`ker(eta) = R_nu ∩ ker(eta_H)` has index at most `[H:R_nu]` in `ker(eta_H)`,
which is finitely generated, so `ker(eta)` is finitely generated. Items 1–2 are
the cited equivalences. ∎

**Use.** Known hosts of this kind: the odometer groups `B = V_(h,r)(<a>)` and
their parity-charge subgroups `B_0` (`a5-arithmetic-germs-embed-in-fp-odometer-host`,
`a5-arithmetic-near-group-obeys-parity-charge-constraint`: finitely presented,
charge onto `Z`, finitely generated charge kernel). Any enumeration of any input
whose near group has finite index in such a host is the first known
non-virtually-cyclic enumeration passing both germ gates. It still leaves the
lifting gate (G3) and, for the shell route, finite presentation of `A_1`.
