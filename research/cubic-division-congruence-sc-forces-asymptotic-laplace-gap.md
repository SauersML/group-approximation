---
rg: 2
id: cubic-division-congruence-sc-forces-asymptotic-laplace-gap
kind: claim
title: Congruence strong convergence for SL_1(O_D) forces an asymptotically optimal Laplace spectral gap on the prime congruence covers
distinct_from:
  cubic-division-congruence-sc-descends-to-thin-subgroups: that transfers strong convergence to thin subgroups (a free-group, operator-algebraic consequence); this transfers it to the Laplacian of the congruence covers of the locally symmetric space (an automorphic, archimedean consequence).
---

ESTABLISHED (unreviewed).  Let `D`, `Gamma_D = SL_1(O_D)` and
`pi_p = l^2_0(SL_3(F_p))` be as in
`cubic-division-congruence-representations-converge-strongly`.  Let
`X = SL_3(R)/SO(3)` and let `lambda_0(X)` be the bottom of the `L^2`-spectrum
of its Laplacian.  `Gamma_D` is torsion-free and cocompact, so
`M_p = Gamma_D(p) \ X` is a compact manifold covering `M_1 = Gamma_D \ X`.
Let `lambda_1^new(p)` be the smallest eigenvalue of the Laplacian on
`L^2(M_p)` minus the pullback of `L^2(M_1)`.

**Claim.**  If `pi_p -> lambda_(Gamma_D)` strongly, then
`liminf_p lambda_1^new(p) >= lambda_0(X)`.  Equivalently, for every `eps > 0`,
all but finitely many prime levels carry no new Laplace eigenvalue below
`lambda_0(X) - eps`.

**What this says about the positive direction.**  A new eigenvalue below
`lambda_0(X)` at level `p` comes from an automorphic representation of
`SL_1(D)` whose archimedean component is spherical and not tempered.  For
`D` of prime degree 3, the Jacquet--Langlands transfer of such a
representation (Badulescu; import, not re-read) is a cuspidal representation
of `GL_3` over `Q` violating the Ramanujan conjecture at infinity.  So a
positive answer contains an asymptotic Ramanujan-at-infinity statement along
prime levels for these forms.  The uniform bound I know (Luo--Rudnick--Sarnak)
does not exclude exceptional archimedean parameters at infinitely many
levels.  That this asymptotic statement is open rests on my memory only: no
search was run, because the web budget was exhausted.

With `cubic-division-congruence-sc-descends-to-thin-subgroups`, the positive
direction thus contains two hard problems from different fields:
- deterministic strong convergence for explicit free groups;
- asymptotic archimedean Ramanujan along prime levels.

The transfer principle (strong convergence of monodromy controls spectral gaps
of covers) is the one Hide and Magee used for random covers of hyperbolic
surfaces; the argument is reproduced in full in the proof route.

Proof: `cubic-division-congruence-sc-forces-asymptotic-laplace-gap-proof`.
