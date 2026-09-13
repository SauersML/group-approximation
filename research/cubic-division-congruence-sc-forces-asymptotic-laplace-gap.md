---
rg: 2
id: cubic-division-congruence-sc-forces-asymptotic-laplace-gap
kind: claim
title: Congruence strong convergence for SL_1(O_D) forces the new automorphic spectrum at prime level to become tempered at infinity, and an optimal Laplace gap
distinct_from:
  cubic-division-congruence-sc-descends-to-thin-subgroups: that transfers strong convergence to thin subgroups (a free-group, operator-algebraic consequence); this transfers it to the right-regular representation of SL_3(R) on the congruence quotients (an automorphic, archimedean consequence).
---

ESTABLISHED (unreviewed).  Let `D`, `Gamma_D = SL_1(O_D)` and
`pi_p = l^2_0(SL_3(F_p))` be as in
`cubic-division-congruence-representations-converge-strongly`.  Let
`G = SL_3(R)`, `X = G/SO(3)`, and let `lambda_0(X)` be the bottom of the Laplace
spectrum of `X`.  Let `R_p` be the right-regular representation of `G` on the
new part `L^2(Gamma_D(p) \ G) minus L^2(Gamma_D \ G)`.  Let `lambda_1^new(p)` be the
smallest Laplace eigenvalue of `M_p = Gamma_D(p) \ X` on the orthogonal
complement of the pullback of `L^2(Gamma_D \ X)`.

Suppose `pi_p -> lambda_(Gamma_D)` strongly along primes.  Then:

1. **Norms.**  For every `f in C_c(G)`, `limsup_p ||R_p(f)|| <= ||lambda_G(f)||`.
2. **Asymptotic temperedness at infinity.**  Let `C` be a compact set of
   non-tempered irreducible unitary representations of `G` (Fell topology).
   Then only finitely many primes `p` carry a new automorphic representation
   whose archimedean component lies in `C`.  Equivalently, every Fell
   accumulation point of new archimedean components along primes is
   tempered.
3. **Laplace gap.**  `liminf_p lambda_1^new(p) >= lambda_0(X)`: for each
   `eps > 0`, all but finitely many prime covers have no new eigenvalue below
   `lambda_0(X) - eps`.

**What this says about the positive direction.**  New automorphic
representations of `SL_1(D)` with non-tempered archimedean component
correspond, via Jacquet--Langlands for `D` of prime degree 3 (Badulescu;
import, not re-read), to cuspidal `GL_3` forms violating the Ramanujan
conjecture at infinity.  So a positive answer contains an asymptotic
Ramanujan-at-infinity theorem along prime levels for these forms.  As far as
I recall, the known tools do not give this: the Luo--Rudnick--Sarnak
uniform bound, and density theorems of Sarnak--Xue type that count
exceptional representations without excluding them at infinitely many
levels.  That is from memory only; no search was run, because the web budget
was exhausted.

Together with `cubic-division-congruence-sc-descends-to-thin-subgroups`, the
positive direction contains two hard problems from different fields:
- deterministic strong convergence for explicit free groups;
- asymptotic archimedean Ramanujan along prime levels.

The transfer principle (strong convergence of the monodromy controls the
spectrum of covers) is the one used by Hide--Magee for random covers of
hyperbolic surfaces.  The proof here is self-contained.

Proof: `cubic-division-congruence-sc-forces-asymptotic-laplace-gap-proof`.
