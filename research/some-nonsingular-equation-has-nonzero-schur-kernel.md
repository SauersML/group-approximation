---
rg: 2
id: some-nonsingular-equation-has-nonzero-schur-kernel
kind: claim
title: Some nonsingular one-variable equation kills a nonzero Schur multiplier class of its coefficient group
distinct_from:
  kervaire-laudenbach-nonsingular-conjecture: that asserts coefficient injectivity for every nonsingular adjunction, degree-one information; this asks for failure of injectivity in second integral homology, which needs no coefficient to die and already refutes hyperlinearity of a central extension.
  kl-violating-equation-over-leavitt-unit-group: that asks for one coefficient-killing equation over the Leavitt unit group; this asks for a Schur-class-killing equation over any countable coefficient group, a weaker certificate with the same payoff for non-hyperlinear-group.
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

**OPEN.** There are a countable group `Q`, `w in Q * <t>` with
`deg_t(w) != 0`, and `0 != x in H_2(Q; Z)` with `x -> 0` in
`H_2((Q * <t>)/<<w>>; Z)`.

The certificate is finite, by `nonsingular-adjunction-never-enlarges-schur-multiplier`:
an identity `r in [F', R_Y][F', <<w~>>]` in a free group, together with a
cocycle evaluating nontrivially on `r`. By
`schur-kernel-lies-in-hyperlinear-radical`, it yields a non-hyperlinear
central extension of `Q`.

If every countable group is hyperlinear, this claim is false. Its negation,
Schur injectivity for every nonsingular adjunction, is a degree-two
companion of `kervaire-laudenbach-nonsingular-conjecture`.

## Attempts

1. **Finite coefficient groups.** Dead:
   `projective-unitary-classes-vanish-on-schur-kernel` makes every Schur
   kernel over a finite group zero. Recorded as
   `schur-kernel-search-over-finite-coefficient-groups`.
2. **Aspherical adjunctions** (small-cancellation-type or tower-reducible
   relative presentations). Dead:
   `aspherical-adjunction-has-zero-schur-kernel`. Recorded as
   `schur-kernel-search-over-aspherical-adjunctions`.
3. **Amenable coefficients.** Dead:
   `amenable-coefficients-have-zero-schur-kernel`. By
   `schur-kernel-localizes-to-coefficient-subgroup`, the killed class comes
   from the coefficient subgroup. For amenable coefficients, twisted regular
   representations detect every class there. Recorded as
   `schur-kernel-search-with-amenable-coefficients`.
4. **Classes seen by projective approximations.** Excluded in general. A
   killed class must vanish under the multiplier of every projective unitary
   homomorphism of `Q`, in any norm and any matrix sizes. So the class must
   be projectively invisible. Candidates come from classes that finite
   quotients and known projective representations do not see, like the
   Maslov class of `Sp_4(Z)` beyond its metaplectic reduction.
5. **From a central Kervaire--Laudenbach failure.** Live reduction
   `nonzero-schur-kernel-from-central-kl-failure`. A failure over a central
   extension whose quotient adjunction injects forces a nonzero Schur kernel.
6. **Deligne.** Open as `sp4-schur-kernel-meets-the-deligne-triple-class`,
   which gives the stronger central collapse for `E_3` directly.
