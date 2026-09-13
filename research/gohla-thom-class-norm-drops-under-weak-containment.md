---
rg: 2
id: gohla-thom-class-norm-drops-under-weak-containment
kind: claim
title: Gohla--Thom — the norm of a central extension class drops under weak containment, vanishes on quotients of free actions of the extension, and is bounded below on finite actions over cosystolic bases
distinct_from:
  gohla-thom-stable-base-nonsofic-extension: that is their Theorem 3.13, stability in finite actions forcing nonsoficity; this imports the lemmas under it (2.13, 2.14, 2.10, 2.16, 3.4, 3.18, Remark 3.14) for use on weak containment of actions.
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-extension-class-norm-2026-09-13.md
---

**ESTABLISHED by citation** (`gohla-thom-class-norm-drops-under-weak-containment-citation`). Gohla--Thom,
*High-dimensional expansion and soficity of groups*, arXiv:2403.09582v2. Verbatim statements are in Section 1 of
the artifact.

Let `Gamma` be of finite type, `A` finite abelian, and `alpha in H^2(Gamma, A)`. For a measured `Gamma`-Boolean algebra
`P` (for instance the measure algebra of a p.m.p. action), `theta_*^P(alpha) in H^2(Gamma, P(A))` carries a quotient
pseudo-norm `|||.|||`, the least Hamming measure of a cocycle representative.
1. **Lemma 2.13 and the proof of Corollary 2.14.** Norms pass isometrically to metric ultraproducts, and inclusions
   are contractive. If `P` is weakly contained in a family `𝒫` (contained in an ultraproduct from `𝒫`, their
   Definition 2.2), then `|||theta^P(alpha)||| >= inf_{Q in 𝒫} |||theta^Q(alpha)|||`.
2. **Theorem 3.4.** If `alpha` classifies a central extension `Gamma~` by `A`, `Q` is an `A`-free measured
   `Gamma~`-Boolean algebra, and `P = Q^A`, then `theta_*^P(alpha) = 0`.
3. **Theorem 2.16.** Let `Gamma` be residually finite, satisfying a cosystolic inequality in dimension 2 for all
   finite transitive actions with respect to `A`, with `alpha` classifying a non-residually-finite extension. Then
   `theta_*^P(alpha) != 0` whenever `P` is weakly contained in the finite actions. The proof bounds the norm below
   uniformly on finite actions.
4. **Theorems 2.10 and 3.18.** For `d >= 4` and large `p`, torsionfree lattices in `PSp_2d(Q_p)` satisfy those
   cosystolic inequalities for every finite abelian `A`. Specific such lattices carry Prasad--Deligne central
   extensions by `Z/(p-1)` that are not residually finite.
5. **Remark 3.14.** The Bernoulli shift has `theta_*(alpha) != 0`, while `{0,1}^{Gamma~}/A` has `theta_*(alpha) = 0` and
   "is not weakly contained in the family of finite actions of Γ".
