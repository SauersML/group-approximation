---
rg: 2
id: mersenne-phases-have-explicit-exact-core-bend
kind: claim
title: Every Mersenne phase countersequence is absorbed by a vanishing parabolic core bend
distinct_from:
  mersenne-phases-refute-diagonal-iwahori-decoder: that proves constant distance from exact diagonal endpoints over the frozen core; this constructs an explicit exact endpoint after moving only the parabolic core generator by a vanishing amount.
  link-thresholds-need-macroscopic-phase-frustration: that globalizes arbitrary half-edge intervals and estimates their syndrome; this identifies the globalization itself as an exact diagonal conjugacy coboundary.
  same-core-involution-cubic-gauge-coercivity: that requires a gauge commuting with the frozen parabolic generator; the conjugating gauge here commutes with r but deliberately has a small nonzero t-commutator.
---

**ESTABLISHED EXACT ABSORBER.** Put

\[
 m=4^n-1,\qquad
 Q=\operatorname{SL}_2(\mathbb Z/m\mathbb Z)/\{+\!I,-I\},
\]

and let

\[
 R=\lambda_Q(r),\qquad T=\lambda_Q(t),\qquad X_0=\lambda_Q(x).
\]

Choose an arbitrary translated half-interval \(I_v\) in the \(m\) incident
edge labels at every vertex \(v\in P\backslash Q\). Let
\(\eta_v(e)\) be its half-edge indicator and define

\[
 c_\eta(\{u,v\})=\eta_u(\{u,v\})+\eta_v(\{u,v\})
 \quad\text{in }\mathbb F_2.                            \tag{ECB1}
\]

There is an explicit diagonal unitary \(U_\eta\) such that

\[
 X_\eta=M_{(-1)^{c_\eta}}\lambda_Q(x)
       =U_\eta X_0U_\eta^*,\qquad
 [U_\eta,R]=0.                                          \tag{ECB2}
\]

Put

\[
 T_\eta=U_\eta T U_\eta^*.
\]

Then the whole square-free tuple

\[
 (X_\eta,R,T_\eta)
 =\operatorname{Ad}(U_\eta)(X_0,R,T)                   \tag{ECB3}
\]

is an exact representation endpoint, and the only moved coordinate obeys
the exact normalized Hilbert--Schmidt identity

\[
 \|T_\eta-T\|_2^2=\frac{8}{3n}.                         \tag{ECB4}
\]

In particular, apply this to the entropy-selected phases in
mersenne-phases-refute-diagonal-iwahori-decoder. Although \(X_\eta\)
stays a fixed distance from every exact diagonal extender over the frozen
core \((R,T)\), the full approximate tuple satisfies

\[
 \operatorname{dist}_2\bigl((X_\eta,R,T),
       \operatorname{Rep}_{|Q|}(\Gamma)\bigr)
 \le \sqrt{\frac{8}{3n}}\longrightarrow0.              \tag{ECB5}
\]

Thus the unconditional binary countersequence is not a counterexample to
strict or flexible Hilbert--Schmidt stability of the full Iwahori
presentation. Its phase frustration is exactly a slowly varying
parabolic-core conjugacy mode.

This result does not decide whether \(X_\eta\) is a fixed positive distance
from the union of all exact nondiagonal endpoints over the *unchanged*
core \((R,T)\). It proves that any such fixed-core lower bound disappears
as soon as the endpoint is allowed the core perturbation required by the
ordinary stability metric. The non-hyperlinearity root remains open.

DERIVATION
half-edge-phases-conjugate-the-regular-endpoint
