---
rg: 2
id: translation-invariant-lcs-with-uniform-torus-gap-exists
kind: claim
title: Some translation-invariant linear rule on Z^2 has J nontrivial and a torus-uniform almost-model gap
distinct_from:
  translation-invariant-lcs-torus-gap-forces-nonhyperlinear: that proves what such a rule would give; this is the open existence statement.
---

**OPEN.** There is a translation-invariant binary linear rule \(R\) on
\(\mathbb Z^2\) with \(J\ne1\) in \(\mathrm{Sol}_R\), together with \(\varepsilon>0\)
and \(n_0\), such that no torus system \(\mathrm{Sol}_{R,n}\) with \(n\ge n_0\)
has an \(\varepsilon\)-model. The definitions are those of
`translation-invariant-lcs-torus-gap-forces-nonhyperlinear`.

By that claim, such a rule makes \(\Gamma_R=\mathrm{Sol}_R\rtimes\mathbb Z^2\) a
finitely presented nonhyperlinear group.

## Attempts

1. **Rules with a periodic classical solution die.** A classical solution is a
   \(0\)-model with \(d=1\). Example: the plaquette rule, \(x_vx_{v+e_1}x_{v+e_2}x_{v+e_1+e_2}=J\)
   with pairwise commuting plaquettes, has the period-2 solution \(x_v=-1\) iff
   \(v\equiv(0,0)\bmod2\). Each plaquette contains exactly one such site. So a
   candidate rule has no classical periodic solution. Commuting-context rules are
   expected to fail wholesale by periodicity of algebraic \(\mathbb Z^2\)-subshifts,
   but that source is not checked here.
2. **Exact derivations cannot certify the gap.** Part (5) of the claim shows that
   exact \(J=1\) derivations on \(T_n\) have area \(\ge n/(2\rho)\) whenever
   \(J\ne1\) in \(\mathrm{Sol}_R\). They certify gaps \(\le4\rho/n\to0\). So
   small-torus exact computations are only necessary-condition filters. No MSI
   search was run for them (2026-09-13, lane `solve-nh-tiling`); a search without
   an analytic rigidity input would certify nothing.
3. **What a proof needs.**
   - **(a)** A rule with \(J\ne1\) in \(\mathrm{Sol}_R\), certified by an explicit
     commuting-operator strategy that is not periodic.
   - **(b)** An analytic, torus-uniform rigidity statement for almost-models with
     \(J=-I\), for example a spectral-gap or Kazhdan-type argument on the local
     algebra, uniform in \(n\).

   By §§2–3 of the proof route, (b) is at least as strong as nonhyperlinearity of
   \(\mathrm{Sol}_R\) itself. The tiling framework adds translation invariance and
   finite tori, not a new mechanism.
