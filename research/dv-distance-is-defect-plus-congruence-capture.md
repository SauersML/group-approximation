---
rg: 2
id: dv-distance-is-defect-plus-congruence-capture
kind: claim
title: Dogon--Vigdorovich distance is defect plus congruence-capture distance
artifacts:
  - research/triangle-reduces-dv-to-unbounded-congruence-capture.md
distinct_from:
  congruence-repair-bypasses-koopman-cycle-firewalls: that gives qualitative repair for sequences already in the congruence locus; this gives a quantitative two-sided reduction for every exact modular-vertex pair.
  regular-iwahori-relative-congruence-exactification: that is the open flexible capture theorem on the regular-character branch; this proves that such capture is the only missing global term after unbounded congruence repair.
  iwahori-uniform-infinitesimal-rigidity: that gives the derivative gap at compatible congruence endpoints; this is a global metric reduction and does not assume the input is in a Newton neighborhood.
  mersenne-phases-far-from-all-frozen-core-endpoints: that gives a positive distance only in a frozen-core slice; this uses the ordinary metric in which the parabolic core may move.
---

**ESTABLISHED SHARP REDUCTION; THE FULL QUESTION REMAINS OPEN.**

Use the representation space and generalized Hilbert--Schmidt metric of
Dogon--Vigdorovich, arXiv:2506.20843v2, Question 1.4. Let
\(\mathcal C\) be the union, over all dimensions and all levels, of exact
pairs of modular-vertex representations whose two vertices factor through
finite congruence quotients. The levels may differ and may have arbitrary
odd and dyadic parts. Put
\[
A_{\mathrm{cong}}(\pi)
 =\inf_{\rho\in\mathcal C}d_2(\pi,\rho).                 \tag{DCC1}
\]

There are constants \(K_{\mathrm{cong}},L_B<\infty\), depending only on the
fixed generating sets and not on dimension or congruence levels, such that
every exact modular-vertex pair \(\pi\) satisfies
\[
 A_{\mathrm{cong}}(\pi)
 \ \le\ D(\pi)
 \ \le\
 K_{\mathrm{cong}}\,\operatorname{def}(\pi)
 +(1+2K_{\mathrm{cong}}L_B)A_{\mathrm{cong}}(\pi).
                                                               \tag{DCC2}
\]

Here \(L_B\) is the largest word length, in the two fixed modular generating
sets, of an Iwahori defect generator and its commensurated mate.

Consequently Dogon--Vigdorovich Question 1.4 is equivalent to the following
single **congruence-capture** statement:
\[
 \operatorname{def}(\pi_n)\longrightarrow0
 \quad\Longrightarrow\quad
 A_{\mathrm{cong}}(\pi_n)\longrightarrow0.              \tag{DCC3}
\]
In particular:

1. the question has a uniform linear positive answer on the full exact
   congruence locus, with no conductor bound;
2. more generally, any sequence with both
   \(\operatorname{def}(\pi_n)\to0\) and
   \(A_{\mathrm{cong}}(\pi_n)\to0\) is globally repairable;
3. every negative countersequence must remain a fixed positive distance
   from **all** congruence vertex pairs, not merely escape every bounded
   conductor window.

The local same-dimension angle is not the remaining congruence obstruction.
The established theorem **iwahori-uniform-infinitesimal-rigidity** gives one
dimension- and level-independent positive singular-value bound at every
compatible congruence endpoint, on the full cocycle mismatch map, including
cuspidal, Eisenstein, and coboundary directions. Thus (DCC3) is a global
basin/capture problem for genuinely noncongruence modular representations,
not a missing local Hecke angle.

The Mersenne phase family confirms the metric distinction. It is uniformly
far from every exact endpoint when the regular parabolic core is frozen, but
the explicit gauge moves that core by squared distance \(8/(3n)\) and
produces an exact endpoint. Hence fixed-core separation contributes no
positive \(A_{\mathrm{cong}}\) term in the ordinary movable-core metric.

This settles a stated restricted case strictly beyond bounded conductor but
does not settle Question 1.4 or prove a nonhyperlinear group.

DERIVATION
triangle-reduces-dv-to-unbounded-congruence-capture
