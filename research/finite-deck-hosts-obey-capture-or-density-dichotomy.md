---
rg: 2
id: finite-deck-hosts-obey-capture-or-density-dichotomy
kind: claim
title: Every finite deck host has quotient capture or a positive density of bad returns
artifacts:
  - research/trace-the-tfd-return-gap-to-a-row-density-bound.md
distinct_from:
  tfd-tensorization-gaps-every-finite-deck-packet: that proves the operator gap for the averaged packet; this converts it into a row-count dichotomy and isolates the precise propagation input still absent from the three-sheet construction.
  index-three-frames-leave-deck-holonomy-uncontrolled: that gives one bad row in the infinite induced host; this proves that every finite host without quotient capture has a positive density of quantitatively bad rows.
  cayley-expansion-aligns-isometry-frame-coranges: that aligns a quotient-indexed field once its full edge energy is known; this shows exactly how much of that full return energy must be produced before finite-host capture can fail.
---

Use the notation and the constant \(\kappa\) of
tfd-tensorization-gaps-every-finite-deck-packet.  Let
\(\pi:\Gamma\to U(\mathcal H)\) be finite-dimensional, let
\(P_\Lambda\) project onto \(\mathcal H^{\pi(\Lambda)}\), and let
\(V:\mathbb C^d\to\mathcal H\) be an isometry.  Define the captured mass
\[
 c(V)=\frac1d\operatorname{Tr}(V^*P_\Lambda V)           \tag{CDD1}
\]
and the individual normalized return rows
\[
 E_{s,q}(V)=\frac1d
 \|(\pi(r(s,q))-1)V\|_{\mathrm F}^2\in[0,4].             \tag{CDD2}
\]
Then
\[
 \frac1{|S||Q|}\sum_{s,q}E_{s,q}(V)
 \geq\kappa\bigl(1-c(V)\bigr).                           \tag{CDD3}
\]

In particular, fix \(0<\alpha\leq1\).  If
\[
 c(V)\leq1-\alpha,                                      \tag{CDD4}
\]
then at least a fraction
\[
 \frac{\kappa\alpha}{8}                                 \tag{CDD5}
\]
of the Schreier rows satisfy
\[
 E_{s,q}(V)\geq\frac{\kappa\alpha}{2}.                   \tag{CDD6}
\]
Conversely, average return energy at most \(\varepsilon\) gives
\(c(V)\geq1-\varepsilon/\kappa\), and the spectral cut in (FDP5)
turns this captured mass into an exact \(\Gamma/\Lambda\)-corner after
losing at most \(2\varepsilon d/\kappa\) dimensions.

For the finite Iwahori deck quotient, this is a sharp transfer boundary.
A finite host which fails to contain an almost-full congruence corner
cannot hide its obstruction in one exceptional translated row: it must
place a fixed quantitative defect on a fixed positive proportion of all
deck returns.  Therefore the finite-host problem is no longer a spectral
gap problem.  It is the following propagation problem:

> construct a finite \(A\)-host from the two three-sheet systems in such a
> way that the concrete endpoint relator energy bounds the average of all
> Schreier return rows.

The two local three-sheet stars provide only a bounded collection of host
rows.  Equations (CDD3)--(CDD6) do not propagate those rows around the
moving quotient.  Quotient expansion can align a field after its full
edge energy is supplied, but it does not identify the local Q-system
errors with the return packet.  Producing that identification is exactly
the finite-host-to-endpoint seam; once it is available, (CDD3) and the
spectral cut finish the transfer with uniform constants.

This claim neither constructs the finite host nor proves (OPD11).  It
rules out rare-row finite countermodels and states the remaining input as
a positive-density propagation theorem, rather than an additional
Kazhdan or property-\((\tau)\) gap.

DERIVATION
trace-the-tfd-return-gap-to-a-row-density-bound
