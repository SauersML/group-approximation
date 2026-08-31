---
rg: 2
id: trace-the-tfd-return-gap-to-a-row-density-bound
kind: route
title: Trace the TFD return gap and count rows above half its mean
target: finite-deck-hosts-obey-capture-or-density-dichotomy
requires:
  - tfd-tensorization-gaps-every-finite-deck-packet
---

Compress (FDP3) by \(V\), take the ordinary trace, and divide by \(d\).
The left side is the average of (CDD2), while the right side is
\[
 \frac{\kappa}{d}\operatorname{Tr}
 \bigl(V^*(1-P_\Lambda)V\bigr)
 =\kappa(1-c(V)).
\]
This proves (CDD3).

Assume (CDD4) and put
\[
 m=\kappa\alpha,\qquad \theta=m/2.
\]
The normalized gap in (FDP1) may be replaced by
\(\min(\kappa,4)\), so assume \(0<\kappa\leq4\).  Let \(p\) be the
proportion of rows for which \(E_{s,q}\geq\theta\).  Every row lies in
\([0,4]\), because it is the squared normalized Frobenius distance between
two isometries.  If fewer than a proportion \(p\) are above the threshold,
then
\[
 \frac1{|S||Q|}\sum_{s,q}E_{s,q}
 \leq(1-p)\theta+4p
 =\theta+(4-\theta)p.                                   \tag{1}
\]
Together with (CDD3)--(CDD4), this gives
\[
 p\geq\frac{m-\theta}{4-\theta}
 =\frac{m}{8-m}
 \geq\frac m8
 =\frac{\kappa\alpha}{8}.                               \tag{2}
\]
Equations (1)--(2) prove (CDD5)--(CDD6).

If the average is at most \(\varepsilon\), (CDD3) instead gives
\[
 c(V)\geq1-\varepsilon/\kappa.                           \tag{3}
\]
The spectral projection
\[
 e=1_{[1/2,1]}(V^*P_\Lambda V)
\]
then has
\[
 \operatorname{rank}(1-e)\leq2\varepsilon d/\kappa.
\]
Polarizing \(P_\Lambda Ve\) gives the relative quotient isometry with the
same displacement estimate, exactly as in (FDP5).  This proves the converse
capture statement.

The argument uses no geometry of the section and no size estimate for
\(Q\).  Its limitation is equally exact: it starts with the average of all
return rows.  A bounded local star does not determine that average.  Any
positive Iwahori transfer must therefore manufacture a finite host and a
local-to-return energy comparison before this counting lemma can apply.
