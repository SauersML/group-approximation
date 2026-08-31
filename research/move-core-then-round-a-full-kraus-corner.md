---
rg: 2
id: move-core-then-round-a-full-kraus-corner
kind: route
title: Move the exact core, then round one full Kraus corner
target: optimized-core-full-pd-energy-is-intrinsic-selector
requires:
  - multi-kraus-frame-energy-is-the-full-relative-pd-gate
  - cayley-expansion-aligns-isometry-frame-coranges
  - tfd-finite-corner-collapse-and-rfd-firewall
  - gauge-optimized-induced-energy-target
---

# Core optimization and corange alignment commute

Put
\[
 C_\gamma=1+2\sqrt{2/\gamma}.
\]
For each fixed competitor \(c\), the pointwise comparison (CEA8) gives
\[
 e_{\rm K}(U_c;c)\leq e_{\rm unit}(U_c;c)
 \leq C_\gamma e_{\rm K}(U_c;c).                         \tag{1}
\]
Therefore
\[
 m(b,c)+e_{\rm K}(U_c;c)^2
 \leq m(b,c)+e_{\rm unit}(U_c;c)^2
 \leq C_\gamma^2\bigl(m(b,c)+e_{\rm K}(U_c;c)^2\bigr).
                                                               \tag{2}
\]
Taking the infimum over the same exact core variety proves (OPD4). No
choice of a minimizing core must be transported through the polar
construction; the comparison is pointwise before taking either infimum.

# A low-energy full frame is already a finite corner

Fix \(c\) and a relative frame within an arbitrarily small error of
\(e=e_{\rm K}(U_c;c)\). In Stinespring form it is a finite-dimensional
representation
\[
 \pi:G_N\to U(\mathscr H)
\]
and an isometry \(V:\mathbb C^d\to\mathscr H\) satisfying
\[
 \pi(b)V=V\beta_c(b)\qquad(b\in B_N),                     \tag{3}
\]
with
\[
 \frac1{|S|}\sum_s\frac1d
 \|\pi(s)V-VU_{c,s}\|_{\mathrm F}^2=e^2.                 \tag{4}
\]
Let \(P=VV^*\). Since \((1-P)VU_{c,s}=0\),
\[
 \frac1d\|(1-P)\pi(s)V\|_{\mathrm F}^2
 \leq\frac1d\|\pi(s)V-VU_{c,s}\|_{\mathrm F}^2.           \tag{5}
\]
Thus the total leakage of \(P\) in the exact finite-dimensional
representation \(\pi\) is at most \(|S|e^2\).

The finite-corner property-\((T;FD)\) rounding theorem applies to
\((\pi,P)\). It produces an exact subrepresentation, with only
\(O(e^2d)\) rank correction, whose marked tuple is at generalized
Hilbert--Schmidt distance \(O(e)\) from \(U_c\). Because \(\pi\) factors
through \(G_N\), so does the rounded endpoint. Moving back from the hybrid
core \(c\) to the supplied core \(b\) costs at most
\[
 \sqrt{m(b,c)}
\]
on the fixed core coordinates. Hence
\[
 D_{\rm flex}(X,R,T)
 \leq C_0\bigl(e+\sqrt{m(b,c)}\bigr)
 \leq C_1\sqrt{e^2+m(b,c)}.                              \tag{6}
\]
Take the infimum over frames and then over \(c\) to obtain (OPD5).

# Exact endpoints give flat competitors

Let \(\rho:G_N\to U(d)\) be exact and take
\(c=(\rho(r),\rho(t))\). The function \(W_g=\rho(g)\) obeys
\[
 W_e=1,\qquad W_{bg}=\beta_c(b)W_g.
\]
For every marked generator,
\[
 U_{c,s}W_g-W_{sg}
 =(U_{c,s}-\rho(s))\rho(g).                              \tag{7}
\]
The core terms in (7) vanish, and the extender term has constant norm
\(\|X-\rho(x)\|_2\). Inserting this flat table into (OPD3) proves (OPD7).
This is why the optimized energy detects the union of endpoint fibers
rather than one preselected relative fiber.

# A chosen Schreier section is only one competitor

For a fixed \(c\), extend the Schreier-section unitaries in (GOI4) by the
exact core covariance. They form a relative unitary zero-cochain. Its
Cayley-row energy is the average of the coordinate defects
\(D_{(U_c,c)}(q,a)\). Hence
\[
 e_{\rm unit}(U_c;c)^2
 \leq C_S\max_a\frac1{|A_N/B_N|}\sum_q
       \|D_{(U_c,c)}(q,a)\|_2^2.                         \tag{8}
\]
Add the identical movement term and take infima to get (OPD8). Equation
(8) is one-way: minimizing over all unitary tables or all Kraus frames can
exploit cancellations and coefficient tables which no chosen word section
realizes.

Finally, the choices in (OPD9)--(OPD10) make the hybrid tuple itself an
exact endpoint. Their flat energies are therefore zero, and only the
displayed core movement remains. This verifies that the intrinsic
functional quotients both explicit false fixed-core directions before
asking for the still-open estimate (OPD11).
