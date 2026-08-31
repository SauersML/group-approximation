---
rg: 2
id: two-bs-edges-hide-an-amenable-q8-splitting
kind: claim
title: Two invisible BS edges make a nonamenable amalgam but hide a finite transverse splitting
artifacts:
  - research/transverse-q8-splitting-proves-the-two-bs-firewall.md
distinct_from:
  q8-bs23-terminal-mark-is-exactly-invisible-but-hyperlinear: that uses one invisible cyclic edge and is hyperlinear by the displayed amenable-edge splitting; this doubles the actor to obtain a genuine nonamenable edge, then finds a different finite-edge splitting of the same group.
  amenable-edge-cycles-cannot-create-an-lcs-gap: that is a general permanence fence; this gives a seven-generator nonamenable-edge presentation whose transverse decomposition falls back inside that fence.
  shared-center-extraspecial-wreath-has-fd-invisible-spin-sector: that shares one sign across infinitely many Pauli sites and leaves a moving-window multiplicity reservoir; this shows why finitely duplicating the Q8 terminal selector does not escape hyperlinear permanence.
---

Let
[
 A_i=langle a_i,t_imid t_i a_i^2t_i^{-1}=a_i^3angle
 cong BS(2,3)qquad(i=0,1)
]
and put
[
 w_i=[t_i a_i t_i^{-1},a_i].
]
Let
[
 Q_8=langle x,y,zmid z^2=1, x^2=y^2=z, [z,x]=[z,y]=1, yx=zxyangle,
]
and let (alpha) be the involutive automorphism interchanging (x,y)
and fixing (z). Define the explicit seven-generator group
[
\begin{aligned}
 Pi_2=langle x,y,z,a_0,t_0,a_1,t_1mid;&Q_8, t_i a_i^2t_i^{-1}=a_i^3,\
 &[z,a_i]=[z,t_i]=1,\
 &w_i xw_i^{-1}=y,quad w_i yw_i^{-1}=x
 quad(i=0,1)angle .                                  	ag{TBS1}
end{aligned}
]

Then all of the following hold.

1. The subgroup (H=langle w_0,w_1angle) of (A_0*A_1) is the
   free group (F_2), and
   [
   Pi_2cong
   (Q_8times_alpha F_2)
   *_{F_2	imeslangle zangle}
   ((A_0*A_1)	imeslangle zangle).                    	ag{TBS2}
   ]
   Thus (TBS1) genuinely has a nonamenable edge.

2. The mark is central and nontrivial in the abstract group:
   [
   zin Z(Pi_2),qquad z
e1.                            	ag{TBS3}
   ]
   Every exact finite-dimensional unitary representation of (Pi_2)
   nevertheless kills (z).

3. The nonamenable-edge display does not produce an HS gap. If
   (Pi_i) denotes the one-copy Q8/(BS(2,3)) terminal group, then
   [
   Pi_2congPi_0*_{Q_8}Pi_1.                           	ag{TBS4}
   ]
   Each (Pi_i) is hyperlinear and (Q_8) is finite, so
   amenable-edge permanence makes (Pi_2) hyperlinear. Consequently
   (TBS1) has matrix almost-representations whose relator defects tend
   to zero while
   [
   |Z-I|_2longrightarrowsqrt2.                       	ag{TBS5}
   ]

There is also an exact modulus locating the failure. For any unitary tuple,
write (W_i=[T_iA_iT_i^*,A_i]) and set
[
 epsilon_Q=|YX-ZXY|_2,qquad
 epsilon_i=|W_iXW_i^*-Y|_2.
]
Then, for each (i=0,1),
[
 |Z-I|_2
 le epsilon_Q+2epsilon_i+2|[W_i,X]|_2.              	ag{TBS6}
]
Hence the hyperlinear models in (TBS5) have
[
 liminf|[W_i,X]|_2ge 1/sqrt2qquad(i=0,1).           	ag{TBS7}
]
Exact finite-dimensional invisibility of each (w_i) has no
dimension-independent normalized-HS robustification, even after the visible
edge has been made nonamenable.

The lesson is structural. A nonamenable edge label is not enough: one must
exclude every transverse amenable splitting and make a nonamenable packet
act on the sign in a way which cannot be decomposed into finitely many
one-word attachments. No nonhyperlinear group is proved here.

DERIVATION
transverse-q8-splitting-proves-the-two-bs-firewall
