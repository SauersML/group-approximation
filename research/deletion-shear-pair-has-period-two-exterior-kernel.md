---
rg: 2
id: deletion-shear-pair-has-period-two-exterior-kernel
kind: claim
title: Incomparable-prefix deletion pairs retain exterior kernels under shared triangular changes
artifacts:
  - research/artifacts/kaplansky-deletion-shear-period-two-exterior-kernel-2026-09-08.md
---

Let a=[[1,s_0],[t_0,0]], b=[[1,s_1],[t_1,0]], and g=diag(a,b)
in the binary Leavitt setting. Put zeta=(01)^infinity and
eta=(10)^infinity, and write a_i=e_i zeta, b_i=e_i eta for
the four binary root coordinates. Then

    w=(a_1+a_3) wedge b_1+(a_2+a_4) wedge b_2

satisfies f_0w=w nonzero and P_0[g]f_0w=0. Therefore the reduced
group-ring splitting identity has no left inverse, even with
unrestricted ambient support. The conclusion follows from the
explicit certificate, independently of the bounded numerical probe
that discovered it.

The same certificate excludes every replacement of (s_0,t_0) and
(s_1,t_1) by (s_alpha,t_alpha) and (s_beta,t_beta), where alpha,beta
are nonempty incomparable binary words. Use zeta=(alpha beta)^infinity
and eta=(beta alpha)^infinity. Their disjoint prefix cylinders give
the same four prefix/deletion identities, so the proof is unchanged.

The same w remains a kernel after every left change
M=[[h,k],[0,h]], with h any invertible binary-linear operator
on a field-coordinate pair and k any binary-linear operator.
The image gw lies in a P_0-null subspace invariant under all
such M. This includes arbitrary upper off-diagonal mixing;
unequal diagonal blocks and general lower mixing are not covered.

For the literal words 0 and 1, the separate claim
`deletion-pair-has-no-left-chart-coefficient-split` excludes
every left coefficient from F_2[K], with kernels depending on
the coefficient.
