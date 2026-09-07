---
rg: 2
id: single-coordinate-section-linearization-proof
kind: route
title: Subtract the zero response and retain the responses to unit data inputs
target: nonlinear-local-sections-of-linear-families-linearize
requires: []
---

Choose finite data memory H and finite certificate memory D for s. Write
the output at g as a local function of z on gH and c on gD. For each
h in H and scalar coordinate j=1,...,m, define the j-th column of p_h(c)
to be the origin response of s to local data that are zero except for a
unit in coordinate (h,j), minus the origin response to zero local data.
Both evaluations use the same certificate c restricted to D. Thus
p_h is locally constant with certificate memory D. Set

    (P_c z)(g)=sum_(h in H) p_h(g^(-1).c) z(gh).

This is k-linear, equivariant as a certificate family, and uses precisely
the allowed memories H and D. Fix c, and let delta_(u,j) be the full
data configuration with a unit in scalar coordinate j at u and zero
elsewhere. By construction, at every g one has

    P_c delta_(u,j)=s_c(delta_(u,j))-s_c(0).              (SCL1)

If u is outside gH, both terms on the right have identical local data
at g and their difference is zero. Otherwise (SCL1) is the corresponding
column in the defining local rule of P. In particular, the difference
on the right has support contained in uH^(-1).

Apply the linear operator T_c to (SCL1). The assumed right inverse gives

    T_c P_c delta_(u,j)
      =T_c s_c(delta_(u,j))-T_c s_c(0)
      =delta_(u,j).

The two local linear operators T_c P_c and I therefore agree on every
unit input. Each output row involves finitely many input coordinates,
so equality on these unit inputs identifies every coefficient of that
row and proves T_c P_c=I on all configurations, including those of
infinite support. This reasoning is uniform in c.

The argument does not differentiate a Boolean function or assert a chain
rule for nonlinear composition. It uses the linearity of the outer map
T_c to commute it with the difference in (SCL1). This is exactly why the
same argument cannot be applied to an arbitrary nonlinear decoder.
