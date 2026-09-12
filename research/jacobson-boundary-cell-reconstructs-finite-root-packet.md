---
rg: 2
id: jacobson-boundary-cell-reconstructs-finite-root-packet
kind: claim
title: One Jacobson boundary cell reconstructs a finite root packet and admits coherent relative correction
distinct_from:
  jacobson-ts-cell-is-independent-after-first-raw-commutation: that separates the TS word from one amenable model; this derives all boundary root addition and commutation relations from an additional explicit cell and a shifted finite packet.
artifacts:
  - research/artifacts/jacobson-shifted-gl3-and-boundary-gl5-packets-2026-09-08.md
  - research/artifacts/jacobson-boundary-packet-relative-rounding-2026-09-08.md
---

Use the original packet `F=GL_3(F_2)_Q x GL_3(F_2)_P` and impose
the shifted packet `G_*=<c,k,h>~=GL_3(F_2)`, with
`c=x_13,P`, `k=x_31,P`, and shifted coordinates
`c=x_13,*`, `k=x_31,*`, `h=w_12,*`. The shared subgroup is
`K_P=<c,k>`, and `K_Q=GL(<e_1,e_3>)_Q` centralizes `G_*`.
Put

```text
s=h c h,          u=[s,k],
a=x_23,Q,         r=x_23,P,
W=[u,h(a r)h](a r),
L_a=[u,h a h]a.
```

Assume the two explicit cells `W=1` and `L_a=1`. The literal
Jacobson action satisfies all these hypotheses and retains the head.

Then the conjugates `a_v=gag^-1`, indexed by `g e_2=v!=0`, are
well-defined and, with `a_0=1`, satisfy

```text
a_v a_w=a_(v+w)      for every v,w in F_2^3.
```

Applying the same construction to the other head row generators
reconstructs the embedded finite subgroup

```text
Hom(F_2^2,F_2^3) semidirect (GL_2(F_2) x GL_3(F_2)),
of order 64512.
```

The raw commutation `[s,r]=1` already follows from `W=1` and the
shifted packet; it is not an additional hypothesis. For exact unitary
packets its defect is at most `12||W-I||`.

The reconstruction is an abstract finite-group statement. In complex
unitary representations the abelian normal subgroup has three character
orbits, of sizes `1,21,42`; there is no assumption of a defining
three-dimensional complex module. This establishes neither a matrix gap
nor non-MF existence. The original first braid is not needed for the
finite-subgroup conclusion.

There is also a quantitative statement for approximate cells. Keep the
two finite packets exact, agreeing on `K_P`, with `K_Q` commuting with
`G_*`, and set

```text
w=||W-I||, ell=||L_a-I||, D=10 ell+128 w.
```

If `D<=1/100`, the common matrix `H` can be replaced on the same
dimension by `H'`, with `||H'-H||<=85D`, so that it and the
unchanged original packet come from an exact representation of the
finite root packet. Its intersection with `F` is
`L'=P_Q x K_P`; this entire subgroup is fixed by the correction.
Consequently the shifted packet, its shared generators, and the boundary
cell remain coherent and become exact simultaneously.

For `b=(w_23,w_23)` in the original packet, the remaining errors obey

```text
||W(H')-I|| <= w+1020D,
||(H'b)^3-I|| <= ||(Hb)^3-I||+255D.
```

Thus vanishing-error models reduce to the finite amalgam
`F *_(P_Q x K_P) J`, where `J` is the group of order 64512 above,
with only the TS word and first braid left approximate. The correction
does not prove a positive lower bound for these remaining errors.

DERIVATION
jacobson-boundary-fano-addition-proof
