---
rg: 2
id: link-thresholds-need-macroscopic-phase-frustration
kind: claim
title: Low-link thresholds give small global syndrome only through a macroscopic phase-frustration gate
distinct_from:
  diagonal-parity-is-hecke-but-tau-misses-local-links: that constructs the low-gap additive link eigenfunction; this computes exact binary thresholds and their globalization over all vertex stars.
  proper-torus-diagonal-code-is-incomplete-cover-curl: that identifies the diagonal code with cellular cocycles; this isolates the remaining distance-to-cocycles variational quantity for a concrete threshold family.
  diagonal-exact-inversion-is-two-cubic-parity-code: that gives the original group-function Hamming modulus; this translates the proposed link coarea attack into normalized edge and face counts.
---

**ESTABLISHED; EXACT COAREA GLOBALIZATION AND DISTANCE FIREWALL.**
Use the odd congruence level

```text
m=4^n-1,   G=SL_2(Z/mZ)/{+-I},   d=ord_m(4)=n,
H=<h(2)>,  N=<H,x>,               P=UH.                 (LTF1)
```

Let `K_(H,m)` be the edge-refined two-triangle complex with

```text
V=P\G,       E=N\G.
```

It is `m`-regular, and

```text
|V|=|G|/(mn),       |E|=|G|/(2n)=m|V|/2.               (LTF2)
```

At every vertex, identify its link vertices with `Z/mZ` as in the link
calculation. Put

```text
I={0,1,...,(m-3)/2}.                                    (LTF3)
```

Thus `|I|=(m-1)/2`. In the combined link whose connection multisets are

```text
+/- <4>       and       +/- (1/2)<4>,
```

the number of link edges crossing from `I` to its complement, with the
face multiplicities retained, is exactly

```text
|partial_link I|=2(m-1).                                (LTF4)
```

The same holds for every additive translate of `I`.

For a vertex `v` and a subset `S` of its incident edges, let `s_(v,S)` be
the one-cochain supported on those star edges. Then

```text
supp(delta_1 s_(v,S))=partial_link S,                   (LTF5)
```

under the face/link-edge correspondence. Moreover the full star is the
vertex coboundary `delta_0 1_v`, so

```text
dist_E(s_(v,S),Z^1)
 <=dist_E(s_(v,S),B^1)
 <=min(|S|,m-|S|)/|E|.                                  (LTF6)
```

In particular a single threshold from (LTF3), or thresholds on `o(|V|)`
vertex stars, have distance tending to zero. They cannot be a Hamming
countersequence even though their defect-to-distance ratio deteriorates.

There is nevertheless an exact macroscopic globalization. At each vertex
`v`, choose any translated interval `I_v` in its link and let
`eta_v(e)=1_(I_v)(e)` on the half-edges at `v`. Define

```text
c_eta({u,v})=eta_u({u,v})+eta_v({u,v}) in F_2.          (LTF7)
```

For every selected triangular face `f={u,v,w}` one has

```text
(delta_1 c_eta)(f)
 =partial eta_u(f)+partial eta_v(f)+partial eta_w(f),   (LTF8)
```

where `partial eta_u(f)` is the difference of the two `u`-half-edge bits
in that face. Consequently

```text
|supp(delta_1 c_eta)|
 <=sum_(v in V)|partial_link I_v|
 =2|V|(m-1),                                            (LTF9)
```

and the normalization used by the diagonal code gives

```text
|supp(delta_1 c_eta)|/|G|
 <=2(m-1)/(mn)
 <2/n.                                                   (LTF10)
```

Thus `c_eta` is an explicit family of globally supported binary
cochains with vanishing syndrome for **every** choice of vertex phases.

The remaining issue is exactly the quotient norm

```text
Phi_n(eta)=inf_(z in Z^1(K_(H,m);F_2))
           |supp(c_eta+z)|/|E|.                         (LTF11)
```

If some phase choices satisfy `liminf Phi_n(eta)>0`, they are a genuine
Hamming countersequence and refute the diagonal decoder. If all phase
choices admit `Phi_n(eta)->0` uniformly, that is a nonlinear global
rescue for this entire low-link family. Neither conclusion follows from
the link eigenvalue or from coarea.

More sharply, if `c` is a sum of threshold star cochains at a set `R` of
vertices, then

```text
dist_E(c,Z^1)<=|R|/|V|.                                 (LTF12)
```

Hence `|R|=o(|V|)` is rigorously harmless. A counterexample must use a
linear proportion of all vertex stars with mutually incompatible phases.
At that density every edge is shared by two local patterns, and their
cancellations are exactly (LTF7)-(LTF11), not a consequence of the
one-link Cheeger estimate.

This converts the proposed threshold attack into one finite, explicit
binary frustration problem. It neither proves nor refutes the Hamming
decoder; the diagonal route and the non-hyperlinearity root remain open.

DERIVATION
link-threshold-phase-frustration-proof
