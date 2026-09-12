---
rg: 2
id: terminated-digit-four-state-nucleus-proof
kind: route
title: Check every local action, inverse nucleus, and typed product for the two carry injections
target: terminated-digit-carries-form-finite-injection-nucleus
requires: []
artifacts:
  - research/artifacts/boone-higman-terminated-digit-resolution-2026-09-08.md
---

Read finite digit words least-significant first, assigning digits
1,...,h their displayed integer values. A finite word w has value
q(w)=sum_j d_j*h^(j-1), and the empty word has value zero.
Every nonnegative integer has a unique such bijective-base word.
The paths w#z form a dense subset of C_Y. Directly from the
recursions, I sends q to q+1 and D sends q to h*q on these
terminated words, leaving the suffix z in C_X unchanged.

The recursions emit a nonempty output prefix whenever they recur,
so they define continuous maps on infinite digit paths too. Their
images are

    I(C_Y)=C_Y minus #C_X,
    D(C_Y)=#C_X union hC_Y.

The first-step image pieces are disjoint and partition these
displayed sets. Recursive decoding is productive, giving inverse
continuous maps on these clopen images. Thus I and D are open
injections. Both images have at least two different first edges,
so neither image has a nonempty common prefix.

## The full nucleus audit

The graph is strongly connected and is not a cycle. Hence it is
its own irreducible core. Both nodes branch, so the identity maps
have exactly the usual typed identity local actions.

The local actions of I are I at h, id_(C_X) at #, and id_(C_Y)
at 1,...,h-1. Those of D are D at 1, id_(C_X) at #, and
id_(C_Y) at 2,...,h. This proves local-action closure and rationality.
The carry maps recur on their displayed loop edges; the two
identity maps recur through the strongly connected graph.

For inverses, the exact formulas are

    I^-1(1z)=D(z),       I^-1(dz)=(d-1)z for 2<=d<=h,
    D^-1(#z)=#z,         D^-1(hz)=I(z).

They give inverse nuclei contained in N. For products of nonidentity
maps, direct evaluation on the dense terminated paths, followed by
continuity, gives

    I*D(z)=1z,           D*I(z)=hz.

These are canonical prefix injections, with only identity recurrent
local actions. The other two products have the following formulas:

    I^2(#z)=2#z,
    I^2(dz)=(d+2)z for 1<=d<=h-2,
    I^2((h-1)z)=1I(z),   I^2(hz)=2I(z),

    D^2(#z)=#z,
    D^2(1z)=h(h-1)D(z),
    D^2(dz)=h(h-1)(d-1)z for 2<=d<=h.

The middle range for I^2 is empty when h=2. Thus the recurrent
local actions of I^2 and D^2 also lie in N. Typed products with
identity maps add nothing. This verifies all the finite-nucleus
conditions, including product closure; checking individual rational
maps alone would not have sufficed.

[Belk--Bleak--Matucci--Zaremsky](https://arxiv.org/pdf/2309.06224),
Definition 2.43 and Theorem 2.46, now give the full contracting
RSG H_(h,r). Their Theorems B and C give, respectively, its finite
presentation and its embedding into a finitely presented simple
group. These are imported theorems; the four-map audit above is
the additional argument used here.
