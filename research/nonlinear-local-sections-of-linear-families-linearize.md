---
rg: 2
id: nonlinear-local-sections-of-linear-families-linearize
kind: claim
title: A nonlinear local right inverse of a certificate-linear family has a linear right inverse with the same memory
distinct_from:
  certificate-linear-automata-have-local-linear-decoders: that obtains a local linear left inverse from injectivity by compactness and clopen patching; this linearizes a given local right inverse by single-coordinate perturbations without increasing its memory.
  injective-automata-have-local-stable-secant-dilations: that adds an auxiliary track and always gives a reversible dilation; this extracts an actual unstabilized linear right inverse from an already valid nonlinear local section.
---

Let k be a finite field, B a finite nonempty certificate alphabet, and G
any group. Let T_c:(k^n)^G->(k^m)^G be a certificate-local linear family.
Suppose a cellular automaton

    (z,c) -> (s_c(z),c)

satisfies T_c s_c(z)=z for every z and c in B^G. The maps s_c need not
be linear or affine in their data. Then there is a certificate-local
k-linear family P_c with

    T_c P_c=I for every c.

P can use the same data memory and certificate memory as s. It is
obtained by evaluating the local rule of s at the zero input and at
one unit input in each scalar data coordinate, then taking differences.
No search for a new inverse and no enlargement of the alphabet is needed.

The premise is a right inverse on the entire certificate-data full shift.
Surjectivity of T alone, or a section only on valid computations, does
not supply it. The conclusion does not assert P_c T_c=I.
