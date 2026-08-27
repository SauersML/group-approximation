---
rg: 2
id: char-p-weyl-blocks-local-commutator-decoder
kind: claim
title: A characteristic-p Weyl cell defeats local additive-commutator decoding from paired Steinberg roots
distinct_from:
  one-additive-commutator-suffices-for-julia-return: that compresses the desired complex-matrix trace certificate to one coefficient-level Steinberg word; this proves that the paired root word alone does not reflect that certificate in abstract unitary representations.
  cyclic-acceptance-root-needs-kernel-reflection: that states the need for root-to-coefficient kernel reflection for one positive acceptance coefficient; this gives an exact canonical-trace finite countermodel already for the paired additive-commutator syntax.
  mixed-steinberg-loops-admit-morita-rectangular-model: that exploits unequal coefficient reservoirs in a Leavitt cell; this obstruction occurs in one square coefficient ring and comes from the characteristic mismatch between algebraic and complex additive commutators.
---

ESTABLISHED.  Fix a prime `p`, let

```text
V=F_p[t]/(t^p),          R=End_(F_p)(V)=M_p(F_p),
```

and define `M,D in R` by multiplication by `t` and formal differentiation.
The truncated boundary causes no error in characteristic `p`, and exactly

```text
D M-M D=1_R.                                             (CPW1)
```

Indeed `(DM-MD)t^j=t^j` for `0<=j<p-1`; for `j=p-1`,
`DM(t^(p-1))=0` while
`MD(t^(p-1))=(p-1)t^(p-1)=-t^(p-1)`.

In the finite elementary group `E_3(R)`, with
`[g,h]=ghg^(-1)h^(-1)`, the two Steinberg triangles therefore give

```text
[e_12(D),e_23(M)] [e_12(M),e_23(D)]^(-1)
   =e_13(DM-MD)=e_13(1_R).                              (CPW2)
```

Take the left regular representation of `E_3(R)`.  This is an exact unitary
finite-packet model of the complete root tables used in `(CPW2)`, and it has
canonical trace on every group word: every nonidentity word has trace zero.
In particular `e_13(1_R)` is retained as a nonidentity root word.

By contrast, for every pair of complex matrices `X,Y in M_d(C)`,

```text
||[Y,X]-I_d||_(2,tr_d) >= |tr_d([Y,X]-I_d)|=1.          (CPW3)
```

Consequently no normalized-HS decoder whose hypotheses consist only of the
finite root tables and the two paired Steinberg multiplication triangles can
have all three of the following properties:

1. it is valid for every exact unitary realization of that finite packet;
2. it sends the coefficient unit to the complex identity; and
3. at zero group defect it outputs complex matrices satisfying the decoded
   additive comparison with zero error.

The failure persists after arbitrary amplification and after replacing the
regular packet by any construction from it using finite spectral
decomposition or conditional expectation: `(CPW3)` concerns the proposed
output matrices themselves.

Applied to the endpoint of
`one-additive-commutator-suffices-for-julia-return`, set formally `P=I` and
`A_t=0`.  The root syntax `(CPW2)` accepts the coefficient equation
`[D,M]=P-A_t` exactly, while the desired complex-matrix residual has norm at
least one.  Thus the coefficient-level identity `(ACJ9)` cannot be promoted
to the required abstract-unitary decoder by paired root triangles, a finite
root packet, or packet conditional expectation alone.

This does **not** refute a decoder using the full ambient presentation.  It
identifies its missing positive datum: the full group must exclude the
characteristic-`p` Weyl sector, or recover a matrix-coordinate coefficient
chart whose unit and trace are compatible with complex finite matrices.
Equivalently, the load-bearing inference is a characteristic-zero
root-to-coefficient trace-reflection theorem, not another local Steinberg
commutator identity.
