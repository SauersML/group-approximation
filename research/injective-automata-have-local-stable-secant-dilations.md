---
rg: 2
id: injective-automata-have-local-stable-secant-dilations
kind: claim
title: A local auxiliary track makes secants reversible but clearing that track on all data is an additional inverse identity
distinct_from:
  boolean-secants-do-not-supply-operator-left-inverses: that disproves unstabilized telescoping inversion; this constructs a uniformly local invertible dilation after doubling the data and identifies the precise condition for restricting it back.
  certificate-linear-counterexamples-compile-to-lamp-algebras: that compiles an already injective linear family with a strict range defect; this always produces a reversible family and does not preserve a hypothetical nonlinear range defect.
  universal-block-return-violates-the-regular-firewall: that uses faithful characteristic-zero traces to exclude universal proper corners; this is a finite-field cellular-automaton construction valid without any trace or finiteness hypothesis.
---

Let k be a finite field, G any group, X=(k^n)^G, and tau,sigma:X->X
cellular automata with sigma tau=id. For certificates c=(x,y) in the
entire full shift C=(k^n x k^n)^G, there are certificate-local linear
operators P_c,Q_c on X such that, writing

    h=y-x,                 ell=tau(y)-tau(x),

one has P_c h=ell and Q_c ell=h. They can be constructed by finite
coordinate telescopes, without choosing frames on infinite configurations.

The operators on two data tracks

    U_c = [ P_c          I   ],
          [ I-Q_c P_c   -Q_c ]

    V_c = [ Q_c          I   ]
          [ I-P_c Q_c   -P_c ]

have uniformly finite memory and satisfy U_c V_c=V_c U_c=I for every
certificate. Consequently

    (z,w,c) -> (U_c(z,w),c)

is a reversible cellular automaton on the whole certificate-data full
shift, including arbitrary data unrelated to its certificate. It sends
the genuine disagreement (h,0) to (ell,0).

This resolves the locality problem for this stabilized construction.
It does not create an injective nonsurjective full-shift map: its inverse
V is explicit. For fixed c, the entire zero-auxiliary subspace
H=X x {0} is forward invariant under U_c if and only if

    Q_c P_c=I.                                             (SSD1)

Under (SSD1), U_c(H)=H if and only if P_c Q_c=I. Thus extracting a
strict embedding of H from this reversible dilation requires exactly
the one-sided operator identity and reverse defect that were missing
before stabilization. Knowing (I-Q_c P_c)h=0 only on the certified
disagreement does not establish (SSD1).

There is also an exact nonlinear version. For any tau,sigma, even without
sigma tau=id, the local map

    R(x,z)=(tau(x)+z, x-sigma(tau(x)+z))

is reversible, with

    R^(-1)(y,w)=(w+sigma(y), y-tau(w+sigma(y))).

When sigma tau=id, it restricts to tau on H. Its restriction is strict
exactly when tau is nonsurjective. This preserves a hypothetical defect
on the zero-auxiliary sector, while the ambient map stays surjective.
No source counterexample tau is constructed here.

Reversible constructions using an extra track are classical; see Vlasov,
*On generalization of reversible second-order cellular automata*,
https://arxiv.org/abs/1311.4297. The route proves the particular secant
and sector identities above directly. No novelty claim is made for
reversible simulation or the elementary block-matrix identity.
