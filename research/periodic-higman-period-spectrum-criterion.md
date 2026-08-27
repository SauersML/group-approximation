---
rg: 2
id: periodic-higman-period-spectrum-criterion
kind: claim
title: Avoiding the Higman period spectrum makes a deep filling non-residually finite
---

Define the Higman period spectrum

```text
Sigma={ord(alpha)>1 :
  H finite, H=<h_0,h_1,h_2,h_3>, alpha in Aut(H),
  alpha(h_i)=[h_i,h_(i-1)] for every i in Z/4}.
```

There is an integer `m_0` such that for every `m>=m_0`,

```text
(no d in Sigma divides m)  ==>
G_m is word-hyperbolic and not residually finite.       (PH3)
```

Here `G_m=M_phi/<<t^m>>`, with `M_phi` the mapping torus in
`periodic-higman-mapping-torus-is-word-hyperbolic`.
