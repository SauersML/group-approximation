---
rg: 2
id: power-pair-pro-p-graph-has-gcd-saturation
kind: claim
title: A power-pair graph has exactly its gcd saturation in the discrete free group
distinct_from:
  coprime-power-pair-phase-hnn-is-residually-finite: that uses the coprime case of this intersection formula to preserve all Britton pinches in finite quotients; this computes the intersection for arbitrary gcd and identifies the exact obstruction to that proof.
  power-pair-phase-hnn-has-finite-heisenberg-mark-models: that realizes one marked compatible finite quotient; this is a structural identity inside every free pro-p completion away from the exponents.
---

Let `F=F(x_1,...,x_r)`, let `m,n` be nonzero integers, put
`d=gcd(|m|,|n|)`, and fix a prime `p` not dividing `mn`.  The substitutions
`phi_k(x_i)=x_i^k` extend to automorphisms of the free pro-`p` completion
`Fhat_p`.  For

```text
beta=phi_n phi_m^(-1) in Aut(Fhat_p)
```

one has the exact discrete intersection

```text
Graph(beta) intersect (F times F)
 ={(phi_(m/d)(a),phi_(n/d)(a)):a in F}.                 (PPGCD1)
```

In particular, coprimality is exactly what makes the profinite graph recover
the intended subgroup `{(phi_m(a),phi_n(a))}`.  If `d>1`, every compatible
quotient obtained by making both power substitutions automorphisms contains
the strictly larger gcd-saturated graph; for example
`(x_1^(m/d),x_1^(n/d))` is then indistinguishable from the target edge in all
such quotients although it is not in the original power-pair subgroup.

Thus the characteristic pro-`p` separation mechanism is sharp.  It proves
residual finiteness for the coprime HNN but supplies a concrete profinite edge
obstruction, rather than a proof, in the noncoprime case.
