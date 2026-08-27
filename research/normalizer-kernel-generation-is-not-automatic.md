---
rg: 2
id: normalizer-kernel-generation-is-not-automatic
kind: claim
title: Regular Cartan normalizers need not generate the Cartan through their kernel
distinct_from:
  normalizer-kernel-generation-forces-haar-action: that is the positive reconstruction under `W*(Gamma cap A)=A`; this gives an explicit amenable ICC group factor and Cartan for which all group unitaries normalize and generate the factor but their intersection with the Cartan is proper.
  full-group-subgroup-trace-generation-dichotomy: that says an essentially free full-group subgroup generates too little of the relation factor; here the group unitaries generate the entire factor, and localized finite-block coincidences generate Cartan data outside the base-unitary kernel.
---

There exist an amenable ICC group `Gamma`, its canonical group factor
`M=L(Gamma)`, and a Cartan subalgebra `A <= M` such that

```text
lambda(Gamma) <= N_M(A),       W*(lambda(Gamma))=M,
tau(lambda(g))=delta_(g,1),
```

but

```text
W*(lambda(Gamma) cap U(A))  is a proper subalgebra of A.  (NKF1)
```

One explicit example is `Gamma=S_3 wr Z`.  Consequently canonical trace plus
generation by phase-decorated/full-pseudogroup normalizers does **not** by
itself force the kernel-generated affine-Haar compact structure of
`normalizer-kernel-generation-forces-haar-action`.  Any use of that
reconstruction for the non-CE relation must prove kernel generation from
additional structure of the witness, or directly construct an algebraic
recoding.

