---
rg: 2
id: exact-cuspidal-hadamard-mixing-has-macroscopic-cross-blocks
kind: claim
title: Exact cuspidal Hadamard gauges have macroscopic cross-packet involution blocks
distinct_from:
  cuspidal-redistribution-refutes-regular-core-orbit-basin: that separates two global endpoint multiplicity types over the same core; this takes two individual equal-core irreducibles and explicitly turns their separation into large off-diagonal blocks of one exact extender.
  congruence-endpoint-orbits-are-restriction-ring-fibers: that classifies exact endpoint orbits modulo the whole core commutant; this proves that a preselected duplicate-packet block decomposition is not intrinsic even before taking that quotient.
  x-central-root-alignment-fails-inside-one-exact-stratum: that fixes one involution and varies two roots; this fixes the represented root/core literally and mixes one exact involution across duplicate core carriers.
---

Let `p=1 mod 4`, let `Q_p=PSL_2(F_p)`, and choose two distinct cuspidal
irreducibles `delta_1,delta_2` of degree `d_0=p-1`.  Their restrictions to
the standard Borel, hence to the square-free BS image `B_p`, are equivalent.
Align them so that

```text
delta_1|_(B_p)=delta_2|_(B_p)=beta_p                 (ECH1)
```

literally on one space `H_p`.  Write `X_i=delta_i(x)` for the extending
involution.  There is a quotient-independent `kappa>0` such that

```text
||X_1-X_2||_(2,d_0) >= kappa.                         (ECH2)
```

Indeed apply the congruence property-`(tau)` gap to the representation on
`Hom(H_p,H_p)`, `Z |-> delta_2(g)Z delta_1(g)^*`.  The identity is fixed by
all generators of `B_p` because of `(ECH1)`, while the two irreducibles have
no global intertwiner.  Since `B` together with `x` generates the endpoint
group, the entire Kazhdan displacement of the identity occurs in the
`x`-row, which is `(ECH2)`.

On `H_p (+) H_p`, start with the exact endpoint
`delta_1 (+) delta_2`.  Its core is `beta_p (+) beta_p`.  The core-commuting
Hadamard unitary

```text
W=2^(-1/2) [ 1   1 ]
             [ -1  1 ]                                  (ECH3)
```

leaves that core literally fixed.  The conjugated extender is

```text
X'=W diag(X_1,X_2) W^*
  =(1/2) [ X_1+X_2    -X_1+X_2 ]
          [ -X_1+X_2   X_1+X_2 ].                       (ECH4)
```

It satisfies the inversion and both cubic rows **exactly**.  Nevertheless,
relative to the two displayed copies of the complete cyclic-packet
decomposition of `beta_p`, the two off-diagonal blocks have total squared
normalized Frobenius mass

```text
(1/(2d_0)) (2/4)||X_1-X_2||_F^2
 = (1/4)||X_1-X_2||_(2,d_0)^2 >= kappa^2/4.           (ECH5)
```

Thus no raw block-matrix theorem can charge every cross block of `X` which
mixes two preselected BS packet copies by the endpoint energy: `(ECH5)` has
positive density while that energy is zero.  This remains true after
refining each copy into all of its irreducible cyclic BS packets; the
Hadamard acts on the duplicate multiplicity coordinate and commutes with
the entire exact core.

The conclusion is a sharp formulation constraint, not a counterexample to
flexible repair.  The mixed tuple is itself exact.  An intrinsic
compatibility relation may only be defined after quotienting by the full
core commutant, equivalently on the nonnegative restriction-ring fiber.
Before global atom labels are known, duplicate restriction types are gauge,
and their cross blocks are not energy-bearing.  Therefore an off-compatible
block estimate must first minimize over these exact Hadamard/kernel
directions and can seek a gap only on the quotient-normal component.
