---
rg: 2
id: extraspecial-character-hnn-two-cycle-forces-global-parity
kind: claim
title: An HNN two-cycle on the extraspecial source atom forces one global payload parity
distinct_from:
  extraspecial-fourier-zero-cell-is-fixed-face-pruning: that rules out finite and residually finite normalizer completions by inducing the shear-fixed character; this treats a possibly nonnormal character-idempotent source-target HNN cell and computes exactly when its Hecke compression can vanish.
  central-pinning-forbids-nonlinear-predicates: that bounds eigenspaces of individual group involutions in a uniquely marked finite packet; this permits an arbitrary HNN target subgroup and derives a payload parity relation from character disagreement on the source-target intersection.
  heisenberg-subgroup-cuts-are-affine-stabilizer-flats: that classifies cuts made by Pauli subgroup characters; this proves the four proposed positive cells fail to compose even though their common gauge and Hermitian-corrector interfaces are both exact.
---

Retain the extraspecial controller notation with `K=F_2^k`, and after the
stabilizer corrector put

```text
V=SC,                 U_i=S W_i S^(-1),
H=<J,X_1,...,X_k>,
q=2^(-(k+1))(1-J) product_i(1+X_i).                  (ECH1)
```

Thus `q` is the character idempotent of the finite abelian group `H` for

```text
chi(J)=-1,            chi(X_i)=1.                    (ECH2)
```

The established common-gauge and corrector relations give

```text
V^2=1,       VJV=J,       VX_iV=U_iX_i,              (ECH3)
```

where the `U_i` are commuting involutions commuting with `H`.

Suppose one tries to use `V` as a character-idempotent HNN source-target
two-cycle. Then the exact regular Hecke compression satisfies

```text
qVq=0
 iff there exist a,c in F_2^k with U_a=JX_c,          (ECH4)
```

where `U_a=product_i U_i^(a_i)` and similarly for `X_c`. In any tensor-spin
completion in which `H` acts on the Pauli factor and the `U_i` act on the
payload multiplicity, `(ECH4)` reduces to

```text
U_a=-1                                                 (ECH5)
```

for some nonzero `a`. Thus an HNN source-target implementation does not
express absence of the trivial payload character. It expresses the strictly
stronger condition that the entire payload spectrum lies in one affine
hyperplane.

This distinction is sharp for every `k>1`. Let the payload multiplicity be

```text
ell^2(K^dual \ {0})
```

and let the `U_i` act diagonally by all nontrivial characters. The common
fixed projection `P_K` is zero, so the extraspecial controller has
`qCq=0`; take common gauge `A=1` and corrector `S=1`, making `V=C` an
involution. But no `U_a` is `-1`: for each nonzero `a`, the kernel of
`chi |-> <a,chi>` contains a nonzero character when `k>1`. Hence this exact
zero-compression completion cannot satisfy any character-HNN two-cycle
relation enforcing `(ECH4)`.

Nor can the source be identified with the literal two-grading source of
`central-marked-two-cycle-zero-compression-cell`. If the marked Pauli
subgroup embeds, `q` has regular trace `2^(-(k+1))`, whereas a nondegenerate
two-grading source `(1-y)(1-z)/4` has regular trace `1/4`. Equivalently the
former has `2^(k+1)` nonzero group-basis coefficients and the latter at most
four. For `k>1` they cannot be the same group-algebra projection.

Therefore the four positive ingredients do not close
`tailored-checks-to-common-marked-group-extensions` for a general
commuting-context losing atom of rank `k>1`. They remove the SELECT gauge
and Hermitianization obstructions, but their source interfaces do not
compose: literal two-gradings have the wrong carrier, while an HNN transport
of the correct character carrier enforces one global parity rather than
zero trivial-character mass. A surviving cell must authenticate a small
character carrier without realizing its zero compression through a single
source-target Hecke intersection.
