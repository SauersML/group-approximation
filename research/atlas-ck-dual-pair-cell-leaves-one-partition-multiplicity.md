---
rg: 2
id: atlas-ck-dual-pair-cell-leaves-one-partition-multiplicity
kind: claim
title: The Atlas CK dual-pair cell is two-qubit Pauli and leaves one arbitrary partition multiplicity
distinct_from:
  atlas-root-triangle-is-heisenberg-character-fibers: that uses one coefficient-one Heisenberg triangle to split the first five central root words into D8 character fibers; this intersects four coefficient-dual triangles and identifies the exact two-qubit spin factor inside every negative fiber.
  e5-idempotent-root-has-two-pair-extraspecial-cell: that uses one idempotent coefficient on four different root positions; this uses the literal Leavitt dual pairs E,e and F,f on the same two side roots, then intersects them with the CK partition eE+fF=1.
  local-steinberg-heisenberg-packets-are-coefficient-rank-blind: that gives a general local rank-blindness countermodel; this computes the precise surviving multiplicity coordinate in the first Atlas CK cell.
  orthogonal-steinberg-root-spectral-support-is-not-additive: that gives a full finite elementary-group model proving individual root supports are not additive; this identifies the two-qubit spin factor and exact multiplicity split in the literal Atlas dual-pair cell.
  pauli-two-child-transfer-packet: that constructs two equal-trace partial-isometry branches in the raw/comb Pauli chart; this analyzes the rank-five CK root triangle and does not produce any partial-isometry transport between its two branches.
---

**ESTABLISHED EXACT LOCAL NORMAL FORM AND LOCAL NO-GO.**  Continue with the
rank-five root triangle `(1,5,2)` and put

```text
Z   = pi(x_12(1)),
X_E = pi(x_15(E)),       X_F = pi(x_15(F)),
Y_e = pi(x_52(e)),       Y_f = pi(x_52(f)).             (CKP1)
```

Here `E=e^*` and `F=f^*`.  The four Cuntz--Krieger product rules

```text
Ee=1,       Ff=1,       Ef=0,       Fe=0                (CKP2)
```

and the literal Steinberg-product rows give

```text
[X_E,Y_e]=Z,       [X_F,Y_f]=Z,
[X_E,Y_f]=1,       [X_F,Y_e]=1.                         (CKP3)
```

The same-source, same-target, orthogonal-root, and involutivity rows say that
all four actors are involutions, `X_E` commutes with `X_F`, `Y_e` commutes
with `Y_f`, and `Z` is central.  Thus `(CKP1)--(CKP3)` present the standard
two-pair extraspecial group `2_+^(1+4)` (order `32`) on the `Z=-1` sector.

Let `Q_chi` be a nonzero character atom from
`atlas-root-triangle-is-heisenberg-character-fibers` with `chi_1=-1`.
Then there is a multiplicity space `M_chi` such that

```text
Q_chi H ~= C^4 tensor M_chi,                            (CKP4)
```

and the four operators in `(CKP1)` act on `C^4` as two independent Pauli
pairs, tensored with the identity on `M_chi`.  In particular

```text
rank(Q_chi) is divisible by 4.                          (CKP5)
```

If `R_(alpha,beta)` is a joint Fourier atom of the commuting pair
`(X_E,X_F)`, then every projection `P<=Q_chi` commuting with the CK cell
satisfies

```text
tr(P R_(alpha,beta)) = (1/4) tr(P).                    (CKP6)
```

This sharpening still does not eliminate a negative `Q_chi`.  Indeed put

```text
p=eE,        q=fF,        C_p=pi(x_12(p)),
C_q=pi(x_12(q)).                                      (CKP7)
```

Spare-index independence makes these derived roots unambiguous.  Since
`p+q=1` and `pq=qp=0`, root additivity gives

```text
C_p C_q=Z,        [C_p,C_q]=1.                         (CKP8)
```

Both derived central-root involutions commute with the four actors in
`(CKP1)`.  On `Q_chi H`, where `Z=-1`, the projections

```text
P_p=(1-C_p)/2,       P_q=(1-C_q)/2                    (CKP9)
```

are complementary and belong to the extraspecial commutant.  Consequently
there is an arbitrary decomposition

```text
M_chi = M_(chi,p) direct-sum M_(chi,q),
P_p = I_4 tensor 1_(M_(chi,p)),
P_q = I_4 tensor 1_(M_(chi,q)).                        (CKP10)
```

Every split in `(CKP10)` occurs in an exact finite-dimensional model of
the relations `(CKP1)--(CKP3)` and `(CKP8)`: use the standard two-qubit
Pauli representation on `C^4`, choose an arbitrary decomposition of the
multiplicity space, let `C_p` be `-1` on the first summand and `+1` on the
second, and set `C_q=-C_p`.

Therefore the first unused CK dual-pair rows do force a common two-qubit
block decomposition, but they leave exactly one local block-coupling datum:
the multiplicity split

```text
dim M_(chi,p) : dim M_(chi,q).                         (CKP11)
```

No consequence of this CK cell and the partition row alone can force the
split to be balanced, make either branch vanish, or make the coefficient
algebra commutative.  A successful next Atlas relation must transport or
compare the two multiplicity branches outside this local extraspecial
commutant.  In particular these rows preserve every old `Q_chi`; they refine
the fibers but do not yet couple distinct characters.

For asymptotically vanishing normalized-HS packet defect, the same statement
holds in the tracial ultraproduct.  Representative-level `(CKP4)--(CKP6)`
follow after exactifying the fixed order-32 packet and averaging into its
commutant.

DERIVATION
atlas-ck-dual-pair-cell-proof
