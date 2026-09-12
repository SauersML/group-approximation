---
rg: 2
id: residual-finite-tensor-camouflages-iwahori-transfer-failures
kind: claim
title: Finite-quotient regular tensors camouflage every Iwahori transfer failure as canonical
distinct_from:
  canonical-iwahori-projection-commutant-transfer: that is the transfer theorem after imposing the canonical character; this proves the character condition places no restriction on tensor-stable failures for the residually finite amalgam.
  trace-conditioned-dimension-matched-kleene-diagonal: that permits a fixed-point search to demand finitely many trace tests; this makes an entire failed sequence pass every canonical trace test without changing its normalized-HS obstruction.
---

Let

```text
A=SL_2(Z[1/2])=C_+ *_(B_+=B_-) C_-                 (RFC1)
```

and suppose exact vertex representations `pi_(n,+),pi_(n,-)` have Iwahori
edge defect tending to zero, with projection witnesses `P_n` asymptotically
central for `pi_(n,+)` but with a second-vertex commutator bounded below.
Then there are finite-dimensional exact representations `lambda_n` of `A`
such that the amplified data

```text
pi'_(n,+)=pi_(n,+) tensor lambda_n|C_+,
pi'_(n,-)=pi_(n,-) tensor lambda_n|C_-,
P'_n=P_n tensor 1                                    (RFC2)
```

have exactly the same normalized-HS edge defects and projection commutator
norms, while every fixed amalgam normal form has canonical trace:

```text
tr(Phi'_n(g)) -> 1_(g=1).                            (RFC3)
```

**Proof.**  The group `A` is residually finite.  Choose finite sets
`F_n increasing A\{1}` exhausting the nonidentity elements, and a finite
quotient `q_n:A->Q_n` in which every element of `F_n` remains nontrivial.
Let `lambda_n` be the left regular representation of `Q_n`.  Its normalized
character is zero on every nonidentity element of `Q_n`.

The two restrictions of `lambda_n` agree exactly on the Iwahori edge.
Tensoring therefore changes an edge difference `R-S` to
`(R-S) tensor lambda_n(b)` and leaves its normalized HS norm unchanged.  The
same identity preserves all commutator norms with `P_n tensor 1` and both
block densities.  Evaluation of any amalgam normal form factorizes:

```text
Phi'_n(g)=Phi_n(g) tensor lambda_n(g),
tr(Phi'_n(g))=tr(Phi_n(g)) tr(lambda_n(g)).           (RFC4)
```

For fixed `g!=1`, the second factor is eventually zero because `g in F_n`.
This proves `(RFC3)` without assuming anything about the original character.

Thus scalar canonical-trace conditioning cannot remove a tensor-stable
Iwahori obstruction.  It changes only the character, not the relative
commutant geometry.
