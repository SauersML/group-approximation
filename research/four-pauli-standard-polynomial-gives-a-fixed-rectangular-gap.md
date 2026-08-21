---
rg: 2
id: four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap
kind: claim
title: Four Pauli words give an explicit amplification-blind gap against the rectangular escape
distinct_from:
  fixed-pi-degree-fingerprints-packet-label-factor: that states the general fixed-degree PI strategy conditionally on a full target tuple; this gives the first explicit tuple and a robust numerical inequality at source degree two.
  rectangular-escape: that constructs the label-doubling/multiplicity-halving countermodel; this proves a fixed scalar test which detects exactly that conversion once one common transported tuple is exposed.
  universal-tracial-certificates-cannot-force-eight-slice-overlap: that forbids a universal tracial proof of the final BCS actuator; the inequality here is a universal analytic endpoint and therefore does not supply the matrix-only common-carrier decoder by itself.
---

Let

```text
s4(A,B,C,D)=sum_(pi in S4) sgn(pi)
             A_(pi(1)) A_(pi(2)) A_(pi(3)) A_(pi(4)).       (FPS1)
```

There is a completely explicit, dimension-free standard-polynomial detector
for the first rectangular enlargement `M_2 tensor I_m -> M_4 tensor I_(m/2)`.
It is invariant under arbitrary spectator amplification.

### The robust four-Pauli inequality

Let `A,B,C,D` be unitaries in a finite tracial von Neumann algebra.  Assume

```text
||AB+BA||_2, ||CD+DC||_2 <= epsilon,                       (FPS2)
||[A,C]||_2, ||[A,D]||_2, ||[B,C]||_2, ||[B,D]||_2
                                                   <= epsilon. (FPS3)
```

Then

```text
||s4(A,B,C,D)||_2 >= 8-144 epsilon.                        (FPS4)
```

Indeed, reorder each of the `24` monomials in `(FPS1)` to `ABCD`.  At most
six adjacent swaps are required.  Each swap costs at most `epsilon` in
Hilbert--Schmidt norm because all surrounding factors are unitary.  Under the
exact signed commutation rules the signed sum is

```text
s4(A,B,C,D)=8ABCD.                                         (FPS5)
```

Thus the accumulated perturbation is at most `24*6 epsilon`, while
`||8ABCD||_2=8`.

The coefficient and the lower bound are witnessed by the canonical two-qubit
tuple

```text
A=I tensor X,  B=I tensor Z,
C=X tensor I,  D=Z tensor I,                              (FPS6)
```

for which

```text
s4(A,B,C,D)=8 (XZ tensor XZ),
||s4(A,B,C,D)||_2=8.                                      (FPS7)
```

### The source-degree upper bound

Suppose the same four unitaries are each within `delta` in normalized
Hilbert--Schmidt norm of one common unital copy

```text
B0 ~= M_2 tensor I_m.                                     (FPS8)
```

Then Amitsur--Levitzki gives `s4=0` on `B0`, and multilinearity gives

```text
||s4(A,B,C,D)||_2 <= 96 delta.                            (FPS9)
```

To see the constant, choose contraction approximants in `B0`.  Each of the
`24` degree-four monomials changes by at most `4 delta`.

Combining `(FPS4)` and `(FPS9)` yields the explicit incompatibility

```text
144 epsilon + 96 delta >= 8.                              (FPS10)
```

In particular, if all six Pauli relation errors and all four source-factor
distances are at most one common number `eta`, then

```text
eta >= 1/30.                                               (FPS11)
```

All norms and constants are unchanged by tensoring every operator with an
identity of arbitrary size.  If the calculation is performed on a common
corner of ambient trace at least `alpha`, the corresponding ambient
Hilbert--Schmidt floor is obtained by multiplying the exact corner signal by
`sqrt(alpha)` (or, equivalently, by first normalizing the corner trace).

### What this closes

The exact rectangular countermodel cannot hide from `(FPS10)`: its source
label algebra is `M_2 tensor I_2`, while its target direct-sum pairing is the
two-qubit factor `M_4`; the four canonical target Weyl words are precisely
`(FPS6)`.  Trading label degree for spectator multiplicity does not alter
either side of the scalar test.  Thus **rank counting is no longer needed
after one common four-word tuple has been transported across the cycle**.

This also removes the vague target-fullness clause from the degree-two case.
It is enough to recover four fixed target words satisfying the two Pauli
anticommutation relations and four cross-commutation relations.  One does not
need to prove separately that they generate all of `M_4`.

### Claim boundary and the two firewalls

This is not a non-hyperlinearity proof.  The remaining statement is genuinely
matrix-coordinate: the presentation must make the **same** four returned
words simultaneously

1. lie near the source `M_2` label factor on one positive-density carrier;
   and
2. satisfy the target two-qubit Pauli relations there.

If both conclusions followed from universal identities in every tracial
representation, `(FPS10)` would also kill the regular representation.  Thus
the common-carrier/source-confinement step must use finite matrix
multiplicity or the non-Connes-embeddable source moments; it cannot be a
cyclic SOS or finite-packet character-table argument.  Conversely, merely
recovering the source and target tuples on unrelated corners leaves the
rectangular escape intact.  The word `same` remains load-bearing, but the
analytic endpoint after that word is now the fixed numerical floor
`1/30`.
