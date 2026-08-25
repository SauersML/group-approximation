---
rg: 2
id: dyadic-pauli-payload-flags-supply-strict-target-capacity
kind: claim
title: Dyadic Pauli flags give every forbidden atom an arbitrarily small strict target-capacity deficit
distinct_from:
  schur-pauli-words-name-atomwise-half-quarter-flags: that names one half and one quarter for the Schur return; this uses an arbitrary finite Pauli depth and takes the complement of the deepest flag to approach the sharp factor-two target capacity from below.
  one-bit-clifford-selector-halves-a-chosen-bcs-atom: that extracts one balanced positive half; this simultaneously names a source half and a larger target whose ratio is `2-kappa`.
  finite-packet-flow-keeps-payload-orientation-balanced: that rules out producing an oriented balanced-HNN gap from finite stationary packet flow; this produces only the scalar source/target capacity deficit and explicitly leaves the rectangular row-map coupling open.
  rectangular-three-row-cell-forces-double-target-capacity: that converts a strict capacity deficit plus three rectangular rows into an HS floor; this supplies the deficit projections with arbitrary dyadic `kappa`.
---

**ESTABLISHED CAPACITY FRONT END.**  Fix a forbidden assignment atom `C` on
the marked `J=-1` BCS sector.  For every `n>=1`, adjoin a finite extraspecial
Pauli packet with involutions

```text
X_1,Z_1,...,X_n,Z_n
```

such that distinct pairs commute, every packet word commutes with the context
tuple defining `C`, and

```text
X_j Z_j X_j=J Z_j.                                    (DPF1)
```

On `C`, where `J=-1`, the `X_j` independently flip the `Z_j` signs.  Put

```text
D_n=C product_(j=1)^n (1-Z_j)/2,
E=C(1-Z_1)/2,
F_n=C-D_n.                                             (DPF2)
```

Then `D_n,E,F_n` are literal finite-group-algebra projections and in every
exact tracial representation

```text
tau(D_n)=2^(-n)tau(C),
tau(E)=tau(C)/2,
tau(F_n)=(1-2^(-n))tau(C)
        =(2-kappa_n)tau(E),
kappa_n=2^(1-n)>0.                                     (DPF3)
```

The same formulas hold after compression by any projection `Q` reducing the
shared context and Pauli packet, with `C` replaced by `QC`.  Thus positive
`kappa` may be made arbitrarily small while the packet and the ordinary-word
formulas remain finite for each chosen `n`.

Apply this to a maximal forbidden atom on a reducing carrier.  The robust
BCS gap and maximal selection give

```text
tau(QC)>=beta tau(Q)/M-O(sqrt(E_pres)),                (DPF4)
```

so the source half satisfies

```text
tau(QE)>=beta tau(Q)/(2M)-O(sqrt(E_pres)).             (DPF5)
```

Finite-group HS exactification perturbs `(DPF3)` by only
`O_n(sqrt(E_pres))`, independently of matrix dimension.  Consequently the
strict target-capacity row needed by
`rectangular-three-row-cell-forces-double-target-capacity` is already
available with any fixed dyadic `kappa_n`; nonlinear predicate decoding and
the scalar capacity ledger are not the remaining obstruction.

The exact perfect BCS/Leavitt model survives this extension.  Every forbidden
atom has `C=0`, hence

```text
D_n=E=F_n=0.                                           (DPF6)
```

The finite Pauli packet itself is realized on an auxiliary matrix tensor
factor (or after countable amplification), so no new perfect-model
constraint remains.

## Sharp regular-trace fence

The Pauli flags do **not** supply the rectangular maps.  If contractions

```text
s_i in F_n M E,             t_i in E M F_n
```

were obtained functorially from fixed packet words and satisfied

```text
t_0s_0=E,             t_1s_1=E,             t_0s_1=0  (DPF7)
```

as universal group-algebra consequences, apply them in the faithful left
regular finite factor.  The forbidden packet atom `C` is nonzero whenever
its context subgroup remains injected, so `(DPF3)` gives

```text
tau(F_n)=(2-kappa_n)tau(E)<2tau(E).
```

This contradicts
`rectangular-three-row-cell-forces-double-target-capacity`.  Equivalently,
the same contradiction applies to any tracially functorial extraction made
from fixed packet averaging, compression, polar/support calculus, or fixed
matrix amplification.

Therefore the capacity row itself is solved, but a phase-safe finite packet
cannot attach the three Leavitt rows to it.  The remaining datum is exactly
one nonfunctorial occurrence-synchronization theorem: the finite canonical
microstate must decode the two inverse maps and crossed product through the
**same** named pair `(E,F_n)`, while the regular Leavitt representation keeps
the typed rectangular maps on its saturated doubled target instead.  More
finite Pauli bits only tune `kappa`; they cannot supply that synchronization.

DERIVATION
dyadic-pauli-payload-capacity-proof
