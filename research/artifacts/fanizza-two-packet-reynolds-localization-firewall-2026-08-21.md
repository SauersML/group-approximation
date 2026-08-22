# Two fixed packet Reynolds actions leave the Gram spectator untouched

## Reynolds averaging points toward the commutant

Let `K` be a finite group with a unitary representation `rho` on a finite
dimensional carrier.  Its conjugation Reynolds operator is

```text
R_K(T)=|K|^(-1) sum_(k in K) rho(k) T rho(k)^*.          (TPR1)
```

The range of `(TPR1)` is `rho(K)'`, not `rho(K)''`.  Thus averaging by the
label packet makes an operator a multiplicity-coordinate operator.  To
project into the label algebra one must average over a generating family of
the full multiplicity commutant.

Adding a second fixed packet does not reverse this direction.  If `A_0` and
`B_0` are any two fixed semisimple packet algebras on `V`, put

```text
C_0=C^*(A_0,B_0) subset End(V).                         (TPR2)
```

On

```text
H_N=V tensor C^N                                       (TPR3)
```

represent both packets by amplification:

```text
A_N=A_0 tensor I_N,          B_N=B_0 tensor I_N.        (TPR4)
```

Every exact internal and mixed relation of the fixed pair is unchanged.
For every projection `Q in M_N(C)`, however,

```text
q_N=I_V tensor Q                                       (TPR5)
```

commutes with both packets.  It is fixed by both Reynolds maps, by every
finite composition of them, and by conjugation averaging over every packet
word.  Unless `Q` is scalar, `q_N` is not in `C_0 tensor I_N`.  Its
normalized trace is

```text
tr(q_N)=rank(Q)/N,                                      (TPR6)
```

so the surviving Gram spectator can have any asymptotic density.

This remains true in the strongest fixed-label case `C_0=End(V)`.  Then

```text
(C_0 tensor I_N)'=I_V tensor M_N(C),                   (TPR7)
```

and `(TPR5)` is exactly the whole anonymous multiplicity factor.

## Smallest Fanizza-compatible instances

For two genuinely distinct packet factors, take

```text
H_N=C^2 tensor C^2 tensor C^N.                          (TPR8)
```

Let the first D8 image generate `A_0=M_2 tensor I_2`.  Put
`W=CZ times SWAP` on the two qubits and let the second D8 image generate
`B_0=W A_0 W^*`.  If the first packet has Pauli generators `X_1,Z_1`, the
second has generators `Z_1X_2,Z_2`.  Thus the two packet actions do not
commute, and together they generate `M_4(C)`: `A_0` supplies `Z_1`, so the
second packet's `Z_1X_2` supplies `X_2`, while it also supplies `Z_2`.

Their common commutant on `(TPR8)` is exactly `I_4 tensor M_N`, yet every

```text
q_N=I_2 tensor I_2 tensor Q                             (TPR9)
```

survives all packet and selector Reynolds tests.  This is the smallest
two-qubit noncommuting pair with distinct full `M_2` packet factors.  Adding
any fixed C18 truth-table selector only enlarges the bounded label factor
and leaves an amplified spectator of the form `(TPR9)`.

The same model works on a central selected atom `E`: compress `(TPR8)` to
the packet sector `EV`, and use the identity of that sector in `(TPR5)`.
Thus positive-density selection does not remove the spectator gauge.

## Why a fixed mutual-commutant pair is impossible at unbounded multiplicity

To use a second packet `B_N` to Reynolds-project into `A_N`, one needs

```text
B_N=A_N'=I_r tensor M_N(C)                              (TPR10)
```

on each simple `A_N=M_r tensor I_N` sector.  A fixed finite-dimensional
semisimple algebra cannot satisfy `(TPR10)` for unbounded `N`: its simple
degrees are bounded.  In any sequence of representations of growing total
dimension, some irreducible occurs with unbounded multiplicity, leaving a
non-scalar matrix algebra in the commutant.

This is the exact finite-packet obstruction behind the warning in
`common-corner-mutual-bicommutant-extraction`.  Two fixed packet actions can
exhaust a fixed label coordinate, but cannot become mutual commutants on an
unbounded carrier.  The second side must be scalable, or mixed relations
must make the spectator gauge itself word-visible.

## Consequence for the Fanizza Gram

The quantization gap in
`fixed-semisimple-trace-charts-cannot-authenticate-proper-fullness` applies
only after the deficiency

```text
q=E-X^*X                                                (TPR11)
```

has been placed in the packet algebra coordinate.  Commutation with two
fixed C18/D8 packet actions, invariance under their Reynolds maps, or exact
mixed relations confined to their bounded joint label algebra do not do
this: `(TPR9)` is a zero-defect countermodel.

The surviving localization gate is therefore narrower than “add a second
noncommuting packet.”  It must either generate the full scalable
multiplicity algebra on the selected carrier, or impose a mixed word whose
value changes under `q -> I_label tensor Q`.  A fixed double finite packet
with only Reynolds/covariance tests is rank blind.
