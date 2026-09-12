# Commuting target packets synchronize transition measurements

Date: 2026-08-14

## 1. Outcome

The multi-edge transition problem has a sufficient criterion stated entirely
before PVM rounding. Let `P` be a projection in a finite tracial matrix
algebra, and let `(E_i)_(i in I)` and `(F_j)_(j in J)` be finite PVMs. Put

```text
A_i=P E_i P,                B_j=P F_j P,             (CTS1)

delta_E=sum_i ||[P,E_i]||_2^2,
delta_F=sum_j ||[P,F_j]||_2^2,
kappa=sum_(i,j)||[E_i,F_j]||_2^2.                   (CTS2)
```

Then `(A_i)` and `(B_j)` are POVMs in `PMP`, and their total commutator
energy satisfies

```text
sqrt(sum_(i,j)||[A_i,B_j]||_2^2)
 <=sqrt(kappa)+sqrt(delta_E/2)+sqrt(delta_F/2).      (CTS3)
```

In particular, if the two target PVMs commute and both have vanishing total
leakage across the common source cut, their transition POVMs asymptotically
commute with no dependence on `|I|` or `|J|`.

Round `(A_i)` and `(B_j)` separately by de la Salle's theorem to PVMs
`(R_i)` and `(S_j)` in `PMP`. They may be chosen so that

```text
eta_R=sum_i||R_i-A_i||_2^2 <=(9/2)delta_E,
eta_S=sum_j||S_j-B_j||_2^2 <=(9/2)delta_F.           (CTS4)
```

The rounded PVMs still satisfy the cardinality-free estimate

```text
sqrt(C(R,S))
 <=sqrt(C(A,B))+sqrt(2 eta_R)+2 sqrt(eta_S).         (CTS5)
```

Therefore `kappa,delta_E,delta_F ->0` implies `C(R,S)->0`. Combined with
`TRUE_PATH_PVMS_CLASSICALIZE_WITHOUT_OUTCOME_LOSS.md`, this yields exact
commuting PVMs on all three edges of the required path after an `o(1)`
perturbation.

This changes the atlas target. A general simultaneous-measurement theorem is
unnecessary if the raw/four-root routing can place the two target character
packets for each required edge in commuting root positions on one common
source cut.

## 2. Compression estimate

For every `i,j`, insert `1=P+(1-P)` between the target projections. Direct
expansion gives

```text
[A_i,B_j]
 =P[E_i,F_j]P
  -P E_i(1-P)F_jP
  +P F_j(1-P)E_iP.                                  (CTS6)
```

The Hilbert direct-sum triangle inequality over `(i,j)` controls the first
family in `(CTS6)` by `sqrt(kappa)`. For the second family, write

```text
X_ij=P E_i(1-P)F_jP.                                (CTS7)
```

Since `sum_j F_j P F_j <=sum_j F_j=1`, positivity and cyclicity of the
trace give

```text
sum_j||X_ij||_2^2
 <=||(1-P)E_iP||_2^2.                               (CTS8)
```

Summing over `i` and using the two off-diagonal blocks of a projection,

```text
sum_(i,j)||X_ij||_2^2 <=delta_E/2.                  (CTS9)
```

The third family has squared direct-sum norm at most `delta_F/2` by the same
argument with `E` and `F` exchanged. This proves `(CTS3)`. Notice that
`(CTS3)` remains valid for approximately commuting target PVMs; exact
target commutation is merely the case `kappa=0`.

## 3. Rounding does not reintroduce an alphabet loss

The transition-effect variance identity gives

```text
sum_i tau(A_i-A_i^2)=delta_E/2,
sum_j tau(B_j-B_j^2)=delta_F/2.                     (CTS10)
```

De la Salle's cardinality-free POVM orthogonalization applied in `PMP`
therefore gives `(CTS4)`.

Set `D_i=R_i-A_i` and `G_j=S_j-B_j`. These are self-adjoint. Because `(S_j)`
is a PVM, the block-expectation identity gives

```text
sum_(i,j)||[D_i,S_j]||_2^2 <=2 sum_i||D_i||_2^2.    (CTS11)
```

For a positive POVM `(A_i)` one has `sum_i A_i^2<=sum_i A_i=P<=1`. Hence,
for every self-adjoint `X`,

```text
sum_i||[A_i,X]||_2^2 <=4||X||_2^2.                 (CTS12)
```

Finally,

```text
[R_i,S_j]=[A_i,B_j]+[D_i,S_j]+[A_i,G_j].            (CTS13)
```

Apply the Hilbert direct-sum triangle inequality to `(CTS13)`, then use
`(CTS11)--(CTS12)`. This proves `(CTS5)`.

An explicit consequence of `(CTS3)--(CTS5)` is

```text
sqrt(C(R,S))
 <=sqrt(kappa)
   +(3+1/sqrt(2))sqrt(delta_E)
   +(3sqrt(2)+1/sqrt(2))sqrt(delta_F).              (CTS14)
```

The asymmetric constants only reflect the order chosen in `(CTS13)`; their
values are irrelevant for a vanishing-defect argument.

## 4. Application test for the Leavitt atlas

For each of the three paired-quotient contexts `(R0,L0)`, `(R0,L1)`, and
`(R1,L1)`, it is now enough to exhibit:

1. one common positive-density source carrier `P`;
2. two complete finite target character PVMs occupying commuting root
   packets, or target commutator energy `kappa=o(1)`;
3. the already proved covariance leakage bounds
   `delta_E,delta_F=o(1)`; and
4. a deterministic character decoder whose trace mismatch for the relevant
   identity `t_i s_j=delta_ij` is `o(1)`.

Items 2 and 4 are the live routing statements. Item 3 is supplied on every
single edge by `TRUE_COVARIANCE_CONTROLS_TOTAL_TRANSITION_VARIANCE.md`, and
all rounding and three-edge assembly after these inputs is now
cardinality-free.

The fixed Pauli countermodel is consistent with the criterion: its adjacent
target character packets do not have `kappa=0`. Thus this theorem does not
classicalize the local Pauli algebra by fiat; it isolates exactly the
additional distant-root/common-carrier geometry that the raw routing must
provide.
