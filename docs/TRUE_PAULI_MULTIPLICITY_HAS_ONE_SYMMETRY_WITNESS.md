# One symmetry witnesses the Pauli multiplicity variance

Date: 2026-08-14

## 1. Outcome

The multiplicity-scalarization gate in
`TRUE_PAULI_BINARY_GAP_IS_MULTIPLICITY_VARIANCE.md` does not require recovery
of an entire coefficient algebra at the terminal step. In every finite
matrix coordinate, one self-adjoint involution in the binary commutant
already witnesses the full obstruction.

For the actual Pauli packet, put

```text
E=PQ,              F=U*QU,
tau(E)=1/8,        tau(F)=1/4,        tau(EF)=1/32,
Phi_E(F)=EFE+(1-E)F(1-E).
```

There is a self-adjoint involution `V` such that

```text
[V,E]=0,
||[V,Phi_E(F)]||_2^2 >= 1/4.                         (PSW1)
```

The bound is dimension independent. Thus the unresolved coordinate theorem
can be stated as a one-involution relative-bicommutant problem: a successful
nonhyperlinearity proof only has to rule out the coordinate-dependent
symmetries in `(PSW1)`, rather than explicitly identify both diagonal
multiplicity algebras.

## 2. Balanced-symmetry averaging

Let `M_m(C)` have normalized trace and let `X=X*` satisfy `tr(X)=0`. For
`m>=2`, choose a diagonal symmetry `J_m=J_m*=J_m^(-1)` whose `+1` and `-1`
multiplicities differ by at most one. Hence

```text
|Tr(J_m)| <= 1.                                      (PSW2)
```

Average the conjugates `U J_m U*` over Haar measure on `U(m)`. The resulting
conjugation channel is scalar on the traceless matrices. Its scalar is

```text
alpha_m=(|Tr(J_m)|^2-1)/(m^2-1),                    (PSW3)
```

because the superoperator trace of `Ad(J_m)` is `|Tr(J_m)|^2`, while the
scalar matrices contribute the eigenvalue `1`. Equation `(PSW2)` gives
`alpha_m<=0`. Consequently

```text
integral ||[U J_m U*,X]||_2^2 dU
  =2(1-alpha_m)||X||_2^2
  >=2||X||_2^2.                                     (PSW4)
```

When `m=1`, a centered `X` is zero, so the same conclusion is vacuous.

Now let `E` be a projection in `M_d(C)` and suppose `X=X*` is block diagonal
and centered separately on the two `E`-blocks:

```text
[E,X]=0,
tr(EX)=0,          tr((1-E)X)=0.                    (PSW5)
```

Apply `(PSW4)` independently to the two nonzero blocks and take a pair at
least as large as the product-Haar average. The direct sum is a
self-adjoint involution `V` with `[V,E]=0` and

```text
||[V,X]||_2^2 >= 2||X||_2^2.                        (PSW6)
```

This is an existence theorem in each finite coordinate. It uses no
spectral-gap hypothesis and no lower bound on either block rank.

## 3. Application to the actual packet

Set

```text
X=Phi_E(F)-(1/4)1.                                  (PSW7)
```

The fixed overlap makes both block traces vanish:

```text
tau(EX)=tau(EF)-(1/4)tau(E)=1/32-1/32=0,
tau((1-E)X)=tau(F)-tau(EF)-(1/4)(1-tau(E))=0.        (PSW8)
```

Writing

```text
y=tau(EFEF)=||EFE||_2^2>=0,
```

the preceding multiplicity calculation gives

```text
||X||_2^2=1/8+2y.                                   (PSW9)
```

Equations `(PSW6)` and `(PSW9)` yield the sharper parameterized bound

```text
||[V,Phi_E(F)]||_2^2
 =||[V,X]||_2^2
 >=1/4+4y
 >=1/4.                                             (PSW10)
```

The scalar endpoint `1/4+4y` and its `1/4` floor are formalized source-first
in `GroupApproximation/Leavitt/PauliCarrierBinaryGap.lean`. No build or
computation was run for this edit.

## 4. Exact scope

This is not yet a nonhyperlinear group. The regular representation contains
the same matrix-block geometry, and the witness `V` is selected separately
at each finite coordinate; it is not a fixed group word.

The advance is a stricter stopping rule. One no longer needs to demand an
explicit reconstruction of the full `N` in

```text
M_2(C) tensor N.
```

It is enough to prove the following single-symmetry statement for a
hypothetical trace-preserving matrix model of the atlas presentation:

> every self-adjoint involution which commutes with the recovered parent cut
> `E_n` has commutator `o(1)` with the block-diagonal transported carrier
> `Phi_(E_n)(F_n)`.

That assertion contradicts `(PSW10)` immediately. It remains genuinely
matrix-specific: an abstract finite-von-Neumann-algebra bicommutant argument
would also apply to the regular model and is false there. The next useful
relation must therefore bind one coordinate commutant symmetry to the
cross-root multiplication module; adding another fixed Pauli commutator
cannot do so.
