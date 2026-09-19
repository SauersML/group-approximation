# Self-reference challenger to Hilbert--Schmidt breaker

## Ingestion status

The supplied construction notebook separates the adversarial route into three
modules:

```text
dimension-matched Kleene diagonal
        -> finite Clifford same-model breaker
        -> finite-presentation table activator.                         (SCB0)
```

The first two modules are already theorem-grade in Cairn. They are recorded as
`dimension-matched-kleene-microstate-diagonal` and
`marked-clifford-table-exponential-dimension`. The third is the live hole
`adaptive-all-pairs-schur-replica-table-compiler` and its machine-indexed
variants. This artifact records the exact interface and prevents the completed
front and back ends from being repeatedly reproved.

The notebook's executive paragraph also announces a low-dimensional
hyperoctahedral constraint packet. The supplied excerpt ends after the
Clifford breaker and does not include that packet's definition or proof, so no
new hyperoctahedral theorem is credited from the excerpt alone. Cairn already
contains the separate established nodes
`all-bcs-contexts-share-one-hyperoctahedral-signed-type` and
`tracial-bcs-has-rational-balanced-hyperoctahedral-atlas`.

## Exact dimension-matched compiler interface

A total computable compiler sends a program index `e` to

```text
(Gamma_e=<S_e|R_e>, w_e, delta_e, alpha_e),
delta_e>0,                      0<alpha_e<sqrt(2),       (SCB1)
```

with:

```text
e does not halt => w_e != 1 in Gamma_e,                 (SCB2)

e halts and prints d
 => every U in U(d)^S_e with Def_(R_e)(U)<delta_e
    has ||w_e(U)-I||_2<=alpha_e.                         (SCB3)
```

Kleene's recursion theorem makes a program search computably dense algebraic
unitary tuples for strict inequalities

```text
Def(U)<delta'_e<delta_e,
||w_e(U)-I||_2>beta_e>alpha_e.                           (SCB4)
```

If it finds a witness, it prints that witness's own dimension. Then `(SCB3)`
contradicts `(SCB4)`, so the program does not halt and `(SCB2)` keeps the word
nontrivial. Hyperlinearity would give microstates with defect tending to zero
and marked distance tending to `sqrt(2)`; density would make the search halt.
Thus the compiled group is nonhyperlinear.

The decisive point is that the backend need defeat only the dimension printed
by the self-search. It does not need an operator-internal dimension sensor and
does not need to control every finite dimension simultaneously. The positive
threshold must nevertheless be computable from the source program before the
search; a threshold learned only as a function of the eventual dimension is
not enough without a positive tensor-amplification envelope.

## Exact finite Clifford breaker

Let `E_N` be the extraspecial Pauli group with central involution `J` and
relations

```text
[X_i,Z_i]=J,
all other Pauli pairs commute.                            (SCB5)
```

If `f:E_N->U(d)` is an all-pairs `epsilon`-homomorphism with `epsilon<1/2`
and

```text
||f(J)-I||_2>42 epsilon,                                 (SCB6)
```

Gowers--Hatami exactification gives a representation `rho:E_N->U(m)` with

```text
d<=m<=d/(1-4epsilon^2)                                  (SCB7)
```

whose compressed central sign is within `42 epsilon` of `f(J)`. Condition
`(SCB6)` forces a nonzero `J=-1` summand. The marked group algebra on that
summand is `M_(2^N)(C)`, so `m>=2^N`. Therefore

```text
d >= (1-4epsilon^2) 2^N.                                (SCB8)
```

After a program prints `d`, choosing

```text
N=1+ceil(log_2(d/(1-4epsilon_0^2)))                      (SCB9)
```

makes a marked all-pairs table impossible in that same matrix model.

## Remaining bridge

The compiler must activate the complete multiplication table selected by the
halting computation from finitely many group relators with

```text
epsilon_table <= C Def_R(U),                             (SCB10)
```

where `C` is independent of the printed dimension, Clifford rank, and runtime.
Writing a growing table literally, evaluating long normal forms, or union
bounding separate local exactifications introduces rank/runtime dependence.
This is the remaining invariant HS-PCP/table-synthesis problem. Neither the
Kleene theorem nor the Clifford capacity estimate supplies it.

