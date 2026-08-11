# The prime-two parity cokernel is a simultaneous Bockstein quotient

Date: 2026-08-11

## 1. Outcome

The finite-support cokernel isolated in
`FALSE_SPARSE_SYNDROME_COMPACTNESS.md` has an exact standard homological
description.

Let `X` be the limiting Laurent presentation cover, let `tau` be its free
cellular deck involution, and put

`Y=<tau>\X`.                                           `(BTI1)`

Let `Z_+` be the trivial integral local system on `Y` and let `Z_-` be the
sign local system associated with the double cover `X->Y`.  Both reduce
modulo two to the trivial system `F_2`.  Write

`beta_+:H_2(Y;F_2)->H_1(Y;Z_+)`,
`beta_-:H_2(Y;F_2)->H_1(Y;Z_-)`                       `(BTI2)`

for the connecting maps of

`0->Z_+ --2--> Z_+ ->F_2->0`,
`0->Z_- --2--> Z_- ->F_2->0`.                         `(BTI3)`

Then the parity-cycle cokernel is canonically

`V/(red_2 Z_2^+ + red_2 Z_2^-)`
` ~=H_2(Y;F_2)/(ker(beta_+)+ker(beta_-)).`             `(BTI4)`

Here `V` is the group of finite-support `tau`-invariant binary two-cycles
on `X`, while `Z_2^+` and `Z_2^-` are the finite-support integral invariant
and anti-invariant two-cycle groups.

Consequently the parity-only escape branch occurs only if one fixed
mod-two class is simultaneously nonliftable to an ordinary integral
two-cycle and to a sign-twisted integral two-cycle.  More precisely, the
class extracted in the sparse compactness theorem lies outside both
Bockstein kernels and outside their sum.

This is a complete identification, not yet a computation of the quotient
for the Laurent group.  The FALSE-side local-primary task is now to decide
whether the two kernels in `(BTI4)` span `H_2(Y;F_2)`.

## 2. Chain identifications for a free involution

Let `C_*(X;Z)` denote finite-support cellular chains.  Since `tau` acts
freely on cells, choose one lift of every cell of `Y`.  The maps

`e |-> e+tau e`,
`e |-> e-tau e`                                       `(BTI5)`

identify

`C_*(Y;Z_+) ~= C_*(X;Z)^(tau=+1)`,
`C_*(Y;Z_-) ~= C_*(X;Z)^(tau=-1)`.                    `(BTI6)`

The second formula is precisely the cellular sign local system: changing a
lift by `tau` changes the chosen generator by `-1`.

After reduction modulo two the two formulas in `(BTI5)` agree.  Both
identify `C_*(Y;F_2)` with the `tau`-invariant binary chains on `X`.
Consequently

`Z_2(Y;F_2) ~= V`,                                    `(BTI7)`

and the two reduction maps on integral cycles correspond exactly to

`red_2 Z_2^+`, `red_2 Z_2^- <=V`.                     `(BTI8)`

All chain groups here are direct sums, so finite support is preserved in
both directions.

## 3. Cycle-level form of the Bockstein sequence

The following elementary lemma keeps track of representatives rather than
only homology classes.

**Lemma 1.**  Let `L` be either `Z_+` or `Z_-`, and let

`beta_L:H_2(Y;F_2)->H_1(Y;L)`                         `(BTI9)`

be the connecting map from `(BTI3)`.  A finite-support binary two-cycle
`epsilon` is the reduction of a finite-support integral `L`-cycle if and
only if

`beta_L([epsilon])=0`.                                `(BTI10)`

**Proof.**  One implication is immediate from exactness.  Conversely,
suppose `[epsilon]` is in the kernel.  Exactness gives an integral
`L`-homology class represented by a cycle `z` whose reduction is homologous
to `epsilon`.  Thus

`epsilon-red_2(z)=d bar(c)`                            `(BTI11)`

for a finite-support binary three-chain `bar(c)`.  Lift `bar(c)`
coordinatewise to an integral `L`-chain `c`.  Then `z+d c` is an integral
cycle and

`red_2(z+d c)=epsilon`.                               `(BTI12)`

End proof.

One can also see `(BTI10)` directly: lift `epsilon` integrally.  Its
boundary is even, and half that boundary represents the Bockstein class.
Vanishing is exactly the possibility of correcting the lift to an integral
cycle.

## 4. Proof of the simultaneous quotient formula

Let

`rho_+:Z_2(Y;Z_+)->Z_2(Y;F_2)`,
`rho_-:Z_2(Y;Z_-)->Z_2(Y;F_2)`                        `(BTI13)`

be reduction on cycles.  Lemma 1 says

`rho_+(Z_2(Y;Z_+))`
` ={epsilon:[epsilon] in ker(beta_+)}`,
`rho_-(Z_2(Y;Z_-))`
` ={epsilon:[epsilon] in ker(beta_-)}`.               `(BTI14)`

Every binary boundary belongs to each image in `(BTI14)`: lift a binary
three-chain integrally and take its boundary.  Therefore quotienting the
sum of the two cycle images kills all binary boundaries, and passage from
cycles to homology gives

`Z_2(Y;F_2)/(im(rho_+)+im(rho_-))`
` ~=H_2(Y;F_2)/(ker(beta_+)+ker(beta_-)).`             `(BTI15)`

Combining `(BTI7)--(BTI8)` with `(BTI15)` proves `(BTI4)`.  End proof.

## 5. Application to the Laurent sign sector

Use

`X=Y_(K_infinity)`,
`K_infinity=pi^(-1)(E(2))`,                            `(BTI16)`

and let `tau` be induced by `t=i_1(e_12(x_1^(-1)))`.  The quotient cover
`Y` corresponds to the index-two overgroup

`K_plus=<K_infinity,t>`.
                                                               `(BTI17)`

Equivalently, its image under `pi` is generated by `E(2)` and `h`; modulo
`E(2)`, the element `h` generates `C_2`.

Suppose the invariant and anti-invariant integral filling radii are bounded
but parity-compatible filling escapes.  The sparse compactness theorem
produces `epsilon in V` outside the left denominator of `(BTI4)`.  Hence:

**Corollary 2 (simultaneous Bockstein obstruction).**  There is a
finite-support class

`alpha=[epsilon] in H_2(Y;F_2)`                       `(BTI18)`

such that

`alpha notin ker(beta_+)+ker(beta_-)`.                `(BTI19)`

In particular

`beta_+(alpha)!=0`, `beta_-(alpha)!=0`.               `(BTI20)`

Both values are elements of order two by exactness of `(BTI3)`.

Thus the parity-only branch forces simultaneous ordinary and sign-twisted
two-primary homology in one fixed index-two intermediate cover.  This is
strictly more specific than the statement that a large finite discriminant
exists.

## 6. Exact remaining computation

The parity-only branch is eliminated by either of the following equivalent
statements:

1. `ker(beta_+)+ker(beta_-)=H_2(Y;F_2)`;
2. every finite-support `tau`-invariant binary two-cycle on `X` is a sum of
   reductions of an invariant and an anti-invariant integral two-cycle;
3. the cokernel in `(BTI4)` is zero.

If the quotient is nonzero, the remaining marked problem is to show that a
class `alpha` as in `(BTI18)--(BTI20)` has moving finite-cover
cancellations with unbounded radical-word incidence.  The local arithmetic
object to compute is now the pair `(beta_+,beta_-)`, not a growing family of
full discriminant lattices.
