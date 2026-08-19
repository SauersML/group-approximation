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

## 7. Cyclotomic generalization at every prime

The preceding argument is not special to signs.  Let `p` be prime, let
`X->Y` be a free cellular `C_p`-cover with generator `tau`, put

`O_p=Z[zeta_p]`, `varpi=1-zeta_p`,                    `(BTI21)`

and let `O_chi` be the rank-`p-1` integral local system on which `tau` acts
by multiplication by `zeta_p`.  The standard integral pullback square is

`Z[C_p] ~= Z times_(F_p) O_p`,                        `(BTI22)`

where the two maps to `F_p` are reduction modulo `p` and modulo `varpi`.
Explicitly, evaluation at `1` and `zeta_p` identifies `Z[C_p]` with

`{(a,b) in Z directSum O_p : a=b in F_p}`.             `(BTI23)`

**Proof of `(BTI22)`.**  The two evaluation kernels are generated by
`tau-1` and by `1+tau+...+tau^(p-1)`.  Their resultant is
`Phi_p(1)=p`, so the cokernel of the joint evaluation map is `F_p`, with
the displayed residue maps.  Equivalently, `(BTI22)` is the usual Milnor
square for the two factors of `tau^p-1`.  End proof.

Apply `(BTI22)` coordinatewise to the cellular chains of the cover.  A
regular integral chain is exactly a pair consisting of an ordinary
integral chain and a cyclotomic chain whose residues agree in
`C_*(Y;F_p)`.  Define

`beta_1:H_2(Y;F_p)->H_1(Y;Z)`,
`beta_chi:H_2(Y;F_p)->H_1(Y;O_chi)`                   `(BTI24)`

from

`0->Z --p--> Z ->F_p->0`,
`0->O_chi --varpi--> O_chi ->F_p->0`.                 `(BTI25)`

The cycle-level proof of Lemma 1 applies verbatim to both sequences.
Therefore:

**Theorem 3 (cyclotomic gluing quotient).**  The obstruction to gluing an
ordinary integral two-cycle and a cyclotomic integral two-cycle along their
common residue is

`H_2(Y;F_p)/(ker(beta_1)+ker(beta_chi)).`              `(BTI26)`

In particular, the integral `C_p`-chain gluing is surjective on cycles if
either

`H_1(Y;Z)[p]=0`                                       `(BTI27)`

or

`H_1(Y;O_chi)[varpi]=0`.                              `(BTI28)`

**Proof.**  Formula `(BTI22)` gives the chain-level fiber product.  The
images of ordinary and cyclotomic cycle reduction are the preimages of
`ker(beta_1)` and `ker(beta_chi)` in `Z_2(Y;F_p)`.  Boundaries lift in both
coefficient systems.  Quotienting their sum therefore gives `(BTI26)` just
as in `(BTI15)`.  The image of either connecting map lies in the torsion
group displayed in `(BTI27)` or `(BTI28)`; if one target is zero, its kernel
is all of `H_2(Y;F_p)`.  End proof.

For `p=2`, one has `O_2=Z`, `zeta_2=-1`, and `varpi=2`; Theorem 3 is exactly
`(BTI4)`.  For the Laurent tower, Theorem 3 combines with the cyclotomic
augmentation theorem in
`FALSE_DECK_FOURIER_BINARY_REDUCTION.md`: the deck orbit of the radical
class supplies the full augmentation representation, while any residual
integral gluing obstruction must be detected simultaneously by the two
Bocksteins in `(BTI24)`.

This produces a prime-varying alternative to the binary computation.  At
each fixed prime satisfying either primary-torsion vanishing condition
`(BTI27)--(BTI28)`, the purely cyclotomic gluing obstruction is zero.  To
deduce a prime-uniform quantitative bound while `p->infinity` one would
still need norm control for the corresponding cycle lifts.  Thus torsion
vanishing is an exact algebraic elimination of the branch, not by itself a
uniform decoder estimate.  Once such norm control is available, any
remaining escape lies in an individual rational Fourier sector, where the
deck Fourier-frame theorem applies.

## 8. The radical augmentation module is torsion-free cyclotomically

The cyclotomic orbit theorem identifies the known radical submodule before
any Bockstein computation.  Put

`R_p=Z[C_p]=Z[t]/(t^p-1)`,
`I_p=Aug_Z(C_p)=(t-1)R_p`.                             `(BTI29)`

The deck orbit of `[w]` is a copy of `I_p`.  Its ordinary and cyclotomic
coinvariants have opposite arithmetic behavior.

**Proposition 4 (augmentation coefficient contrast).**

`(I_p)_(C_p)=I_p/(t-1)I_p ~= Z/pZ`,                   `(BTI30)`

whereas for the nontrivial cyclotomic character,

`(I_p tensor_Z O_chi)_(C_p) ~= O_p`                   `(BTI31)`

as an abelian group.  In particular `(BTI31)` has no `varpi`-torsion.  Under
the natural map induced by `I_p<=R_p` into the twisted regular orbit, its
image is the principal ideal

`(zeta_p-1)O_p=varpi O_p`.                             `(BTI32)`

**Proof.**  Multiplication by `t-1` gives an `R_p`-module isomorphism

`R_p/(1+t+...+t^(p-1)) ~= I_p`.                       `(BTI33)`

Taking ordinary coinvariants sets `t=1`; the remaining relation in
`(BTI33)` becomes `p=0`, proving `(BTI30)`.

For diagonal twisted coinvariants, tensoring over `R_p` evaluates `t` at
`zeta_p^(-1)` (the inverse depends only on the left/right convention).  The
norm polynomial in `(BTI33)` vanishes at that value, so

`I_p tensor_(R_p) O_(chi^(-1)) ~= O_p`,               `(BTI34)`

which is `(BTI31)`.  The inclusion `I_p<=R_p` sends its generator `t-1`
to `zeta_p^(-1)-1`, a unit multiple of `varpi`, proving `(BTI32)`.  End
proof.

At `p=2`, Proposition 4 says that the anti-invariant radical line becomes
ordinary `C_2` torsion after adjoining the involution, while in sign
coefficients it remains an infinite cyclic line.  More generally, the
known radical augmentation module has an ordinary `p`-torsion coinvariant
but no cyclotomic `varpi`-torsion at the isolated module level.

This does not prove that the ordinary coinvariant injects into the full
`H_1(Y;Z)`, nor that `H_1(Y;O_chi)[varpi]` vanishes.  Additional
relation-module summands and the five-term transgression still have to be
audited.  It does prove that the explicit radical orbit, considered by
itself, has no cyclotomic primary torsion; a simultaneous obstruction in
`(BTI26)` needs additional homological input.
