# Return sections give the full cycle-core MF reflection in low rank

2026-09-13. Written proof, not Lean-verified.

Let `X` be a nonempty finite-alphabet subshift over coefficient field
`F_2`, write `R=LC(X,F_2) semidirect_T Z`, let `Y` be its cycle core,
and put `U=X\Y`, `I=LC_c(U,F_2) semidirect_T Z`. The
[cycle-core theorem](pestov91-cycle-core-exact-mf-reflection-2026-09-13.md)
identifies the full MF radical with the restriction kernel in rank
at least four and proves that `I` is locally matricial.

## Theorem

Suppose `k>=1` and `T^j` has no fixed points for `1<=j<k`. For every
`n>=1` with `nk>=4`,

`Rad_MF(GL_n(R))=ker(GL_n(R) -> GL_n(R_Y))`.            (1)

This kernel is locally finite, and the maximal MF quotient is the
LEF image of restriction. For `n>=2`, also

`Rad_MF(EL_n(R))=ker(EL_n(R) -> EL_n(R_Y))`,            (2)

with quotient exactly `EL_n(R_Y)`, which is LEF.

Thus the full cycle-core reflection holds in elementary rank two when
there are no fixed points, and in the unit group when there are no
points of periods one, two or three. Every aperiodic subshift satisfies
both conclusions. These are exact radical formulas, strengthening the
earlier low-rank criterion that only supplied a nonzero invisible element.

The section statements in sections 1--2 also hold for any full clopen
return section with bounded positive return times: replace `2k-1` by
their maximum `H`, and `4k-2` by `2H`, in those arguments. The lower
bound `k` is needed for the matrix embedding in section 3.

## 1. Full return sections preserve the core

Take the clopen section `C` from the
[return-tower construction](pestov91-return-towers-lower-mf-rank-2026-09-13.md),
with return times in `[k,2k-1]`, and let `S` be its first-return map.
The corner `P=pRp`, `p=1_C`, is the crossed product of the finite-alphabet
return subshift. Let `Y_C` be the cycle core of this return system.
Then, as subsets of `C`,

`Y_C=C intersection Y`.                              (3)

First, finite matrix rings and unital corners preserve ring-LEF.
For a corner, include its idempotent and all needed multiplication
relations in a finite ring table. The finite model sends that idempotent
to an idempotent, and restricting to its finite corner gives the desired
table model with the correct local identity. Matrices are handled by
including their finitely many entries and multiplication relations.

The return ring on `C intersection Y` is a corner of the LEF ring
`R_Y`, so it is LEF. The cycle criterion and maximality of `Y_C`
give `C intersection Y subset Y_C`.

Conversely, saturate `Y_C` through the finitely many return towers.
Writing `C_h` for the first-return-time cells, set

`W=union_h union_(0<=i<h) T^i(Y_C intersection C_h)`.

This is a closed invariant subshift of `X`. Its return section is
exactly `Y_C`. The full tower map identifies `R_W` with a unital
corner of `M_(2k-1)(R_(Y_C))`. Since the latter coefficient ring is
LEF, so is `R_W`. Maximality of `Y` therefore implies `W subset Y`,
and in particular `Y_C subset C intersection Y`, proving (3).

It follows that

`J=pIp=ker(P -> R_(Y_C))`.                            (4)

We use the original return coding and original tower lengths when
restricting systems; no new coding or rank is introduced for the core.

## 2. A full section normally generates the transient kernel

For any `n>=1`, define `K_n(I)` to be the invertible matrices `1+A`
over `R` whose deviations `A` and inverse deviations have entries in
`I`. Define `K_n(J)` similarly in `GL_n(P)`, with identity `p I_n`.
Embed the latter into `GL_n(R)` by adding `(1-p)I_n`. Then

`normalClosure_(K_n(I))(K_n(J))=K_n(I)`.              (5)

This is an algebraic statement about the transient ideal; it uses no
MF hypothesis. Its proof also shows that `K_n(I)` is locally finite
for every `n>=1`, including units.

Start with an element of `K_n(I)` and the entries of its deviation
and inverse deviation. As in the local matrix-algebra lemma, express
these entries using finitely many compact clopen partial shifts, and
let `K subset U` contain all their sources and ranges.

For each point of `K`, add partial shift arrows to its first strictly
future return to `C` and its next return to `C`. Both displacements
are bounded by `4k-2` in total, and the appropriate domains are clopen.
Only finitely many partial shifts are added. Their targets, together
with `K`, form a compact clopen set `K' subset U`. Every generated
equivalence class contains a point of `K` and at least two distinct
points of `C`; these two points are distinct because `U` has no periodic
points. All newly added points are connected to their point of `K`.

A finite wandering clopen cover of `K'` bounds every orbit's visits
to `K'`. The earlier local matrix lemma therefore gives a finite
product of matrix algebras

`B=product_alpha M_(h_alpha)(F_2) subset I`

containing the prescribed entries and the added arrows. Use its explicit
finite-equivalence-relation construction, refining the clopen partition
also by `C`. The projection `q=1_(K' intersection C)` then belongs to
`B`, satisfies `q<=p`, and has rank `r_alpha>=2` in every matrix factor.
In particular `qBq subset J`.

The element under consideration lies in the unitized finite group
`GL_n(B)=product_alpha GL_(n h_alpha)(F_2)`. In each factor, the subgroup
coming from `GL_n(qBq)` contains a transvection supported in its at least
two section coordinates, and it contains such a transvection independently
in each factor. Conjugating by finite permutation matrices gives all
elementary transvections of that factor. These generate its whole general
linear group over `F_2`. Hence the normal closure of the unitized
`GL_n(qBq)` inside the unitized `GL_n(B)` is all of `GL_n(B)`.
Since the former subgroup lies in the embedded `K_n(J)`, this proves (5).

The same local matrix argument, without the additional section arrows,
places any finite collection of kernel elements in one finite group.
Thus `K_n(I)` is locally finite also when `n=1`. For `n>=2` it lies in
`EL_n(R)`, by the characteristic-two elementary flattening argument
already proved in the cycle-core theorem. All conjugations in (5)
therefore take place inside the elementary group in those ranks.

## 3. Import the entire high-rank kernel through the tower

The first `k` tower levels give the previously established injection

`Phi:M_k(P) -> R`,
`Phi(A)=sum_(i,j<k) a_i A_ij b_j`,

where `a_0=b_0=p`, `b_i a_j=delta_ij p` for `i,j<k`, and the identity
of the image is `e=sum_(i<k) a_i b_i`. Applying this entrywise and
adding `(1-e)I_n` gives an embedding

`EL_(nk)(P) -> GL_n(R)`.

For `n>=2` its image lies in `EL_n(R)` by elementary flattening.
Since `nk>=4`, the exact high-rank theorem applied to the return
subshift identifies its invisible kernel with

`K_(nk)(J)=ker(GL_(nk)(P) -> GL_(nk)(R_(Y_C)))`.

This kernel lies in `EL_(nk)(P)`. Every MF-target map out of the
ambient low-rank group therefore kills its embedded image.

That image contains all of `K_n(J)` in its phase-zero placement.
Indeed, given `g in K_n(J)`, place its `n` rows and columns in the
phase-zero position of each outer block and put identity entries in
all other phases. This matrix is in `K_(nk)(J)`. Under the tower map
it becomes exactly `(1-p)I_n+g`. This includes `n=1`; it does not
require that a unit over `P` already be an elementary matrix in rank one.

Every MF-target map thus kills the embedded `K_n(J)`, and normality
together with (5) makes it kill all of `K_n(I)`. Restriction to the
core has LEF image, giving the reverse radical inclusion in (1).
For `n>=2` the same proof takes place inside `EL_n(R)`, and coefficient
lifting makes its core restriction onto `EL_n(R_Y)`. This proves (2).

## Scope

The argument computes complete kernels without assuming they are simple
or a finite product of simple groups. The analytic input remains the
printed rank-four torsion-defect theorem, through the exact cycle-core
result. The absence of short periods supplies the full return section;
the periodic rank-two and rank-three cases remain open. The coefficient
field here is `F_2`. No Lean verification or global priority is claimed.

## Dependency validation

Cairn 2.13.1 checked all four new nodes on MSI against snapshot
`658e7272a164008e654ffc9b3887c21257c9f8e1` in 37.060 seconds.
Both `check --changed` and `preview` returned zero, both new claims
were `ESTABLISHED`, and neither graph had errors. The graph contained
10,423 claims and 10,682 routes. The
[receipt](pestov91-lowcore-cairn-receipt-2026-09-13.json) records the
source delta and runner hashes. This paragraph and that receipt were
added after the run. These are dependency checks for a written proof;
no finite test or Lean verification is claimed to establish the general
normal-generation and MF assertions.
