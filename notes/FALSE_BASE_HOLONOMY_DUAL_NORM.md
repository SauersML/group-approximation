# Fixed-rank dual norm for amplified transfer holonomy

Date: 2026-08-11

## 1. Purpose

The amplified transfer-holonomy certificate in
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md` asks for modularly transferable
base cycles `v` for which

`H_q(Hol_(w,X,q)(Jv))/||v||`                                      `(BHD1)`

is large.  At first sight this is an optimization over all integral base
cycles and all moduli.  When the full base cycle lattice transfers at a
given stage, the optimization has fixed rank.  In fact it is exactly a
finite shortest-representative problem, and it is uniformly equivalent to
the Euclidean norm of the centered holonomies of one fixed integral basis.

Consequently, on full-transfer stages the FALSE search needs only finitely
many modular right-hand sides, independent of the cover degree.  Divergence
of their centered holonomy vector already proves that a hyperlinear
nonsofic group exists.

## 2. Setup

Retain the notation of `FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md`.  Thus

`K_1=ker(A_1^*) <= C^2(P,Z)`                                      `(BHD2)`

is the base cycle lattice, `J:K_1->K_X` is constant lift, and

`Hol=Hol_(w,X,q):J(K_1) intersect im(A_X mod q)->Z/qZ`              `(BHD3)`

is the radical transgression.  Assume at the stage `(X,q)` that the full
base lattice transfers:

`J(K_1) <= im(A_X mod q)`.                                        `(BHD4)`

Put `k=rank(K_1)` and choose once and for all an integral basis

`v_1,...,v_k` of `K_1`.                                           `(BHD5)`

Every `v_i` is primitive in `K_1`.  Let

`B:R^k->K_1 tensor R`,  `B e_i=v_i`,                              `(BHD6)`

where both spaces carry their ambient Euclidean norms.  Write

`s_B=sigma_min(B)>0`,  `M_B=max_i ||v_i||`.                        `(BHD7)`

For each basis vector choose the centered integer representative

`c_i in [-q/2,q/2] intersect Z`

of `Hol(Jv_i)`, with either endpoint convention when `q` is even, and put
`c=(c_1,...,c_k) in Z^k`.

Define the optimal amplified base-holonomy slope

`Omega_(X,q)=sup_(0!=v in K_1) H_q(Hol(Jv))/||v||`.                `(BHD8)`

The terms with zero holonomy contribute zero.

## 3. Exact finite formula

For `nbar in (Z/qZ)^k`, define the shortest representative length

`lambda_(B,q)(nbar)=min{||Bm||:m in Z^k, m=nbar mod q}`.            `(BHD9)`

For `nbar!=0`, this is positive.  If `nbar=0`, its only possible holonomy
is zero and it can be omitted.

**Theorem 1 (exact fixed-rank formula).**  Under `(BHD4)`,

`Omega_(X,q)`
` =max_(nbar in (Z/qZ)^k, H_q(c dot nbar)!=0)`
`      H_q(c dot nbar)/lambda_(B,q)(nbar)`.                        `(BHD10)`

Here `c dot nbar` is evaluated modulo `q`.  In particular, the right-hand
side is a finite optimization in the fixed rank `k`, regardless of the
cover degree.  The maximum over an empty set is understood to be zero.

**Proof.**  Every `v in K_1` has a unique expression `v=Bn` with
`n in Z^k`.  Since `Hol` is a homomorphism and the `c_i` represent its
values on the basis,

`Hol(JBn)=c dot n mod q`.                                         `(BHD11)`

The numerator therefore depends only on `n mod q`.  Within one residue
class the numerator is fixed, so the ratio is maximized by an integral
representative having the least value of `||Bn||`.  Such a representative
exists because `B(Z^k)` is a lattice and Euclidean balls meet it in finite
sets.  Taking the maximum over the finitely many residue classes proves
`(BHD10)`.  End proof.

The exact formula is a fixed-dimensional closest-vector problem.  The next
estimate removes even that optimization when only divergence matters.

## 4. Basis-holonomy norm equivalence

**Theorem 2 (dual-norm comparison).**  Under `(BHD4)`,

`||c||_2/(sqrt(k) M_B) <= Omega_(X,q) <= ||c||_2/s_B`.             `(BHD12)`

Both comparison constants depend only on the once-chosen base lattice
basis, not on `X` or `q`.

**Proof.**  For the upper bound, write `v=Bn`.  The integer `c dot n` is a
representative of `Hol(Jv)`, so

`H_q(Hol(Jv)) <= |c dot n|`
`                 <= ||c||_2 ||n||_2`
`                 <= (||c||_2/s_B)||Bn||`.                        `(BHD13)`

Take the supremum over nonzero `v`.

For the lower bound, choose `i` with

`|c_i|=||c||_infinity >= ||c||_2/sqrt(k)`.                         `(BHD14)`

Because `c_i` is centered,

`H_q(Hol(Jv_i))=|c_i|`.                                           `(BHD15)`

The term `v_i` in `(BHD8)` gives

`Omega_(X,q)>=|c_i|/||v_i||`
`             >=||c||_2/(sqrt(k)M_B)`.                            `(BHD16)`

End proof.

Thus the apparently nonlinear integral search over base cycles is, on a
full-transfer stage, just the norm of a fixed-rank modular character.  The
shortest-vector geometry in `(BHD10)` affects the optimal constant but not
whether the constant diverges.

## 5. Complete amplified FALSE corollary

**Corollary 3 (basis-holonomy divergence proves FALSE).**  Suppose there
are regular covers `X_j` and moduli `q_j>1` satisfying

`J(K_1) <= im(A_(X_j) mod q_j)`                                    `(BHD17)`

for every `j`.  Let `c_j in Z^k` be the centered basis-holonomy vector at
stage `j`.  If

`||c_j||_2 ->infinity`,                                            `(BHD18)`

then a hyperlinear nonsofic group exists.

Equivalently, along full-transfer stages the amplified obstruction exists
if and only if

`Omega_(X_j,q_j)->infinity`                                       `(BHD19)`

after passage to a subsequence.

**Proof.**  By finite-dimensional pigeonhole, after passing to a
subsequence there is a fixed index `i` such that `|c_(j,i)|->infinity`.
The primitive base vector `v_i` is fixed, and

`H_(q_j)(Hol_(w,X_j,q_j)(Jv_i))/||v_i||`
` =|c_(j,i)|/||v_i|| ->infinity`.                                 `(BHD20)`

The amplified transfer-holonomy certificate, Theorem 3a of
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md`, now constructs a hyperlinear
image retaining `w in Rad_sof(H)`, so that image is not sofic.  Conversely,
`(BHD12)` shows that divergence of `Omega` forces divergence of `||c_j||`;
the lower bound shows the reverse implication.  End proof.

Notice that `(BHD18)` automatically forces `q_j->infinity`, since every
coordinate of `c_j` has absolute value at most `q_j/2`.

## 6. Computational form

Choose the basis matrix `V=[v_1 ... v_k]` once.  At a candidate stage form
the block modular system

`A_X [a_1 ... a_k]=J V mod q`.                                    `(BHD21)`

Full transfer is exactly solvability of this one block system.  Evaluate
each solution on one lifted word chain:

`h_i=<a_i,b_(w,x)> mod q`,                                        `(BHD22)`

and center the `h_i` to obtain `c`.  No basis of `K_X`, Smith form of the
full cover discriminant, or search over `v in K_1` is needed.  The exact
optimal slope can be recovered from `(BHD10)` if desired; for the FALSE
criterion it is enough to watch `||c||_2`.

This turns the live full-transfer search into two exact tests:

1. solve `k` modular right-hand sides, where `k=rank(K_1)` is fixed;
2. determine whether the centered output vector is unbounded.

## 7. Scope

The hypothesis `(BHD4)` is substantial.  It is not asserted that arbitrary
regular covers or the current projective charts satisfy full base transfer.
If only a fixed primitive sublattice `L<=K_1` transfers, the same proof
applies to a fixed integral basis of `L`; a divergent centered coordinate
again supplies the primitive vector required by Theorem 3a.  If the
transfer sublattice itself changes with the stage and contains no fixed
primitive direction, the finite-basis pigeonhole step need not apply.

Accordingly this note does not prove FALSE.  It proves that, wherever full
base transfer occurs, variable-cycle optimization hides no additional
asymptotic difficulty: the entire amplified obstruction is visible in a
fixed finite vector of modular holonomies.
