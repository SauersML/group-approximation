# Regular-MF Bass--Serre closure theorems

This note records two closure operations which preserve not only an
operator-norm MF embedding of a group but also a trace realizing the
canonical regular character.  That extra trace is what certifies the
abstract Bass--Serre normal form inside the MF completion.

## 1. Regular MF realizations

Call a countable group `H` **regularly MF-realized** if there are

* a separable unital MF C-star-algebra `A`,
* an injective homomorphism `i:H->U(A)`, and
* a tracial state `tau` on `A`

such that

`tau(i(h))=delta_(h,1)`, `h in H`.                         `(RMF1)`

This is stronger than merely being weak/operator-norm MF.  It does not say
that the trace is Connes embeddable and does not imply that `H` is
hyperlinear.

Every countable residually finite group satisfies `(RMF1)`: take nested
finite quotients separating its elements, use their left regular
representations in a norm matrix corona, and take an ultralimit of the
normalized traces.

## 2. Symmetric doubles

The regular-double theorem proved in `notes/FALSE_FINITE_KERNEL_AUDIT.md`
says:

**Theorem (regular symmetric double).**  If `H` is regularly MF-realized
and `C<=H`, then

`H *_C H`                                                  `(RMF2)`

is regularly MF-realized.

Shulman's symmetric-amalgam theorem makes
`A *_(C^*(C)) A` MF.  The reduced tracial amalgam of the two GNS closures
has zero trace on every nontrivial Bass--Serre reduced word, which both
certifies injectivity of `(RMF2)` and supplies its regular character.

## 3. Central HNN extensions

There is an analogous closure theorem which was not needed in the finite-
kernel audit.

**Theorem (regular central HNN closure).**  Let `H` be regularly
MF-realized and let `C<=H`.  Then

`Gamma=<H,t | t^(-1)c t=c for every c in C>`              `(RMF3)`

is regularly MF-realized.

**Proof.**  Fix `(A,i,tau)` as in `(RMF1)` and put

`B=C^*(i(C))<=A`.                                         `(RMF4)`

Shulman's central-HNN theorem makes the full C-star HNN extension

`E=<A,t | t^(-1)b t=b for every b in B>`                  `(RMF5)`

an MF algebra.

Let `(pi_tau,H_tau)` be the GNS representation of `tau`, and write

`M=pi_tau(A)'',  N=pi_tau(B)''`.                          `(RMF6)`

The state `tau` extends normally to `M`.  There is a trace-preserving
conditional expectation `E_N:M->N`.  For `h in H\C`, regularity gives

`E_N(pi_tau(i(h)))=0`.                                    `(RMF7)`

Indeed the conditional expectation is the orthogonal projection
`L^2(M,tau)->L^2(N,tau)`, and for every `c in C`,

`<i(h),i(c)>_(L^2)=tau(i(c^(-1)h))=0`.                    `(RMF8)`

Form the reduced von Neumann HNN extension

`P=HNN(M,N,id)`                                           `(RMF9)`

with its canonical trace `Tau` and stable unitary `v`.  The pair
`pi_tau:A->M<=P`, `t|->v` satisfies the relations in `(RMF5)`, so the
universal property gives a star-homomorphism

`Theta:E->P`.                                             `(RMF10)`

Now map `(RMF3)` into `U(E)` by its canonical generators and compose with
`Theta`.  A nonidentity word lying in `H` has trace zero by `(RMF1)`.  If a
word contains stable letters, put it in Britton-reduced form.  At every
pinch where consecutive stable-letter exponents have opposite signs, the
intervening group coefficient lies outside `C`; `(RMF7)` says that its
conditional expectation onto `N` is zero.  The reduced-HNN moment formula
therefore gives

`Tau(Theta(w))=0`                                         `(RMF11)`

for every nontrivial Britton-reduced group word `w`.  In particular
`Theta(w)!=1`, so the group map `Gamma->U(E)` is injective.  Finally
`Tau compose Theta` is a tracial state on `E` satisfying the regular law on
`Gamma`.  Since `E` is MF, this is a regular MF realization of `(RMF3)`.
End proof.

## 4. Finite iteration

Theorems `(RMF2)` and `(RMF3)` may be iterated.  Starting with countable
residually finite vertex groups, any finite construction obtained by

1. taking a symmetric double over an arbitrary subgroup, or
2. adjoining a stable letter which centralizes an arbitrary subgroup

at each step is regularly MF-realized.  No separability of the amalgamated
subgroup in the group-theoretic sense is required.

The trace assertion is load-bearing.  Shulman's C-star permanence alone
does not automatically imply that the canonical group map into the full
amalgam or HNN algebra is injective; the reduced tracial model supplies that
normal-form detector.

## 5. Exact limitation for the FALSE lane

The cyclic shear uses a nontrivial edge automorphism

`alpha(r)=rz`, `alpha(z)=z`,                               `(RMF12)`

not the identity edge map in `(RMF3)`.  Consequently the theorem above does
not prove weak MF of the shear.  Extending `(RMF3)` to `(RMF12)` would still
require the nonzero operator-norm projective sector isolated in
`notes/FALSE_FINITE_KERNEL_AUDIT.md`.  Thus regular central-HNN closure
enlarges the safe construction toolkit without crossing the currently open
finite-kernel gate.

Source for MF permanence in `(RMF5)`: Tatiana Shulman, *The MF property for
amalgamated free products*, the central-HNN extension theorem (Theorem 29 in
the cited manuscript version).  The trace calculation uses the standard
reduced von Neumann HNN construction and its reduced-word moment formula.
