# The live central obstruction is a marked Schur-multiplier class

Date: 2026-08-11

## 1. Outcome

**Closure update for the explicit symmetric double.** Although the marked
classes below may occupy growing Schur multipliers, their position relative
to the fixed relator classes has uniformly bounded coefficient distortion.
The reason is group-theoretic: the full finite residual \(R\) satisfies
\(R=[D,R]\). Thus this marked-Schur route cannot finish FALSE for the
current presentation. See `FALSE_FINITE_RESIDUAL_COMMUTATOR_NO_GO.md`.

After the real relation-filling closure in
`FALSE_REAL_RELATION_FILLING_NO_GO.md`, the quotient-dependent part of the
central search has a canonical finite home.

Let

`P=<s_1,...,s_d | r_1,...,r_ell>=F/N`,

let `w` represent an element of `Rad_sof(P)`, and let `F->Q` be a finite
quotient factoring through `P`, with kernel `L`.  Put

`C_Q=L/[F,L]`,
`K_Q=ker(Z^d=H_1(F;Z) -> H_1(Q;Z))`.                `(SMR1)`

Then there is a split, but generally noncanonical, exact sequence

`0 -> H_2(Q;Z) -> C_Q -> K_Q -> 0`.                  `(SMR2)`

The group `K_Q` is a rank-`d` free abelian lattice.  Thus all torsion in
`C_Q` is exactly the Schur multiplier `H_2(Q;Z)`.

Choose once and for all integers `c_1,...,c_ell` satisfying

`epsilon(w)=sum_j c_j epsilon(r_j) in Z^d`,           `(SMR3)`

where `epsilon` is exponent sum.  Such a choice exists because the sofic
abelianization of `P` kills `w`.  For every finite quotient `Q`, the residual
marked class

`kappa_Q=[w]-sum_j c_j[r_j] in C_Q`                  `(SMR4)`

lies in the embedded subgroup `H_2(Q;Z)`.  Under the Hopf formula it is the
class of the exponent-zero word

`w product_j r_j^(-c_j) in L intersect [F,F]`         `(SMR5)`

modulo `[F,L]`.

Consequently any successful finite central-relator sequence must make a
character detect `kappa_Q`.  The free lattice part alone is bounded by the
one fixed coefficient vector in `(SMR3)` and cannot produce the required
asymptotic amplification.

## 2. Exact sequence and splitting

The five-term exact sequence for

`1 -> L -> F -> Q -> 1`

and `H_2(F;Z)=0` give

`0 -> H_2(Q;Z) -> H_1(L;Z)_Q`
`  -> H_1(F;Z) -> H_1(Q;Z) -> 0`.                    `(SMR6)`

Here

`H_1(L;Z)_Q=L/[F,L]=C_Q`,                            `(SMR7)`

and the image in `H_1(F;Z)=Z^d` is precisely `K_Q`.  This proves exactness
of `(SMR2)`.  Every subgroup of a free abelian group is free abelian, so
`K_Q` is free.  Hence

`Ext_Z^1(K_Q,H_2(Q;Z))=0`,                            `(SMR8)`

which proves the noncanonical splitting.  Since `Q` is finite,
`H_1(Q;Z)` is finite and `K_Q` has rank `d`.

Reduction modulo any `m>=2` remains exact:

`0 -> H_2(Q;Z)/mH_2(Q;Z)`
`  -> C_Q/mC_Q -> K_Q/mK_Q -> 0`.                    `(SMR9)`

There is no left `Tor` term because `K_Q` is free.  Thus a canonical central
cover can be stored using a finite Schur-multiplier block and `d` lattice
coordinates; the full Schreier matrix is an intermediate representation,
not the intrinsic output.

## 3. The marked Hopf class

The word in `(SMR5)` belongs to `L` because `w` and every `r_j` vanish in
`Q`.  Its exponent sum is zero by `(SMR3)`, so it also belongs to `[F,F]`.
The Hopf formula gives

`H_2(Q;Z) ~= (L intersect [F,F])/[F,L]`.              `(SMR10)`

Its class under `(SMR10)` maps to `(SMR4)` in `C_Q`.  This proves that
`kappa_Q` is not an arbitrary torsion coordinate: it is an explicit marked
Schur-multiplier class functorially determined by the quotient labels and
the fixed exponent filling `c`.

Changing `c` changes `kappa_Q` by the Schur classes of fixed integer
relations among the exponent vectors of the presentation relators.  The
central separation problem is independent of that bookkeeping choice; one
choice should be fixed globally so that classes can be compared across a
quotient tower.

## 4. Quantitative necessity

Let `chi:C_Q->T` be any character.  From `(SMR4)`,

`chi(w)=chi(kappa_Q) product_j chi(r_j)^(c_j)`.        `(SMR11)`

For unit complex numbers, telescoping gives

`|chi(kappa_Q)-1|`
` >= |chi(w)-1|-sum_j |c_j| |chi(r_j)-1|`,            `(SMR12)`

and

`|chi(w)-1|`
` <= |chi(kappa_Q)-1|+sum_j |c_j| |chi(r_j)-1|`.      `(SMR13)`

Therefore, if all fixed relator phases tend to one while the marked phase
stays a positive distance from one, the same is true of `chi(kappa_Q)`.
This proves:

**Theorem (marked Schur necessity).**  Every central-relator certificate for
FALSE has a subsequence on which the associated characters detect the
marked Schur classes `kappa_Q` macroscopically.

In particular, a quotient family for which every `kappa_Q` vanishes is
sterile before any modular optimization.  This is the Schur-multiplier
version of the fixed-kernel filling no-go.

## 5. Proof-producing finite computation

For an explicit finite presentation and quotient label map, the useful
certificate is now:

1. a presentation or certified invariant-factor decomposition of
   `H_2(Q;Z)`;
2. the marked Hopf class `kappa_Q`;
3. a basis for the finite-index lattice `K_Q<=Z^d`;
4. the relator classes in one chosen splitting of `(SMR2)`; and
5. a character modulo a prime power with a certified marked/relator phase
   ratio.

The first screen is only whether `kappa_Q` is nonzero at the selected prime.
If it is zero, discard the quotient.  If it survives, solve the remaining
fixed-rank modular phase problem.  GAP/HAP or another exact finite-group
homology package can compute the Schur block; Hermite/Smith arithmetic handles
the rank-`d` lattice.  No dense unitary matrices and no rational filling LP
are part of this workload.

For the fold-aligned Baumslag--Solitar candidate, the concrete bridge is now
especially sharp: realize its growing primary transgression generator as the
marked Hopf class `(SMR5)` in a finite quotient of the full presented double.
Once this identification is made, only the phases of the fixed relator
classes in the same Schur/lattice coordinates remain to be controlled.
