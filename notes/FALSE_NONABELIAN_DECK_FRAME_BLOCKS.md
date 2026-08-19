# Nonabelian deck frames reduce to exact reduced-density blocks

Date: 2026-08-12

## 1. Outcome

The abelian deck-Fourier estimate in
`FALSE_DECK_FOURIER_BINARY_REDUCTION.md` extends exactly to every finite
deck subgroup.  The correct nonabelian object is not only the norm of an
isotypic projection: it is the largest eigenvalue of the multiplicity-side
reduced density matrix of the canonical real filling.

Let a finite group `A` of order `m` act unitarily on a finite-dimensional
complex Hilbert space `H`, let `q in H`, and define the orbit analysis map

`T_(A,q):H->ell^2(A)`,
`(T_(A,q)y)(a)=<a q,y>`.                              `(NDF1)`

Write the isotypic decomposition as

`H=directSum_(pi in A^) V_pi tensor M_pi`,            `(NDF2)`

where `d_pi=dim(V_pi)`, and write `q_pi` for the `pi`-component of `q`.
Define the positive operator on the multiplicity space

`rho_pi=Tr_(V_pi)(|q_pi><q_pi|) in B(M_pi)`.          `(NDF3)`

Then the orbit-frame norm is given by the exact formula

`||T_(A,q)||_op^2`
` =max_(pi in A^) (m/d_pi)||rho_pi||_op`.             `(NDF4)`

Consequently every nonabelian isotypic block gives the marked-ratio lower
bound

`Lambda_(w,X)^2`
` >=(m/d_pi)||rho_pi||_op`
` >=m ||q_pi||^2/(d_pi rank(rho_pi))`.                `(NDF5)`

Since `rank(rho_pi)<=d_pi`, a simpler but weaker form is

`Lambda_(w,X)>=sqrt(m)/d_pi ||q_pi||`.                `(NDF6)`

For a character, `d_pi=rank(rho_pi)=1`, and `(NDF5)` is precisely the
earlier abelian bound `sqrt(m)||P_pi q||`.

There is also a sharp converse interpretation.  If `Lambda_(w,X)<=C`, then
any family of irreducible blocks carrying squared filling mass at least
`eta` has effective Plancherel capacity at least

`sum_pi d_pi rank(rho_pi)>=m eta/C^2`.                `(NDF7)`

Thus bounded marked ratio forces the real filling to be spread across a
positive proportion of the available nonabelian matrix degrees, including
their multiplicity-side Schmidt ranks.  Concentration on `o(m)` effective
capacity proves FALSE.

This criterion is sharp.  In the regular representation, `q=delta_1` has
norm one and asymptotically all of its norm is noninvariant, but its orbit
is an orthonormal basis and `||T_(A,q)||=1`.  Therefore the tempting claim

`noninvariant filling norm bounded below => frame amplification`          `(NDF8)`

is false.  The invariant component amplifies coherently; a regular-like
noninvariant component can remain perfectly flat.

For a general deck tower, this produces an exact new alternative:
low-capacity concentration proves FALSE, while the escape is
Plancherel-flatness in the precise reduced-density sense above.  In the
constant-stabilizer Laurent tower the operator-level Kazhdan decoder now
proves that bounded intermediate real filling forces the flat branch; see
`FALSE_KAZHDAN_ORBIT_FRAME_OPERATOR_BOUND.md`.  Hence only the nonlinear
discriminant/carry analysis survives there.

## 2. Exact finite-group twirling formula

For a vector `v`, write `|v><v|` for the rank-one positive operator
characterized, independently of the inner-product convention, by

`<|v><v|y,y>=|<v,y>|^2`.                              `(NDF9)`

The frame operator of `(NDF1)` is

`S_(A,q)=T_(A,q)^*T_(A,q)`
`       =sum_(a in A)|a q><a q|`.                    `(NDF10)`

**Theorem 1 (nonabelian orbit-frame formula).**  Under `(NDF1)--(NDF3)`,

`S_(A,q)|_(V_pi tensor M_pi)`
` =(m/d_pi) I_(V_pi) tensor rho_pi`.                 `(NDF11)`

In particular `(NDF4)` holds.

**Proof.**  Expand the rank-one operator in `(NDF10)` using the isotypic
decomposition.  Averaging a cross term from
`V_pi tensor M_pi` to `V_sigma tensor M_sigma` gives an intertwiner from
`pi` to `sigma`.  Schur orthogonality makes it zero when `pi` and `sigma`
are inequivalent.

Fix one irreducible `pi`, choose an orthonormal basis `e_1,...,e_d` of
`V_pi`, and write

`q_pi=sum_(i=1)^d e_i tensor z_i`.                   `(NDF12)`

Then

`rho_pi=sum_(i=1)^d |z_i><z_i|`.                     `(NDF13)`

Matrix-coefficient orthogonality gives

`sum_(a in A) pi(a)|e_i><e_j|pi(a)^*`
` =(m/d) delta_(i,j) I_(V_pi)`.                      `(NDF14)`

Substituting `(NDF12)` into the `pi`-block of `(NDF10)` and applying
`(NDF14)` gives exactly `(NDF11)`.  Taking the largest eigenvalue of the
orthogonal block sum gives `(NDF4)`.  End proof.

The density matrix records both the size and the Schmidt spread of the
filling component:

`Tr(rho_pi)=||q_pi||^2`,
`rank(rho_pi)<=d_pi`.                                `(NDF15)`

Hence

`||rho_pi||_op>=||q_pi||^2/rank(rho_pi)`.            `(NDF16)`

Equations `(NDF4)` and `(NDF16)` prove `(NDF5)`, and the rank bound in
`(NDF15)` gives `(NDF6)`.

## 3. Application to a marked presentation cover

Let `X=D/K` be a finite regular presentation cover and let `A<=D/K` be a
finite deck subgroup.  Let `q=q_(w,1)` be the canonical minimum real filling
of the marked loop at the identity vertex.  Deck equivariance gives

`q_(w,a)=a q`, `a in A`.                             `(NDF17)`

The marked analysis operator on all vertices is

`T_X:W_X->C^X`,
`(T_Xy)_x=<q_(w,x),y>`.                              `(NDF18)`

Restricting the output coordinates in `(NDF18)` to the distinct vertices
indexed by `A` gives `(NDF1)`.  Therefore

`||T_X||_op>=||T_(A,q)||_op`.                        `(NDF19)`

The tangent bound from
`FALSE_STABILIZER_FRAME_AMPLIFICATION.md` says

`Lambda_(w,X)>=||T_X||_op`.                          `(NDF20)`

Combining `(NDF4)`, `(NDF19)`, and `(NDF20)` proves `(NDF5)` for every
irreducible representation of `A` occurring in the complexified two-chain
space.

The invariant block is the old stabilizer-frame theorem.  Indeed, for the
trivial representation,

`q_1=P_Aq`,
`rho_1=|P_Aq><P_Aq|`,                                `(NDF21)`

so `(NDF4)` gives

`||T_(A,q)||_op>=sqrt(m)||P_Aq||`.                   `(NDF22)`

When `A=H/K`, exact quotient scaling turns the right side into
`Fill_(R,2)(w;H)`.

## 4. Effective Plancherel-capacity criterion

Put

`r_pi=rank(rho_pi)`,
`cap_q(Omega)=sum_(pi in Omega)d_pi r_pi`.            `(NDF23)`

This capacity depends only on the Schmidt supports actually used by `q`.
It is bounded by ordinary Plancherel mass:

`cap_q(Omega)<=sum_(pi in Omega)d_pi^2<=m`.           `(NDF24)`

**Corollary 2 (nonabelian spectral delocalization).**  If

`Lambda_(w,X)<=C`,                                   `(NDF25)`

then for every set `Omega` of irreducibles,

`sum_(pi in Omega)||q_pi||^2`
` <=(C^2/m) cap_q(Omega)`.                           `(NDF26)`

Consequently, if the left side is at least `eta>0`, then `(NDF7)` holds.

**Proof.**  Equations `(NDF5)` and `(NDF25)` give

`||rho_pi||_op<=C^2 d_pi/m`.                         `(NDF27)`

Using `(NDF15)` and the definition of `r_pi`,

`||q_pi||^2=Tr(rho_pi)`
` <=r_pi||rho_pi||_op`
` <=(C^2/m)d_pi r_pi`.                               `(NDF28)`

Sum over `Omega`.  End proof.

The contrapositive is the useful FALSE certificate:

**Corollary 3 (low-capacity real concentration proves FALSE).**  Suppose
`X_n` are finite exact presentation covers for a fixed nontrivial
`w in Rad_sof(D)`, and there are finite deck subgroups `A_n` of orders
`m_n` and sets `Omega_n subset A_n^` such that

`sum_(pi in Omega_n)||q_(n,pi)||^2>=eta>0`,
`cap_(q_n)(Omega_n)=o(m_n)`.                          `(NDF29)`

Then

`Lambda_(w,X_n)->infinity`,                          `(NDF30)`

and a hyperlinear nonsofic group exists.

**Proof.**  If the marked ratios were bounded by `C` on a subsequence,
`(NDF26)` would make the first quantity in `(NDF29)` tend to zero.  Thus
`(NDF30)` holds.  Apply the marked discriminant divergence criterion.  End
proof.

For a single block, it is enough that

`||q_(n,pi_n)||>=eta`,
`d_(pi_n)r_(pi_n)=o(m_n)`.                            `(NDF31)`

This is stronger than asking for a one-dimensional character and applies
to perfect deck groups with no nontrivial characters.

## 5. The regular representation is the sharp escape

Take `H=ell^2(A)` with the left regular representation and `q=delta_1`.
Then

`T_(A,q)y=(<delta_a,y>)_(a in A)`                    `(NDF32)`

is a unitary coordinate transform, so

`||T_(A,q)||_op=1`.                                  `(NDF33)`

Under the Fourier decomposition of the regular representation, the
`pi`-component of `delta_1` is maximally entangled between the
representation and multiplicity copies.  In the normalization above,

`rho_pi=(d_pi/m)I_(d_pi)`.                           `(NDF34)`

Therefore every block in `(NDF4)` has value

`(m/d_pi)||rho_pi||_op=1`.                           `(NDF35)`

The invariant component has squared norm `1/m`, while the total
noninvariant squared norm is `1-1/m`.  Thus `(NDF33)` persists even though
the noninvariant norm tends to one.

This proves that `(NDF7)` is not merely a proof artifact.  The capacity
scale `m` is necessary: a vector distributed with Plancherel weights and
maximal Schmidt rank can have a completely bounded orbit frame.

## 6. The sharpened stabilizer-tower alternative

Use the tower from `FALSE_STABILIZER_FRAME_AMPLIFICATION.md`:

`K_n=pi^(-1)(L_n)`, `H_n=pi^(-1)(J L_n)`,
`A_n=H_n/K_n`, `m_n=|A_n|`.                          `(NDF36)`

Let `q_n` be the minimum real filling in the `K_n`-cover and let
`r_n=P_(A_n)q_n`.  Exact quotient scaling gives

`||r_n||=m_n^(-1/2)Fill_(R,2)(w;H_n)`.               `(NDF37)`

If the intermediate real fills are unbounded, the invariant block already
proves FALSE.  Suppose instead that they remain bounded.  Then

`||r_n||=O(m_n^(-1/2))`.                             `(NDF38)`

The boundary operators in covers of one fixed finite presentation have a
uniform operator-norm bound `M`.  Along a locally separating tower the
fixed lifted word chain is eventually nonzero with norm bounded below by
some `beta>0`.  Since

`partial_2 q_n=b_(w,1)`,                              `(NDF39)`

one has

`||q_n||>=beta/M`.                                   `(NDF40)`

Thus `(NDF38)` leaves a fixed positive amount of nontrivial isotypic mass.
In a general tower, Corollary 2 gives the exact dichotomy between
low-capacity concentration, which proves FALSE, and linear-capacity
Plancherel spreading.

For this explicit Kazhdan tower the second alternative is now known to be
forced.  The operator-level refinement in
`FALSE_KAZHDAN_ORBIT_FRAME_OPERATOR_BOUND.md` constructs a simultaneous
equivariant decoder for the entire noninvariant word orbit and proves

`||T_(A_n,q_n)||_op`
` <=max{Fill_(R,2)(w;H_n),C_J}`.                     `(NDF41)`

Thus bounded intermediate real fills imply `(NDF27)` uniformly for every
nontrivial block; low-capacity real concentration cannot occur here.  This
sharpens the general dichotomy rather than contradicting it.

If the second branch holds and the intermediate real fills stay bounded,
the known integral filling escape still forces the canonical discriminant
radii to diverge.  The remaining obstruction is then genuinely nonlinear:
one must prove marked nonisotropy/incidence for those low-carry classes.
The two theorems together separate the arithmetic branch from all
nonabelian real-frame concentration, rather than conflating both under the
phrase "noninvariant filling."
