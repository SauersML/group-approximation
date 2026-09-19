# FALSE lane: regular MF doubles and the finite-kernel gate

Date: 2026-08-10

This note records an orientation correction and the exact surviving
operator-norm problem for the cyclic radical shear.  It deliberately makes
no claim that the main problem has been solved.

## 1. Regularly MF-realized groups

Call a group `H` **regularly MF-realized** if there are

- a separable MF C-star algebra `A`,
- an injective homomorphism `i:H -> U(A)`, and
- a tracial state `tau` on `A`

such that

`tau(i(h))=0` for every `h!=1`.                         `(RMD1)`

Equivalently, the cyclic representation of `H` obtained from the GNS vector
of `tau` is the left regular representation.

**Lemma (profinite regular MF realization).**  Every countable residually
finite group is regularly MF-realized.

**Proof.**  Choose a decreasing sequence of finite-index normal subgroups
`N_n` with trivial intersection, put `Q_n=H/N_n`, and let `lambda_n` be the
left regular representation of `Q_n`.  Then

`h |-> [(lambda_n(hN_n))_n]`                            `(RMD1a)`

is injective in the norm matrix corona: if `h!=1`, then `hN_n!=1` eventually,
and a nontrivial permutation unitary has operator-norm distance at least
`sqrt(3)` from the identity.  Let `A` be the separable C-star algebra generated
by this group copy.  It is MF because it is a C-star subalgebra of the norm
matrix corona.  Any ultralimit of the normalized matrix traces restricts to

`tau(h)=0` for every `h!=1`,                            `(RMD1b)`

since the trace of the regular permutation of `hN_n` is zero eventually.
Thus `(A,tau)` is the required regular MF realization.  End proof.

**Proposition (regular MF symmetric doubles).**  If `H` is regularly
MF-realized and `C<=H`, then

`H *_C H`                                               `(RMD2)`

is regularly MF-realized.

**Proof.**  Put `B=C^*(i(C))<=A`.  Shulman's symmetric-amalgam theorem says
that the full amalgamated free product

`D=A *_B A`                                             `(RMD3)`

is MF.  It remains to check that the canonical group homomorphism from
`H *_C H` to `U(D)` is injective and has a regular trace.

Let `pi_tau` be the GNS representation, put `M=pi_tau(A)''` and
`N=pi_tau(B)''`, and let `E_N:M->N` be the trace-preserving conditional
expectation.  For `h notin C`, equation `(RMD1)` gives

`E_N(pi_tau(i(h)))=0`:                                 `(RMD4)`

indeed the unitary is orthogonal in `L^2(M,tau)` to every group unitary from
`C`, hence to `L^2(N)`.

Map the two copies of `A` in `(RMD3)` to the reduced von Neumann amalgam

`(M,E_N) *_N (M,E_N)`.                                 `(RMD5)`

For every nontrivial reduced group word in `H *_C H`, its syllables outside
`C` are centered by `(RMD4)`, so the reduced-amalgam trace of that word is
zero.  Therefore the induced trace on the group copy is its regular trace.
In particular no nontrivial reduced group word maps to `1`, proving
injectivity.  Pulling the trace in `(RMD5)` back to `(RMD3)` proves `(RMD1)`
for the double.  End proof.

This proposition can be iterated.  Start with the residually finite
Kun--Thom vertex group `G` and its subgroup `Gamma`.  The profinite lemma and
one application of the proposition show that the banked symmetric double

`D=G *_Gamma G`

is regularly MF-realized.  A second application, now to `D` and the primitive
radical shear word `r`, shows that the untwisted quotient

`K=D *_(C_D(r)) D`                                     `(RMD6)`

has a regular MF realization.  This explicit two-step dependency is the
profinite-trace repair: the claim does not follow from an arbitrary weak-MF
embedding of `G`, because such an embedding may fold the amalgamated subgroup.

## 2. The finite-extension orientation correction

For the cyclic shear group `J`, the quotient calculation is

`1 -> <z> ~= C_2 -> J -> K -> 1`.                     `(FKG1)`

This is a **finite-kernel** extension.  It is not a finite-index extension.
The usual MF permanence argument applies in the opposite orientation:
if an MF normal subgroup has finite quotient, the whole group embeds into a
finite wreath product and is MF.  It gives no conclusion from `(FKG1)`.

This distinction is load-bearing.  Were MF automatically preserved under
finite central kernels, the difficult projective-representation obstructions
in Deligne-type covers would disappear.  Bachner--Dogon--Lubotzky,
Proposition 1.6, likewise assumes separately that the total finite-kernel
extension is MF; it does not prove that hypothesis.

Thus `(RMD6)` does not prove that `J` is MF.

## 3. Exact projective-sector criterion

The missing datum can be stated without any amalgam notation.

Let

`1 -> <z> ~= C_p -> E -q-> K -> 1`                   `(PSC1)`

be a central extension, where `p` is prime, and assume `K` is MF.  Choose a
normalized section `s:K->E` and write

`s(k)s(l)=omega(k,l)s(kl)`, `omega(k,l) in C_p`.      `(PSC2)`

Let `chi:C_p->T` be any nontrivial character (hence faithful).

**Theorem (one projective sector is necessary and sufficient).**  The group
`E` is MF if and only if there are dimensions `d_n` and maps

`v_n:K->U(d_n)`                                       `(PSC3)`

such that, for every fixed `k,l in K`,

`||v_n(k)v_n(l)-chi(omega(k,l))v_n(kl)||_op -> 0`.    `(PSC4)`

No injectivity condition on `(v_n)` is required.

**Proof.**  Suppose first that `E` embeds in the unitary group of a norm
matrix corona `Q`.  The image `Z` of `z` is a central unitary with `Z^p=1`.
Because the embedding does not kill `z`, at least one nontrivial spectral
projection

`e_chi=(1/p) sum_(a=0)^(p-1) conjugate(chi(z^a)) Z^a` `(PSC5)`

is nonzero.  In the corner `e_chi Q e_chi`, put

`v(k)=e_chi Phi(s(k))`.                                `(PSC6)`

Equations `(PSC2)` and `(PSC5)` make `(PSC4)` exact in the corona.  Lifting
the projection and the countable family of unitaries to matrix corners gives
the asymptotic maps `(PSC3)--(PSC4)` after diagonalization.

Conversely, let `rho:K->U(Q_0)` be an injective norm-corona homomorphism and
let `v:K->U(Q_chi)` be the projective homomorphism induced by `(PSC3)--(PSC4)`.
Define

`Phi(z^a s(k))=rho(k) directSum chi(z^a)v(k)`.         `(PSC7)`

Equation `(PSC4)` proves multiplicativity.  If an element is nontrivial
modulo `<z>`, the first summand detects it; if it is a nontrivial power of
`z`, faithfulness of `chi` detects it in the second summand.  Hence `Phi` is
injective and `E` is MF.  End proof.

For `p=2`, `(PSC4)` is precisely a nonzero `-1`-multiplier sector.  Applied
to `(FKG1)`, it says:

> the shear group is MF exactly when its central-extension cocycle admits
> operator-norm asymptotic projective representations with multiplier `-1`.

The faithful MF data of the quotient and the projective data which retain
`z` may live in separate direct-sum blocks.  Consequently the open problem
is not to make the projective sector faithful; it is only to make it exist.
In C-star language, one needs a nonzero MF representation of the relevant
twisted group algebra.

There is a useful rigidity corollary when the kernel is radical.

**Corollary (the required sector is necessarily unstable).**  If, in
addition, `z in Rad_sof(E)`, then there is no honest finite-dimensional
projective representation satisfying `(PSC4)` exactly and detecting `z`.

**Proof.**  Such a projective representation is the same thing as a
finite-dimensional representation of `E` on which `z` acts by the faithful
character `chi`.  Its image is a finitely generated linear group, hence is
residually finite by Malcev and therefore sofic.  This would give a sofic
image of `E` which does not kill `z`, contrary to radicality.  End proof.

Thus any positive solution of `(PSC4)` must be a genuinely non-liftable
operator-norm asymptotic projective representation.  A stability theorem
which corrects `(PSC4)` to honest finite-dimensional projective
representations would rule out this candidate rather than prove it MF.

## 4. What the recent stability inputs do not yet supply

Lubotzky--Salomon's flexible operator-norm stability of `Z^2` removes a
winding obstruction by adjoining `o(d_n)` clock--shift dimensions and then
correcting an almost commuting pair.  The cyclic shear edge is already
exactly balanced in finite dimensions; its obstruction is extension of that
balanced sector across the radical vertex.  Flexible stability of the edge
does not construct `(PSC3)` for the quotient cocycle.  In view of the
preceding corollary, a hypothetical flexible-stability theorem for the full
twisted relation would instead prove that no such sector exists.

Paddock's maximally-entangled rounding theorem improves near-optimal quantum
strategies to tracial/maximally-entangled ones.  Its error is an averaged
game loss.  It does not impose operator-norm control of all fixed group
relations and therefore cannot guarantee the nonzero norm-corona projective
sector `(PSC3)--(PSC4)`.  A sector supported on negligible normalized rank is
exactly what tracial rounding is allowed to ignore.

There is a refined positive reading once a scalar negative sector is already
present.  Paddock's Lemma 3.26 only needs a nonzero output subspace, and an
exact scalar `z=-1` would survive on that subspace without any relative-rank
bound.  The missing input is then its approximate-tracial commutator
hypothesis, not output dimension.  The exact induced Mackey model in the
next section is nonamenable and has no approximately central finite-rank
density matrices, so it does not furnish that hypothesis.

The audited FALSE endpoint is therefore `(PSC4)`, equivalently the existing
corona covariance condition `(CRC4)`.  Proving it for the cyclic radical
shear would make `J` weak MF; its central radical involution would then yield
a hyperlinear nonsofic corner.  It remains unproved.

## 5. Exact infinite-dimensional realization of the missing sector

The projective sector is not empty at infinite dimension.  For the
free-stabilized shear, put `G=H*<a>`, `C=<r>`, and let

`pi_0=Ind_C^G(1)`,  `pi_1=Ind_C^G(chi)`,

where `chi(r^n)=(-1)^n`.  Mackey restriction and translation length in the
free-product Bass--Serre tree give

`Res_C(pi_0) ~= chi tensor Res_C(pi_1)`.               `(PSC8)`

Indeed, on a double-coset summand with stabilizer
`C intersect tCt^(-1)`, a nontrivial equality
`r^m=t r^n t^(-1)` forces `|m|=|n|`; hence the two parity characters agree
on the stabilizer.  After tensoring by `chi` they cancel.

An intertwiner in `(PSC8)` glues the two induced vertex representations
across the twisted edge and produces an exact representation of the shear
on which `z=-1`.  Thus the missing sector has a canonical exact
infinite-dimensional model.  The remaining problem is to prove that the
C-star algebra generated by this model is MF.  If it is, normalized matrix
traces produce a hyperlinear image in which the radical element `z`
survives, and that image is nonsofic.

The full proof and the resulting concrete MF target are recorded in
`notes/FALSE_MACKEY_SECTOR.md`.
