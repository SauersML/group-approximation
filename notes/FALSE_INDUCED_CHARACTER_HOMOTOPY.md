# FALSE lane: whole-vertex induced-character homotopy

Date: 2026-08-11

This note strengthens the exact Mackey construction in
`FALSE_MACKEY_SECTOR.md`.  The two endpoint representations used there are
homotopic as representations of the **whole reduced vertex algebra**, not
only related after restriction to the cyclic edge.  The homotopy is
point-norm continuous.  This is useful positive structure, but Shulman's
ordinary homotopy-lifting theorem still does not give the norm-compatible
endpoint lifts required by the cyclic shear.

## 1. A bounded Schreier cocycle from the tree

Let a countable group `G` act on a simplicial tree `T`, let `r in G` be
hyperbolic, and put

`C=<r> isomorphic Z`.                                      `(ICH1)`

Write `ell>0` for the translation length of `r`.  Choose a vertex `v` on
the axis of `r` and a base vertex `o in T`.  For every right coset
`x in G/C`, choose a representative `s(x)` so that `s(x)v` minimizes the
distance to `o` among the lattice

`xv={g r^n v:n in Z}`.                                    `(ICH2)`

For `g in G`, define the integer Schreier cocycle `kappa(g,x)` by

`g s(x)=s(gx) r^(kappa(g,x))`.                            `(ICH3)`

**Lemma 1 (uniform cocycle bound).**  For every fixed `g in G`,

`sup_(x in G/C)|kappa(g,x)| <= d_T(o,go)/ell+2`.          `(ICH4)`

**Proof.**  The two points

`a=g s(x)v`, `b=s(gx)v`

belong to the same `ell`-spaced lattice in the line `g s(x)Axis(r)`.
The point `a` is nearest in that lattice to `go`, while `b` is nearest to
`o`.  Nearest-point projection onto a geodesic in a tree is 1-Lipschitz,
and replacing a projected point by a nearest lattice point costs at most
`ell`.  Hence

`d_T(a,b) <= d_T(o,go)+2ell`.                            `(ICH5)`

Equation `(ICH3)` and the fact that `v` lies on the axis give

`d_T(a,b)=|kappa(g,x)|ell`.

This proves `(ICH4)`.  End proof.

The estimate is independent of properness of the action and of the sizes
of vertex stabilizers.  It therefore applies directly to the Bass--Serre
tree of the free stabilization `G=H*<a>` used by the cyclic shear.

## 2. The induced characters form a point-norm path

For `theta in R`, let

`chi_theta(r^n)=exp(i theta n)`,
`pi_theta=Ind_C^G(chi_theta)`.                           `(ICH6)`

Using the section in `(ICH2)`, all the representations act on the same
space `ell^2(G/C)`.  Up to the harmless choice of inverse convention, their
monomial formula is

`pi_theta(g)delta_x`
`  =exp(i theta kappa(g,x))delta_(gx)`.                 `(ICH7)`

**Theorem 2 (point-norm induced-character homotopy).**  For every `g in G`,

`||pi_theta(g)-pi_phi(g)||`
` <= (d_T(o,go)/ell+2)|theta-phi|`.                    `(ICH8)`

Consequently `theta |-> pi_theta` is a point-norm continuous path of
star-homomorphisms

`C*_r(G) -> B(ell^2(G/C))`.                             `(ICH9)`

**Proof.**  The difference in `(ICH8)` is a weighted permutation matrix.
Its norm is the supremum of the absolute differences of its weights.
Equations `(ICH4)` and `(ICH7)`, together with
`|exp(it)-exp(is)|<=|t-s|`, give `(ICH8)`.

The estimate first gives point-norm continuity on the complex group ring.
Every `pi_theta` is weakly contained in `lambda_G`: the cyclic group `C` is
amenable, hence `chi_theta` is weakly contained in `lambda_C`; induction
preserves weak containment; and

`Ind_C^G(lambda_C) is unitarily equivalent to lambda_G`. `(ICH10)`

Thus the maps factor through `C*_r(G)`.  Contractivity and density extend
the point-norm continuity from the group ring to all of `C*_r(G)`.  End
proof.

## 3. The Mackey endpoints are homotopic on the whole vertex

Put `chi=chi_pi`.  The Mackey parity theorem from
`FALSE_MACKEY_SECTOR.md` supplies a unitary `U` such that

`U pi_pi(c) U^*=chi(c)pi_0(c)`, `c in C`.              `(ICH11)`

Every unitary on a complex Hilbert space has a bounded self-adjoint Borel
logarithm.  Choose `L=L^*` with `U=exp(iL)`.  Concatenate the path

`pi_0 -> pi_theta -> pi_pi`, `0<=theta<=pi`,

with the norm-continuous conjugation path

`pi_pi -> Ad(exp(itL))pi_pi`, `0<=t<=1`.               `(ICH12)`

This proves:

**Corollary 3 (whole-vertex endpoint homotopy).**  The homomorphisms

`psi=pi_0`, `phi=Ad(U)pi_pi:C*_r(G)->B(ell^2(G/C))`    `(ICH13)`

are homotopic, and their edge restrictions satisfy

`phi(r^n)=(-1)^n psi(r^n)`.                             `(ICH14)`

If `calB` is the regular MF completion of `G` used in
`FALSE_FINITE_KERNEL_AUDIT.md`, its regular GNS representation gives a
surjection

`q_reg:calB -> C*_r(G)`.                                `(ICH15)`

Composing `(ICH13)` with `q_reg` therefore gives a homotopy of
representations of the entire MF vertex algebra `calB` with exactly the
desired parity relation at the endpoint.

This is strictly stronger than the edge-only homotopy `(HSE1)` in the
notebook.

## 4. What Shulman's theorem gives

Let `mathcal D` be the algebra of star-strongly convergent matrix sequences,
let `I` be its star-strongly-null ideal, and let

`q_D:mathcal D -> B(ell^2(G/C))`                       `(ICH16)`

be the limit map.  Since `calB` is MF, Shulman's lifting characterization
(arXiv:2508.00125v5, Theorem 15) gives a discrete asymptotic lift of `psi`.
Her homotopy-lifting theorem (Theorem 11) then lifts the whole homotopy in
`(ICH13)`.

In particular, it gives endpoint asymptotic lifts `Psi_j,Phi_j` with

`q_D(Phi_j(r)+Psi_j(r))=0`.                             `(ICH17)`

But `(ICH17)` says only

`Phi_j(r)+Psi_j(r) in I`.                               `(ICH18)`

It does not imply

`||Phi_j(r)+Psi_j(r)|| ->0`,                            `(ICH19)`

which is the operator-norm compatibility needed in `(CRC3)/(CRC4)`.
For example, the sequence of rank-one projections onto the last coordinate
of `C^n` belongs to `I` and has norm one at every level.

The proof of Shulman's theorem makes the obstruction especially explicit.
The mapping-cylinder coordinate is lifted by a quasicentral positive
contraction whose quotient is `1`.  Its complement can be strongly null
while retaining norm one.  Evaluation at the endpoint kills that complement
in `B(H)`, but not in the norm matrix corona.

## 5. Why the obvious projection cut is unavailable

A tempting repair is to replace the positive mapping-cylinder cutoff by
finite-rank spectral projections which are asymptotically invariant in
operator norm.  In this Mackey model that would contradict the already
proved nonamenability of the quasi-regular representation.

Indeed, suppose there were nonzero finite-rank projections `P_j` with

`||[P_j,pi_0(g)]|| ->0` for every `g in G`.             `(ICH20)`

Normalized traces on the corners `P_j B(H)P_j` have a weak-star cluster
point which is a `pi_0(G)`-central state on `B(H)`.  Restriction to the
diagonal algebra `ell^infinity(G/C)` gives a `G`-invariant mean on `G/C`.
Thus `C` would be coamenable in `G`.

In the shear application, `C` is amenable and `G=H*Z` is nonamenable.  If
`C` were coamenable, amenability of the subgroup and of the homogeneous
action would make `G` amenable, a contradiction.  Hence `(ICH20)` is
impossible.

This does not disprove every conceivable relative lifting theorem.  It
does prove that the natural strategy

`whole-vertex homotopy + Shulman lift + projectional endpoint cut`

cannot create the required projective sector from the Mackey model.

## 6. Updated live gate

The positive result is:

> the parity-twisted Mackey endpoints are joined by an explicit point-norm
> homotopy of representations of the whole regular MF vertex.

The remaining missing theorem is still relative:

> turn that lifted whole-vertex homotopy into endpoint lifts agreeing in the
> **norm** matrix corona on the parity-twisted cyclic edge, without producing
> an amenable/quasidiagonal approximation of `Ind_C^G(1)`.

Ordinary homotopy lifting stops at the strong ideal `(ICH18)`.  Solving this
relative norm problem would establish `(PSC4)/(CRC4)`, make the cyclic shear
MF, and then the finite-radical corner theorem would produce a hyperlinear
nonsofic quotient.

## Primary source

* T. Shulman, *Homotopy lifting, asymptotic homomorphisms, and traces*,
  arXiv:2508.00125v5, Theorems 11 and 15.
