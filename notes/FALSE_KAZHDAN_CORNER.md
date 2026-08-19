# FALSE lane: Kazhdan-corner extraction and the envelope barrier

This note isolates a useful conversion theorem for operator-norm models and
audits the tempting universal-Kazhdan-envelope shortcut.  Here **weak MF**
means an injective homomorphism into a norm matrix corona

`B = (product_n M_(d_n))/(directSum_n M_(d_n))`,

where the ideal consists of sequences converging to zero in operator norm.

## 1. A weak-MF Kazhdan group has a nontrivial hyperlinear quotient

**Theorem (Kazhdan-corner extraction).**  Let `G` be a nontrivial group with
Kazhdan property `(T)`.  If `G` is weak MF, then `G` has a nontrivial
hyperlinear quotient.

**Proof.**  Let

`rho:G -> U(B)`                                             `(KC1)`

be injective.  By the universal property, `(KC1)` extends to a unital
star-homomorphism

`Phi:C*_max(G) -> B`.                                      `(KC2)`

Let `p` be the central Kazhdan projection and put `q=1-p`.  In every unitary
representation, `p` projects onto the invariant vectors.  Hence

`u_g p=p`, `g in G`.                                       `(KC3)`

The projection `z=Phi(q)` is nonzero: if `z=0`, then `(KC3)` gives
`rho(g)=Phi(p)=1` for every `g`, contradicting injectivity.  In the nonzero
corner `zBz`, define

`psi(g)=z rho(g)`.                                         `(KC4)`

This representation is nontrivial, since triviality of `(KC4)` would again
give `rho(g)=Phi(p)+z=1` for every `g`.

Lift `z` to coordinate projections `z_n` of positive ranks `r_n`, discarding
finitely many zero coordinates.  Standard polar correction lifts the
unitaries `(KC4)` to maps

`psi_n:G -> U(z_n M_(d_n) z_n) ~= U(r_n)`                 `(KC5)`

whose multiplicative defects tend to zero in operator norm, hence also in
normalized Hilbert--Schmidt norm on the `r_n`-corners.

Choose a finite symmetric Kazhdan set `S`.  The Kazhdan Laplacian

`Delta=sum_(s in S) (u_s-1)^*(u_s-1)`                     `(KC6)`

has a spectral gap on the complementary corner: for some `kappa>0`,

`q Delta q >= kappa q` in `C*_max(G)`.                    `(KC7)`

Apply `Phi`, lift `(KC7)` to the matrix corners, and take normalized corner
traces.  The norm-null lifting errors disappear and give

`liminf_n sum_(s in S) ||psi_n(s)-1||_(2,r_n)^2 >= kappa` `(KC8)`

(after harmlessly shrinking `kappa`).  Therefore the homomorphism induced
by `(KC5)` into a tracial matrix ultraproduct is nontrivial.  Its kernel is a
proper normal subgroup of `G`, and its image is the required nontrivial
hyperlinear quotient.  End proof.

The point is that the norm-visible sector may have negligible rank in the
original matrices, but one is allowed to renormalize on the nonzero Kazhdan
corner.  The gap `(KC7)` then prevents the resulting tracial representation
from becoming trivial.

## 2. Simple and quasisimple consequences

**Corollary.**  A nontrivial simple Kazhdan weak-MF group is hyperlinear.

**Proof.**  The kernel produced above is proper and normal, hence trivial.
End proof.

More generally, suppose `U` is perfect, every proper normal subgroup of `U`
is central, and

`Q=U/Z(U)`                                                 `(KC9)`

is simple and nonsofic.  If `U` is Kazhdan and weak MF, Kazhdan-corner
extraction gives a hyperlinear image `U/C` with `C<=Z(U)`.  Thom's theorem
that quotients of hyperlinear groups by central subgroups are hyperlinear
then makes

`Q=(U/C)/(Z(U)/C)`                                        `(KC10)`

hyperlinear.  Since `Q` is nonsofic, `(KC10)` solves hyperlinear versus
sofic negatively.

For the explicit binary-Leavitt witness

`U=St_5(L_(F_2)(1,2))`, `Q=EL_4(L_(F_2)(1,2))`,          `(KC11)`

the repository has already checked the needed structural inputs: `U` is
finitely presented, Kazhdan, and quasisimple, while `Q` is simple and
nonsofic.  Consequently

`U weak MF  ==>  Q hyperlinear and nonsofic`.             `(KC12)`

Thus weak MF of the one concrete group in `(KC11)` is a complete FALSE-side
certificate.  It remains unproved.

## 3. Why the universal Kazhdan embedding theorem does not provide weak MF

Delzant's SQ-universality theorem says that every non-elementary hyperbolic
group is SQ-universal.  Taking a hyperbolic property-`(T)` group `P`, for
every countable group `H` there is a normal subgroup `N normal P` such that

`H embeds P/N`.                                           `(KE1)`

Since property `(T)` passes to quotients, `P/N` is a Kazhdan envelope of
`H`.  This is the standard proof that every countable group embeds in a
countable Kazhdan group.

It does **not** preserve weak MF.  Even if `P` is weak MF, obtaining weak MF
of `P/N` would require permanence under the arbitrary quotient map

`P -> P/N`.                                               `(KE2)`

Weak MF is subgroup-closed but is not known to be quotient-closed.  The
usual free-group presentation already shows the scale of the missing
principle: quotient permanence for weak MF would imply that every countable
group is weak MF.  No known feature of the SQ-universal quotient makes
`(KE2)` a finite, central, amenable, or otherwise controlled quotient.

There is a second loss.  Even if one somehow proved the envelope `P/N` weak
MF, Theorem `(KC1)--(KC8)` only produces some nontrivial hyperlinear quotient
of `P/N`; its kernel may contain the embedded copy of `H`.  To transfer the
known weak-MF nonsofic group into a solution, one would need either

1. a weak-MF-preserving **simple** Kazhdan envelope, or
2. control showing that the Kazhdan corner retains a chosen nonsofic-radical
   witness from `H`.

No such preservation or retention theorem is currently available.  The
Delzant construction therefore supplies no shortcut to `(KC12)`.

## 4. Current exact target

The useful alternatives are now sharply separated:

* prove weak MF of the explicit Steinberg group `(KC11)` by constructing a
  genuinely unstable operator-norm model; or
* build a weak-MF-preserving simple Kazhdan envelope which retains the
  existing weak-MF nonsofic subgroup.

The second item is not a routine application of SQ-universality.  The first
is the more concrete certificate and is compatible with the independent
Hilbert--Schmidt-stability fork in `notes/ATLAS_HS_CRITERION.md`.

Primary source for `(KE1)`: Thomas Delzant, *Sous-groupes distingues et
quotients des groupes hyperboliques*, Duke Math. J. 83 (1996), Theorem 3.5
and the remark immediately following it.  Central-quotient permanence is
Andreas Thom, *Examples of hyperlinear groups without factorization
property*, Lemma 3.3 and Remark 3.4.
