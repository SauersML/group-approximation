# FALSE lane: coamenable actions that move a central radical element

Date: 2026-08-10

This note gives an action-theoretic reformulation of the amenable-negative-
sector criterion in `FALSE_AMENABLE_SECTOR_AUDIT.md`.  A transitive amenable
permutation action gives the required trace whenever the central radical
element moves one point, because centrality then makes it move every point.
For a central involution this turns out to be equivalent to the induced-sign-
character formulation, not strictly weaker; the equivalence is proved below.

Throughout, let `J` be countable and let

`1 != z in Z(J) intersect Rad_sof(J)`.                         `(CAC1)`

Here `Rad_sof(J)` is the intersection of the kernels of all homomorphisms
from `J` to sofic groups.

## 1. The coamenable-subgroup criterion

**Theorem.**  Suppose that `J` has a coamenable subgroup `L` such that

`z notin L`.                                                   `(CAC2)`

Then a hyperlinear nonsofic group exists.

**Proof.**  Let `X=J/L`, let `u:J->U(ell^2(X))` be the quasi-regular
representation, and choose a `J`-invariant mean `m` on `X`.  Define a state
on `B(ell^2(X))` by

`Phi(T)=m(x |-> <T delta_x,delta_x>)`.                         `(CAC3)`

Conjugation by `u(g)` translates the diagonal function in `(CAC3)`.
Invariance of `m` therefore gives

`Phi(u(g) T u(g)^*)=Phi(T)`, `g in J`.                        `(CAC4)`

Consequently the restriction `tau=Phi|_(C^*(u(J)))` is tracial: `(CAC4)`
allows each generating unitary to be moved cyclically across an arbitrary
element, and linearity and norm density finish the argument.  The state
`Phi` is a hypertrace extending `tau`, so `tau` is an amenable trace.

Centrality and `(CAC2)` imply that `z` fixes no point of `X`.  Indeed,

`z gL=gL  iff  g^(-1) z g=z in L`,                            `(CAC5)`

which never occurs.  Thus

`tau(u(z))=m(Fix_X(z))=0`                                    `(CAC6)`

and, since `z` is an involution in the cyclic-shear application,

`||u(z)-1||_tau^2=2`.                                        `(CAC7)`

The matrix characterization of amenable traces supplies u.c.p. maps from
`C^*(u(J))` to matrices which recover `tau` and are asymptotically
multiplicative in normalized Hilbert--Schmidt norm.  Polar correction on a
countable diagonal sequence gives a homomorphism from the GNS image of
`u(J)` to a tracial matrix ultraproduct.  Equation `(CAC7)` says that the
image of `z` is nontrivial.  This countable image group is hyperlinear.

If the image group were sofic, the composite homomorphism from `J` to it
would have to kill `z` by `(CAC1)`, contradicting `(CAC7)`.  Hence the image
is hyperlinear and nonsofic.  End proof.

The involution assumption is inessential: for a general central `z`,
`(CAC6)` still gives
`||u(z)-1||_tau^2=2-2 Re(tau(u(z)))=2`.

## 2. Faithful transitive amenable actions are enough

Let `calA` denote the Glasner--Monod class of countable groups admitting a
faithful, transitive, amenable action on a countable set.

**Corollary.**  Under `(CAC1)`, if `J in calA`, then a hyperlinear nonsofic
group exists.

**Proof.**  Write the action as `J action J/L`.  Faithfulness means that the
core `intersection_(g in J) g L g^(-1)` is trivial.  If the central element
`z` belonged to `L`, it would belong to every conjugate of `L` and hence to
the core.  This contradicts `z!=1`.  Therefore `(CAC2)` holds and the theorem
applies.  End proof.

For a central involution, this criterion is exactly equivalent to the
coamenable induced-sign-character criterion.

**Proposition.**  The following are equivalent:

1. there is a coamenable subgroup `L<J` with `z notin L`;
2. there is a coamenable subgroup `L^+<J` and a character
   `chi:L^+->{+-1}` with `chi(z)=-1`.

**Proof.**  From (1), put `L^+=<L,z>`.  Centrality, `z^2=1`, and
`z notin L` give `L^+=L times <z>`.  A supergroup of a coamenable subgroup
is coamenable, by pushing the invariant mean from `J/L` to `J/L^+`.  The
formula

`chi(l z^e)=(-1)^e`                                      `(CAC8)`

is therefore the required character.  Conversely, from (2) put
`L=ker(chi)`.  It has finite index in `L^+`, hence is coamenable in `L^+`;
coamenability is transitive, so `L` is coamenable in `J`.  Since
`chi(z)=-1`, one has `z notin L`.  End proof.

Thus `(CAC2)` removes scalarity from the proof, but not from the existence
problem: inducing `(CAC8)` recovers a scalar negative sector, while taking
its sign kernel recovers the fixed-point-free transitive action.  In quotient
language, `(CAC2)` also says that the central extension splits over the image
of `L` in `J/<z>`.

## 3. Application boundary for the cyclic shear

For the cyclic shear

`J=(G times C_2) *_((C times C_2,id),(C times C_2,alpha))`

from `FALSE_MACKEY_SECTOR.md`, the central involution `z` satisfies `(CAC1)`.
Therefore either of the following would finish the FALSE lane:

1. prove directly that `J` has a coamenable subgroup omitting `z`;
2. prove the stronger statement `J in calA`.

The currently located class-`calA` theorems do not establish this.  Moon,
*Amenable actions of amalgamated free products* (arXiv:0810.2456), proves
the result for doubles `F_2 *_Z F_2` with cyclic amalgam.  Fima,
*Amenable, transitive and faithful actions of groups acting on trees*
(arXiv:1202.6467), treats amalgamation over a finite subgroup under
almost-free amenable-action hypotheses on the vertex groups.  The shear has
an infinite edge `C times C_2`, arbitrary nonsofic data in its vertex group,
and a twisted edge embedding.  Thus neither theorem applies as stated.

The precise equivalent group-action problem is

> construct an invariant mean on one transitive `J`-set on which the central
> involution `z` acts freely.

This is weaker than constructing a faithful action, but equivalent to the
coamenable induced-sign sector in `FALSE_AMENABLE_SECTOR_AUDIT.md`.  Its
advantage is a direct fixed-point/trace formulation, not a weaker existence
hypothesis.  No construction of that action is currently proved here.
