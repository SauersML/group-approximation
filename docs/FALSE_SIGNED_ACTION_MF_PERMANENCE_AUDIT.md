# The signed radical action lies exactly beyond strong quasidiagonality

Date: 2026-08-11

## 1. Outcome

Let `G` be countable, let `1 != s in Rad_sof(G)`, and let

`alpha:G -> Aut(A)`

be an action on a unital C-star algebra.  Suppose there is an element
`a in A` with

`||a||=1`, `alpha_s(a)=-a`.                              `(SAM1)`

Then the action is **not** quasidiagonal in the strong sense of
Kerr--Nowak: it cannot be approximated by ucp norm microstates which are
equivariant for honest actions of `G` on matrix algebras.

This applies to the signed coinduced action in
`FALSE_COINDUCED_PARITY_MODEL.md`, with `a` the base coordinate involution.
Consequently none of the crossed-product theorems whose input is a
residually finite action, or the original Kerr--Nowak strong
quasidiagonality condition, can prove MF of the signed crossed product.

There is an important distinction.  Rainone's later notions of MF and QD
actions allow the implementing matrix unitaries to be only locally
approximately multiplicative.  Those weaker notions are not excluded by
the theorem below.  In fact, an MF model for the signed action in this weak
sense would already supply the desired operator-norm one-involution
certificate and finish FALSE.  The literature therefore localizes the
problem exactly; it does not solve it.

Primary sources:

* Kerr--Nowak, *Residually finite actions and crossed products*,
  arXiv:1104.1216, Definition 3.2 and Theorem 3.4;
* Rainone, *MF Actions and K-theoretic Dynamics*, arXiv:1404.4389,
  Definition 3.3, the comparison after Theorem 3.5, Proposition 3.17, and
  Theorem 3.19;
* Rainone--Schafhauser, *Crossed products of nuclear C-star-algebras by free
  groups and their traces*, arXiv:1601.06090, Theorem 1.1.

## 2. Radical elements disappear in honest matrix actions

**Lemma 1.**  If `s in Rad_sof(G)` and

`gamma:G -> Aut(M_d)`                                      `(SAM2)`

is an action, then `gamma_s=id`.

**Proof.**  The image of `(SAM2)` is a countable subgroup of
`Aut(M_d)=PU(d)`.  The adjoint representation embeds `PU(d)` in a finite
dimensional complex linear group.  Countable linear groups are sofic
(apply Malcev residual finiteness to finitely generated subgroups and use
closure under directed unions).  By the definition of the sofic radical,
every homomorphism from `G` to a sofic group kills `s`.  Hence
`gamma_s=id`.  End proof.

This uses the full strength of an honest matrix action.  It is false for a
locally approximately multiplicative table of matrix unitaries; retaining
`s` in such a table is precisely what weak/operator MF permits.

## 3. Antipodality contradicts strong quasidiagonality

Recall the Kerr--Nowak condition.  For every finite `Omega subset A`,
finite `F subset G`, and `epsilon>0`, it asks for an honest action

`gamma:G -> Aut(M_d)`

and a ucp map `phi:A -> M_d` which is approximately multiplicative,
approximately isometric on `Omega`, and approximately equivariant on
`F times Omega`.

**Theorem 2 (radical-antipode obstruction).**  Under `(SAM1)`, `alpha` is
not strongly quasidiagonal in this sense.

**Proof.**  Put `Omega={a}` and `F={s}` and take `epsilon<2/3`.  If a
strong quasidiagonal model existed, Lemma 1 would give `gamma_s=id`.
Linearity of `phi` and equivariance would then give

`2||phi(a)||`
` =||phi(-a)-phi(a)||`
` =||phi(alpha_s(a))-gamma_s(phi(a))||<epsilon`.        `(SAM3)`

Approximate isometry gives

`||phi(a)||>||a||-epsilon=1-epsilon`.                  `(SAM4)`

Equations `(SAM3)--(SAM4)` imply `2(1-epsilon)<epsilon`, contrary to
`epsilon<2/3`.  End proof.

The same proof works with any scalar eigenrelation
`alpha_s(a)=zeta a`, provided `zeta != 1`; the numerical contradiction is

`|zeta-1|(1-epsilon)<epsilon`.                          `(SAM5)`

Thus the obstruction is not specifically binary.  Any nontrivial radical
character visible on one norm-one dynamical coordinate excludes honest
finite-dimensional equivariant models.

## 4. The concrete signed coinduced action is faithful and not residually
finite

For completeness, specialize to the symmetric double

`D=G_0 *_Gamma G_0`,
`s=i_2(h)i_1(h)^(-1)`, `C=<s>`, `Y=D/C`,                `(SAM6)`

and its signed coinduced action on `X={-1,1}^Y`.  The base coordinate
function `T(x)=x_C` satisfies

`alpha_s(T)=-T`.                                         `(SAM7)`

Hence Theorem 2 applies immediately.

There is also a purely topological exclusion.  First observe that the core

`core_D(C)=intersection_(g in D) g C g^(-1)`             `(SAM8)`

is trivial.  Indeed a nontrivial core would be an infinite cyclic normal
subgroup of `D`, because every nontrivial subgroup of `C` has finite index
in `C`.  It would force all of `D` to preserve the Bass--Serre axis of the
hyperbolic element `s`: conjugation preserves the core and the axis of any
nonzero power of `s` is the axis of `s`.  The Bass--Serre action is minimal,
so its tree would be that line.  A nondegenerate symmetric amalgam has a
line as Bass--Serre tree only when `[G_0:Gamma]=2`; but then `Gamma` is
normal in `G_0`, contrary to the defining nonnormality of the Kun--Thom
pair.  Thus `(SAM8)` is trivial.

If an element acts trivially on `X`, then in particular its induced
permutation of the coordinate set `D/C` is trivial, so it belongs to
`core_D(C)`.  Therefore the signed action is faithful.

**Lemma 3.**  A countable group admitting a faithful residually finite
continuous action on a compact Hausdorff space is residually finite.

**Proof.**  Let `g != 1`.  Faithfulness supplies `x` with `gx != x`.
Choose an entourage of the diagonal small enough to distinguish `x` from
`gx`, and apply residual finiteness of the action to the finite set
containing `g`, at a finite model point whose image is sufficiently close
to `x`.  Approximate equivariance forces `g` to move that finite-model
point.  The associated homomorphism to the permutation group of the finite
model separates `g`.  End proof.

Since `D` is nonsofic and every residually finite group is sofic, `D` is not
residually finite.  Lemma 3 shows directly that the action `(SAM6)` is not
residually finite.  This is stronger than merely observing that no chosen
finite-quotient tower works.

## 5. Exact scope of the crossed-product permanence theorems

Kerr--Nowak prove that a strong QD action has MF reduced crossed product
when `C_r^*(G)` is MF.  Their residually finite topological actions are
strongly QD.  Sections 3--4 show that neither hypothesis on the action is
available here.

Rainone deliberately weakens the action notion.  His Definition 3.3 uses a
map

`v:G -> U(M_d)`

which is only approximately multiplicative on the prescribed finite set.
He explicitly contrasts this with the honest matrix action required by
Kerr--Nowak.  For nuclear `A`, Theorem 3.19 gives

`A crossed_r G is MF`
` iff C_r^*(G) is MF and alpha is MF`                    `(SAM9)`

in this weaker sense.  Theorem 2 does not contradict weak MF: Lemma 1
cannot be applied to `v`, since `v` is not a homomorphism.

For the signed action, weak MF would contain exactly the missing data.  On
a finite window of coordinate involutions, approximate multiplicativity of
`phi` makes their images almost commuting involutions; approximate
equivariance gives

`v_s phi(T) v_s^* approximately -phi(T)`,               `(SAM10)`

and approximate multiplicativity of `v` supplies an operator-norm
asymptotic representation of `G`.  Thus proving the weak MF action property
already yields the operator-norm version of the one-involution endpoint.
It is not a permanence shortcut.

Li--Orfanos cannot apply either: their crossed-product theorem requires the
acting group itself to be amenable and residually finite and the action to
be almost periodic.  The acting group `D` is nonsofic.

## 6. Why pulling back to a free presentation does not impose the relators

Let

`q:F_r ->> D`, `N=ker(q)`,                               `(SAM11)`

and pull the signed action back to `F_r`.  Since `C(X)` is AF and the
product measure is invariant and faithful, the reduced free-group crossed
product is stably finite.  Rainone--Schafhauser's Theorem 1.1 therefore
makes

`C(X) crossed_r F_r` MF.                                `(SAM12)`

This does not approximate the desired `D`-crossed product.  In `(SAM12)`,
every nontrivial `n in N` remains a regular group unitary, even though it
acts trivially on `C(X)`.  A quotient map

`C_r^*(F_r) -> C_r^*(D)`, `lambda_f |-> lambda_(q(f))` `(SAM13)`

exists exactly when the quasi-regular representation on `F_r/N` is weakly
contained in the regular representation, equivalently when `N` is
amenable.  Here `N` is a nontrivial normal subgroup of a nonabelian free
group and hence is free of infinite rank, so it is nonamenable.  Therefore
`(SAM13)` does not exist.

There is a quotient at the **full** crossed-product level, but
Rainone--Schafhauser's theorem concerns the reduced crossed product, and MF
does not pass to arbitrary C-star quotients.  Pulling back to `F_r` has
therefore removed exactly the quotient relations that carry the radical
obstruction.

## 7. Updated endpoint

The literature audit closes three tempting routes:

1. the signed action is not residually finite;
2. it is not strongly QD via honest matrix actions;
3. its free-presentation reduced crossed product cannot be quotiented to
   the desired reduced crossed product.

The live statement is narrower and genuinely nonlinear:

> Construct Rainone-MF action microstates for the signed coinduced action,
> or directly construct their one-involution finite-window restriction,
> using approximately multiplicative matrix implementers which remain a
> definite distance from every honest finite-dimensional action.

This agrees with `FALSE_EQUIVARIANT_FIBER_FUNCTOR_STABILIZER_REDUCTION.md`:
exact finite completion kills the fold, while a successful construction
must be uniformly nonliftable.  It also explains why the paired
Fourier/Frobenius construction is the correct surviving target rather than
another finite-quotient or profinite crossed-product model.
