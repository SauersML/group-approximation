# FALSE lane: coamenability cannot move a central sofic-radical element

Date: 2026-08-10

This note corrects the earlier proposal to detect a central sofic-radical
element in a coamenable coset action.  Such an action cannot exist.  Følner
truncation turns any fixed-point-free element of an amenable action into a
nontrivial element of a sofic image.

Throughout, let `J` be a countable group and write

`Rad_sof(J)=intersection_(phi:J->S, S sofic) ker(phi)`.         `(CAF1)`

## 1. Følner truncation detects a fixed-point-free element

**Theorem.**  Let `J action X` be an amenable action on a countable set.  If
`z in J` acts without fixed points on `X`, then

`z notin Rad_sof(J)`.                                         `(CAF2)`

**Proof.**  Choose a Følner sequence of nonempty finite sets `F_n subset X`,
diagonalized over `J`, so that

`|g F_n triangle F_n|/|F_n| -> 0` for every `g in J`.         `(CAF3)`

For each `g in J`, its action restricts to a bijection

`D_(g,n)=F_n intersect g^(-1)F_n  ->  R_(g,n)=F_n intersect gF_n`.
                                                                    `(CAF4)`

The two complements in `F_n` have equal cardinality, so complete `(CAF4)`
arbitrarily to a permutation `sigma_n(g) in Sym(F_n)`.

Fix `g,h in J`.  If

`x, h x, gh x in F_n`,                                      `(CAF5)`

then all three relevant partial maps in `(CAF4)` are unchanged by completion
and

`sigma_n(g)sigma_n(h)x=ghx=sigma_n(gh)x`.                   `(CAF6)`

The complement of `(CAF5)` has relative size at most

`|hF_n triangle F_n|/|F_n|`
`  + |ghF_n triangle F_n|/|F_n| -> 0`.                      `(CAF7)`

Thus `(sigma_n)` is pointwise asymptotically multiplicative.  It defines a
homomorphism from `J` to a metric ultraproduct of finite symmetric groups.

On `D_(z,n)`, the permutation `sigma_n(z)` agrees with the original action
of `z`, which has no fixed points.  Hence every fixed point introduced by
the arbitrary completion lies in `F_n minus D_(z,n)`, and

`|Fix(sigma_n(z))|/|F_n|`
` <= |zF_n triangle F_n|/|F_n| -> 0`.                        `(CAF8)`

The ultraproduct image of `z` is therefore nontrivial.  The countable image
group is sofic, so the composite map from `J` to that image witnesses
`(CAF2)`.  End proof.

The argument needs no centrality.  Centrality enters only when a coset action
must be shown fixed-point-free.

## 2. Central radical elements lie in every coamenable subgroup

**Corollary.**  If

`z in Z(J) intersect Rad_sof(J)`                              `(CAF9)`

and `L<J` is coamenable, then

`z in L`.                                                     `(CAF10)`

**Proof.**  The action `J action J/L` is amenable.  If `z notin L`, then for
every coset

`z gL=gL  iff  g^(-1)zg=z in L`,                             `(CAF11)`

where centrality was used.  Thus `z` acts without fixed points, contradicting
the theorem and `(CAF9)`.  End proof.

In particular, a group in the Glasner--Monod class `calA` of faithful,
transitive, amenable actions has

`Z(J) intersect Rad_sof(J)={1}`.                              `(CAF12)`

Indeed, a nontrivial central element acts fixed-point-freely in every faithful
transitive action: if it fixed one point, centrality and transitivity would
make it fix all points.

## 3. All coamenable monomial negative sectors are impossible

Suppose `z` is a central involution satisfying `(CAF9)`, `L<J` is
coamenable, and `chi:L->{+-1}` is a character with `chi(z)=-1`.  Its kernel
`K=ker(chi)` has finite index in `L`, hence is coamenable in `L`; by
transitivity of coamenability, `K` is coamenable in `J`.  But `z notin K`,
contradicting `(CAF10)`.  Therefore

> no character of any coamenable subgroup can induce a negative scalar
> sector for a central element of the full sofic radical.      `(CAF13)`

Normality is unnecessary.  The normal-coamenable commutator theorem in
`FALSE_AMENABLE_SECTOR_AUDIT.md` remains a stronger algebraic conclusion in
its narrower setting, but nonnormality does not evade the representation
obstruction.

## 4. Consequence for the cyclic shear

For the cyclic shear `J` of `FALSE_MACKEY_SECTOR.md`, the central involution
`z` belongs to `Rad_sof(J)`.  Hence:

1. every coamenable subgroup of `J` contains `z`;
2. `J` does not admit a faithful transitive amenable action;
3. the class-`calA` theorems of Moon, Fima, and Azuelos--Gaboriau cannot
   apply in a way that moves `z`;
4. no quasi-regular or coamenably induced monomial representation supplies
   the negative sector.

The amenable-negative-sector criterion from
`FALSE_AMENABLE_SECTOR_AUDIT.md` is still valid for an arbitrary amenable
unitary representation with `pi(z)=-1`.  This note proves that such a
representation, if it exists, must be genuinely nonmonomial: it cannot arise
by inducing a character from a coamenable subgroup.  The exact Mackey model
is nonamenable, so the surviving FALSE target remains a nonamenable
Connes-embeddable trace or a genuinely nonmonomial amenable negative sector.

## 5. A hypothetical shear action already separates a vertex witness

Although `(CAF2)` already rules out a fixed-point-free amenable action of the
cyclic shear, the collaborator's displacement computation gives a useful
quantitative localization of the same failed route.  Let `m` be a
`J`-invariant mean on an arbitrary `J`-set `X`, and define

`d_m(g,h)=m({x in X : gx != hx})`.                         `(CAC9)`

Write `x_i,a_i,r_i=[x_i,a_i]` for the elements in the two vertex copies,
where each `x_i` is the copy of the original nontrivial element
`x in Rad_sof(H)`.  The shear relation is

`r_1=r_2 z`, and hence `z=r_2^(-1) r_1`.                  `(CAC10)`

**Proposition (displacement collapse).**  If `z` acts freely on `X`, then

`max(d_m(x_1,1),d_m(x_2,1)) >= 1/4`.                     `(CAC11)`

Consequently, even before applying `(CAF2)`, the restricted action of one
vertex copy of `H` already gives an amenable trace whose hyperlinear image
retains the original radical witness `x`.

**Proof.**  Invariance of `m` makes `(CAC9)` bi-invariant.  Since `z` acts
freely, `d_m(z,1)=1`.  The triangle inequality and `(CAC10)` give

`1 <= d_m(r_1,1)+d_m(r_2,1)`.                            `(CAC12)`

For every pair of permutations `u,v`, bi-invariance also gives

`d_m([u,v],1)`
` <= d_m(u^(-1),1)+d_m(v^(-1)uv,1)`
` =2 d_m(u,1)`.                                         `(CAC13)`

Applying `(CAC13)` to `r_i=[x_i,a_i]` in `(CAC12)` yields

`1 <= 2d_m(x_1,1)+2d_m(x_2,1)`,                         `(CAC14)`

which proves `(CAC11)`.

Restrict the action and invariant mean to the vertex copy of `H` selected by
`(CAC11)`.  The diagonal-state construction gives an amenable trace `tau_H`
on its permutation image, and

`tau_H(u(x_i))=m(Fix_X(x_i))=1-d_m(x_i,1) <= 3/4`.       `(CAC15)`

Thus `x_i` survives in the tracial matrix-ultraproduct image furnished by
amenability of `tau_H`.  If that image were sofic, the homomorphism from `H`
to it would kill `x_i in Rad_sof(H)`, contradicting `(CAC15)`.  The image is
therefore hyperlinear and nonsofic.  End proof.

This proposition is conditional: `(CAF2)` says that its hypothesis cannot
hold for the cyclic shear because `z in Rad_sof(J)`.  Its value is to show
where the hypothetical separation would already occur.  It cannot emerge
only after amalgamation; it is already present as positive mean displacement
of the original radical element in one vertex.  The associated analytic
target is an amenable `H`-action with an invariant mean `m` satisfying
`m(Fix_X(x))<1`, not a class-`calA` permanence theorem for the shear.

## 6. Prescribed invariant means also have coherent finite models

The last target in the preceding paragraph is itself impossible.  The
fixed-point-free hypothesis of `(CAF2)` can be replaced by positive
displacement with respect to one specified invariant mean.

**Theorem (co-soficity of invariant-mean permutation characters).**  Let a
countable group `J` act on a countable set `X`, and let `m` be a
`J`-invariant mean on `X`.  Put

`theta_m(g)=m(Fix_X(g))`.                                  `(CAP1)`

There are finite `J`-tables `sigma_n:J->Sym(Omega_n)` such that, for every
`g,h in J`,

`d_H(sigma_n(g)sigma_n(h),sigma_n(gh))->0`,                `(CAP2)`

and

`|Fix(sigma_n(g))|/|Omega_n| -> theta_m(g)`.               `(CAP3)`

Consequently, after pullback along any free presentation `q:F->J`, the
function `theta_m circle q` is a pointwise limit of finite-`F`-action
characters, and

`J/{g : theta_m(g)=1}` is sofic.                            `(CAP4)`

**Proof, step 1: a Reiter sequence prescribed by `m`.**  Finitely supported
probability measures are weak-star dense in the means on `X`: for any finite
family of bounded functions, the vector of their `m`-values lies in the
closed convex hull of their point-evaluation vectors.  Otherwise a finite-
dimensional separating functional would give a bounded function `f` with
`m(f)>sup_X f` or `m(f)<inf_X f`, contradicting positivity of `m`.

Choose a net of finitely supported probabilities `mu_i` converging weak-star
to `m`.  For a fixed finite `S subset J`, the tuple

`T_S(mu_i)=(g mu_i-mu_i)_(g in S)`                         `(CAP5)`

converges weakly to zero in the finite direct sum of copies of `ell^1(X)`,
because `m` is invariant.  Mazur's lemma supplies convex combinations of a
tail for which `(CAP5)` tends to zero in norm.  Tail convex combinations
remain finitely supported probabilities and retain all previously imposed
weak-star tests.  Diagonalizing over `J` and the countable family of
indicators `1_(Fix_X(g))` gives finitely supported probabilities `mu_n` with

`||g mu_n-mu_n||_1 -> 0`,
`mu_n(Fix_X(g)) -> theta_m(g)` for every `g in J`.           `(CAP6)`

Approximate the finitely many nonzero weights of each `mu_n` by rational
weights.  After another diagonal choice, `(CAP6)` still holds.  Write the
rational probability as

`mu_n(x)=c_(n,x)/M_n`, `sum_x c_(n,x)=M_n`.                `(CAP7)`

**Step 2: coherent numbered fibers.**  Define

`Omega_n={(x,k):1<=k<=c_(n,x)}`.                            `(CAP8)`

For `g in J`, use the canonical partial bijection

`(x,k) |-> (gx,k)` whenever `k<=min(c_(n,x),c_(n,gx))`.     `(CAP9)`

Its domain and range have the same cardinality, so complete it arbitrarily
to a permutation `sigma_n(g)` of `Omega_n`.  The proportion outside the
canonical domain is

`b_n(g)=1/2 ||g mu_n-mu_n||_1`.                            `(CAP10)`

The common fiber index in `(CAP9)` is essential.  If a point lies in the
canonical domains for `h`, then for `g` after `h`, and also for `gh`, both
composites send `(x,k)` to `(ghx,k)`.  A union bound therefore gives

`d_H(sigma_n(g)sigma_n(h),sigma_n(gh))`
` <= b_n(h)+b_n(g)+b_n(gh) -> 0`,                          `(CAP11)`

which proves `(CAP2)`.

On a fiber over `x in Fix_X(g)`, `(CAP9)` is the identity on the entire
fiber.  On every other canonical-domain point it moves to a different
fiber.  Only the completion points can contribute additional fixed points.
Hence

`mu_n(Fix_X(g))`
` <= |Fix(sigma_n(g))|/M_n`
` <= mu_n(Fix_X(g))+b_n(g)`.                               `(CAP12)`

Equations `(CAP6)`, `(CAP10)`, and `(CAP12)` prove `(CAP3)`.  The maps
`sigma_n` induce a homomorphism to a metric ultraproduct of finite symmetric
groups.  Its kernel consists exactly of the elements for which
`theta_m(g)=1`, proving `(CAP4)`.  Finally, for a free presentation
`q:F(A)->J`, assign the generator `a` the permutation `sigma_n(q(a))` and
extend this assignment to an honest finite `F(A)`-action.  Telescoping
`(CAP2)` along each fixed word `w` shows that its permutation differs in
Hamming distance from `sigma_n(q(w))` by a quantity tending to zero.  Its
fixed-point character therefore converges to `theta_m(q(w))`, proving the
stated co-sofic character conclusion.  End proof.

**Radical consequence.**  If `x in Rad_sof(J)`, then every invariant mean
for every amenable `J`-action satisfies

`m(Fix_X(x))=1`.                                           `(CAP13)`

Otherwise `(CAP4)` is a sofic image retaining `x`.  Thus no amenable action
of the original vertex group `H` can satisfy the final target after
`(CAC15)`.  More generally, amenable permutation representations cannot
provide a genuinely new negative sector for a sofic-radical element; any
remaining amenable negative representation must be nonpermutational as well
as nonmonomial.
