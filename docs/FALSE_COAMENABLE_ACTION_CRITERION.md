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
