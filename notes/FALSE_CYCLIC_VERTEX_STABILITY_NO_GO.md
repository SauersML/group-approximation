# Cyclic vertex sectors cannot supply the missing HS instability

Date: 2026-08-11

## 1. Purpose

The one-orbit clutching form of the coinduced parity candidate reduces its
algebraic twist to one regular `Gamma`-orbit.  After the exact-vertex matching
no-go, a tempting next move is to import one of Eckhardt's operator--HS
unstable amenable groups into a cyclic lamp direction of a residually finite
vertex.

This note rules out that move.  The obstruction is structural and
quantitative:

* every finite window in a cyclic vertex sector lies in `A wr Z` for a
  **finite abelian** lamp group `A`;
* Dogon--Vidick's polynomial HS correction theorem applies to every such
  `A wr Z`;
* Eckhardt's unstable unipotent group has torsion-free derived subgroup, so it
  cannot occur in the binary cyclic sector even algebraically.

Consequently the genuinely nonliftable vertex model required by
`FALSE_RF_VERTEX_HS_MATCHING_NO_GO.md` must use several acting directions of
the Kazhdan vertex at once.  It cannot be supported on one cyclic lamp orbit.

## 2. The cyclic preimage

Let `G` act freely on a set `Y` and put

`W=(directSum_Y C_2) semidirect G`.                    `(CVS1)`

Fix an infinite-order element `q in G`, and let `W_q` be the inverse image of
`<q>` under `W -> G`:

`W_q=(directSum_Y C_2) semidirect <q>`.                `(CVS2)`

Because the `G`-action on `Y` is free, the restricted `<q>`-action is free.
Choosing a set `I` of its orbits gives an isomorphism of `<q>`-sets

`Y ~= I times Z`, `q(i,n)=(i,n+1)`.                    `(CVS3)`

For a finite subset `I_0 subset I`, define

`W_(q,I_0)=(directSum_(I_0 times Z) C_2) semidirect <q>`.
                                                               `(CVS4)`

If `A_(I_0)=C_2^(I_0)`, regrouping the lamps at each integer coordinate gives

`W_(q,I_0) ~= A_(I_0) wr Z`.                           `(CVS5)`

## 3. Every finite window is a finite-abelian lamplighter window

**Theorem 1 (cyclic-window exhaustion).**  Every finite subset of `W_q` is
contained in `W_(q,I_0)` for some finite `I_0`.  In particular

`W_q=directLimit_(I_0 finite subset I) A_(I_0) wr Z`. `(CVS6)`

**Proof.**  Each element of the restricted direct sum has finite support in
`Y`.  A finite set of elements therefore meets only finitely many
`<q>`-orbits; call their set `I_0`.  Its lamp parts and its cyclic acting parts
all lie in `(CVS4)`.  Equation `(CVS5)` finishes the proof.

The point is not merely that the groups in `(CVS5)` are amenable.  The main
theorem of Dogon--Vidick,
[*Polynomial Hilbert--Schmidt stability of the lamplighter group*](https://arxiv.org/abs/2607.20135),
proves a quantitative correction theorem for `C_2 wr Z` and states explicitly
that the proof works equally well for `A wr Z` for every finite abelian `A`.
Thus it applies to every group in `(CVS5)`.

**Corollary 2 (finite-window HS correction).**  Let

`phi_n:W_q -> U(d_n)`                                  `(CVS7)`

be an asymptotic representation in normalized Hilbert--Schmidt norm.  For
every finite set `F subset W_q`, there are a finite `I_0` and genuine
finite-dimensional representations

`rho_n:W_(q,I_0) -> U(d_n)`                            `(CVS8)`

such that `F subset W_(q,I_0)` and, after discarding finitely many `n`,

`max_(x in F) ||phi_n(x)-rho_n(x)||_2 -> 0`.           `(CVS9)`

**Proof.**  Choose `I_0` by Theorem 1 and restrict `phi_n` to the fixed group
`W_(q,I_0) ~= A_(I_0) wr Z`.  Its defects on every fixed relation tend to
zero.  Apply HS stability of this finite-abelian lamplighter and then restrict
the resulting correction to `F`.

This is a local statement: `rho_n` need not extend to all of `W_q`.  That is
exactly the amount needed to rule out an instability mechanism confined to a
fixed cyclic lamp window.

There is a stronger conclusion when the maps are trace separating.  Theorem
1.1 of Burton--Chaudkhari--Juschenko--Muliarchyk,
[*Hyperlinear approximations to amenable groups come from sofic
approximations*](https://arxiv.org/abs/2311.09202), says that every sufficiently
accurate hyperlinear approximation of an amenable group is close, on any
prescribed finite set and in the **same dimension**, to permutation matrices
coming from a sofic approximation.  Since every group in `(CVS5)` is
amenable, it gives the following upgrade.

**Corollary 3 (same-dimension permutationization).**  Fix finite
`I_0 subset I`, a finite set `E subset W_(q,I_0)`, and `epsilon>0`.  There are
a finite set `F subset W_(q,I_0)` and `delta>0` such that every
`(F,delta)`-hyperlinear approximation

`alpha:W_(q,I_0)->U(d)`

is accompanied by an `(E,epsilon)`-sofic approximation on a set of cardinality
`d`, whose permutation matrices `beta` satisfy

`max_(g in E) ||alpha(g)-beta(g)||_2^2 <= epsilon`.       `(CVS10)`

Thus Dogon--Vidick and Burton--Chaudkhari--Juschenko--Muliarchyk control two
different regimes of the same cyclic sector:

* without trace separation, the lamplighter relations are polynomially
  correctable to an exact unitary representation;
* with the regular trace separation required of a hyperlinear model, the
  matrices are directly correctable to a sofic-induced model in the same
  dimension.

The second statement does not require permutation stability of the
lamplighter group: the resulting permutations are a sofic approximation, not
necessarily an exact finite action.

The harmless central `C_2` factor in the vertex decomposition

`J_i ~= C_2 times ((directSum_Y C_2) semidirect G_i)`  `(CVS11)`

does not change the conclusion: a fixed finite group has HS-stable relations,
and one may correct that factor together with the finite window.

## 4. Eckhardt's unipotent core cannot embed in the cyclic sector

Eckhardt's basic unstable group is

`G_p=Z[1/p]^2 semidirect_alpha Z`,
`alpha=[[1,1],[0,1]]`.                                 `(CVS12)`

Writing its elements as `(a,b,c)`, the multiplication is

`(a_1,b_1,c_1)(a_2,b_2,c_2)`
` =(a_1+a_2+c_1 b_2,b_1+b_2,c_1+c_2)`.                `(CVS13)`

If `t=(0,0,1)` and `u_b=(0,b,0)`, then

`[t,u_b]=(b,0,0)`.                                    `(CVS14)`

Hence `[G_p,G_p]` contains a copy of the torsion-free group `Z[1/p]`.

By contrast, for every finite abelian group `A` the derived subgroup of
`A wr Z` is contained in its lamp base `directSum_Z A`.  In the binary vertex
case `A=C_2^m`, that base has exponent two.  Therefore:

**Proposition 3.**  No `G_p` embeds in any binary cyclic vertex group
`C_2^m wr Z`.

**Proof.**  An embedding restricts injectively to the derived subgroup.
Equations `(CVS12)--(CVS14)` put a torsion-free copy of `Z[1/p]` in the
source derived subgroup, whereas the target derived subgroup has exponent
two.  This is impossible.

In particular the unipotent trace obstruction `(CVS12)--(CVS14)` is not an
internal cyclic-lamp obstruction for `(CVS2)`.

Eckhardt's finitely generated class-three-nilpotent-by-cyclic and finitely
presented solvable linear examples are finite-dimensional overgroups built to
retain this same `Z[1/p]` unipotent trace obstruction.  Merely replacing their
torsion-free unipotent coordinates by binary lamps removes the mechanism and
lands back in the stable family `(CVS5)`.

## 5. Consequence for the FALSE program

The exact RF-vertex no-go already proves that positive negative-corner rank
cannot come from asymptotically matching honest vertex representations.  The
present calculation rules out the most obvious source of the required
nonhonest representation as well:

> The missing HS instability cannot be localized to one infinite cyclic
> actor and finitely many of its binary lamp orbits.

A successful model must use a genuinely higher-dimensional portion of the
`G_i`-action--for example a multi-generator Kazhdan/Schreier cocycle--and its
failure of liftability must survive on that whole portion.  Clock/shift,
single-tower, and Eckhardt-unipotent substitutions do not meet this condition.

This does not prove that the full vertex `J_i` is HS-stable, nor would such a
claim be expected from the argument.  It isolates precisely where a
nonliftable sector would have to live.  In particular, the trace-separated
part of that sector cannot hide a nonpermutational obstruction inside an
amenable cyclic window; any surviving obstruction must occur in the gluing
across several nonamenable acting directions.
