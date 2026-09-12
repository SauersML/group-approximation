# Finite-quotient parity on one Schreier orbit is exactly subgroup separability

Date: 2026-08-11

## 1. Outcome

The one-orbit clutching reduction in
`FALSE_COINDUCED_PARITY_MODEL.md` leaves an apparently simple finite model:
on a regular `K`-orbit of lamps, negate precisely the lamps indexed by a
subgroup `H<K`.  A finite quotient of `K` implements this operation exactly
by taking parity over the image of `H`.

There is, however, an exact obstruction.  The finite quotient cannot
distinguish `H` from the larger subgroup

`H ker(q)`.                                                    `(OPS1)`

Consequently a sequence, or even a dimension-weighted mixture, of these
finite parity models converges to the desired one-orbit clutching if and only
if `H` is closed in the profinite topology of `K`.

For the Kun--Thom orbit which is nonsofic, this route is therefore
impossible: profinite separability would itself give finite Schreier models
of the coset action.  The remaining construction must be genuinely
nonmonomial.  In particular it must absorb the orbit clutching into a
base-dependent Fourier polarization or tangent-module functor, rather than
represent the distinguished orbit by the characteristic function of a
subset of a finite quotient.

This is a no-go theorem for a specific globalization mechanism.  It does
not rule out the paired Fourier/Frobenius construction.

## 2. Infinite one-orbit parity

Let `K` be a countable group and `H<K`.  Write

`A=direct_sum_(g in K) F_2 delta_g`                           `(OPS2)`

for the regular binary lamp module.  Define the distinguished-orbit
functional

`ell_H(a)=sum_(g in H) a_g in F_2`.                          `(OPS3)`

The sum is finite because `a` has finite support.  On `ell^2(A)`, let

`P_H e_a=(-1)^(ell_H(a)) e_a`,                               `(OPS4)`

and let `L(b)e_a=e_(a+b)` be lamp translation.  Then

`P_H L(delta_g) P_H^*=(-1)^(1_(g in H)) L(delta_g).`          `(OPS5)`

Moreover `P_H` commutes with the permutation action of `H` on `A`, because
left multiplication by `H` preserves the subset `H`.  Thus `(OPS4)` is the
exact parity multiplier required by the one-`H`-orbit clutching.

## 3. What a finite quotient actually implements

Let

`q:K -> Q`                                                   `(OPS6)`

be a homomorphism to a finite group.  Put

`A_q=F_2[Q]`                                                 `(OPS7)`

and push lamps forward by `delta_g -> delta_(q(g))`.  On
`ell^2(A_q)`, define

`ell_(q(H))(b)=sum_(u in q(H)) b_u`,

`P_q e_b=(-1)^(ell_(q(H))(b)) e_b`.                          `(OPS8)`

Exactly as above,

`P_q L_q(delta_(q(g))) P_q^*`
` =(-1)^(1_(q(g) in q(H)))L_q(delta_(q(g))).`                `(OPS9)`

The membership condition in `(OPS9)` has the exact pullback

`q(g) in q(H)`
` iff g in H ker(q).`                                        `(OPS10)`

Hence the finite model negates the lamps on `H ker(q)`, not merely those on
`H`.  The multiplier `P_q` commutes with `q(H)`, so all subgroup covariance
relations remain exact; `(OPS10)` is the only membership error.

**Lemma 1 (exact normalized-HS error).**  Compare the desired conjugation
rule `(OPS5)` with the finite rule `(OPS9)` on the generator `delta_g`.
Their normalized Hilbert--Schmidt discrepancy is zero when the two
membership indicators agree and is two when they disagree.  Thus its square
is

`4 1_(g in H ker(q) setminus H).`                            `(OPS11)`

**Proof.**  Both sides are the same unitary lamp translation multiplied by
scalars in `{1,-1}`.  Distinct signs differ by twice a unitary, whose
normalized Hilbert--Schmidt norm is two.  Equation `(OPS10)` finishes the
proof.  End proof.

## 4. Direct sums do not weaken the obstruction

At level `n`, allow finitely many quotients `q_(n,j):K->Q_(n,j)` with
dimension weights `lambda_(n,j)>=0`, where

`sum_j lambda_(n,j)=1`.                                    `(OPS12)`

This includes arbitrary finite direct sums and multiplicities of the
quotient parity blocks.  Let `E_n(g)^2` be the squared normalized
Hilbert--Schmidt error of the resulting direct sum on the lamp `delta_g`.
By orthogonality of direct sums and Lemma 1,

`E_n(g)^2`
` =4 sum_j lambda_(n,j) 1_(g in H ker(q_(n,j)) setminus H).` `(OPS13)`

In particular, `E_n(h)=0` for every `h in H`, while for `g notin H`,

`E_n(g)^2=4 Prob_n[g in H ker(q)].`                          `(OPS14)`

**Theorem 2 (weighted finite-quotient parity criterion).**  The following
are equivalent.

1. There are weighted finite-quotient parity models for which
   `E_n(g)->0` for every fixed `g in K`.
2. There is a sequence of finite quotients `q_n` such that

   `intersection_n H ker(q_n)=H`                            `(OPS15)`

   after replacing the sequence by its successive product quotients.
3. `H` is closed in the profinite topology of `K`.

### Proof

`(2)` and `(3)` are the standard finite-quotient formulation of subgroup
separability.  If `(2)` holds, use a single quotient block at each level.
Then `(OPS10)--(OPS11)` give eventual exactness on every fixed finite subset,
so `(1)` holds.

Suppose `(1)` holds.  Enumerate

`K setminus H={g_1,g_2,...}`.                               `(OPS16)`

For fixed `m`, equation `(OPS14)` and the union bound give

`Prob_n[there exists i<=m with g_i in H ker(q)]`
` <=sum_(i=1)^m E_n(g_i)^2/4 ->0.`                         `(OPS17)`

For sufficiently large `n`, the probability in `(OPS17)` is less than one.
Therefore one quotient occurring with positive weight excludes all
`g_1,...,g_m` from `H ker(q)`.  Choose such a quotient `q_m`.  Replacing
`q_m` by the product `q_1 times ... times q_m` makes the kernels decreasing
without losing any previous separation.  The resulting sequence satisfies
`(OPS15)`.  Hence `(1)` implies `(2)`.  End proof.

The proof shows that randomization or highly uneven multiplicities buy
nothing: vanishing normalized-HS error can be diagonalized to a deterministic
profinite separating tower.

## 5. Consequence for a nonsofic Schreier action

If `(OPS15)` holds, the transitive finite `K`-sets

`K/(H ker(q_n))`                                           `(OPS18)`

converge locally to the Schreier action `K curvearrowright K/H`.  Indeed,
for every finite set of words, `(OPS15)` eventually decides exactly which
of them belong to `H`; after taking successive product quotients the same is
true at every translated rooted ball.  Thus the coset action is residually
finite as an action and in particular sofic.

**Corollary 3 (nonsofic-orbit no-go).**  If the Schreier action
`K curvearrowright K/H` is nonsofic, no finite-quotient parity construction
of the form `(OPS8)`, including arbitrary dimension-weighted direct sums,
can implement the one-orbit clutching with vanishing normalized-Hilbert--
Schmidt error on all fixed lamps.

This applies to the distinguished nonsofic orbit in the explicit
Kun--Thom-based FALSE construction.  It explains why the exact infinite
coinduced parity model does not admit the obvious finite quotient
approximation even though each finite block separately satisfies every
algebraic parity and subgroup-covariance relation.

## 6. Relation to the three Schreier moments

The primitive scalar Weyl construction fails for a different but compatible
reason: `FALSE_PROPERTY_T_PRIMITIVE_HOLONOMY_MOMENT_NO_GO.md` proves that
property `(T)` forces one centered scalar transition moment to be linear in
the clock order.  The present theorem shows that replacing that scalar clock
by the characteristic parity of one finite quotient orbit also fails: it
would require profinite separation of the very subgroup whose coset action
is nonsofic.

The two failures isolate the surviving target.  A successful finite model
cannot encode the marked orbit by either

1. one primitive scalar transition coordinate, or
2. one subset `q(H)` of a finite quotient.

It must distribute the clutching through internal matrix directions while
keeping the full fixed group action coherent.  This is precisely the
base-dependent paired Fourier/Frobenius problem stated in
`FALSE_LONG_FROBENIUS_ELEMENTARY_COMPRESSOR.md`.
