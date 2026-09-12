# A modular transfer-holonomy certificate for a hyperlinear nonsofic image

Date: 2026-08-11

## 1. Purpose

Uniform averaging over a deck-invariant discriminant subgroup cannot make
the mean carry energy microscopic; this is the orbit obstruction in
`FALSE_REGULAR_COVER_MEAN_ENERGY_NO_GO.md`.  An individual high-order class
can nevertheless be microscopic.  This note gives an exact low-dimensional
certificate for such a class.

The certificate is a single modular column-space equation

`A_X a=Jv mod q`,                                                     `(THC1)`

together with one modular word evaluation.  It is the marked-word version
of the transfer-divisibility criterion `(ICD40)` and requires neither a
basis of the full cycle lattice nor a closest-vector computation.

## 2. Presentation-cover setup

Fix a finite presentation

`H=<S | R>`                                                          `(THC2)`

and a word `1!=w in Rad_sof(H)`.  Let `P` be its presentation complex, and
let `P_X->P` be a connected regular finite cover with deck group `T` and
degree `n`.  Since every homomorphism from `H` to the finite group `T` kills
`w`, every lift of the `w`-path is a loop.

Let

`A_X:C^1(P_X,Z)->C^2(P_X,Z)`                                        `(THC3)`

be the cellular coboundary matrix.  Write `r=|R|`, so the target of `A_X`
has `m=rn` coordinates.  Let

`A_1:C^1(P,Z)->C^2(P,Z)`,
`K_1=ker(A_1^*)`, `K_X=ker(A_X^*)`,                                  `(THC4)`

where the kernels are taken in the integral cell lattices.  The constant
lift and coordinate sum are

`J:C^2(P,Z)->C^2(P_X,Z)`,
`S:C^2(P_X,Z)->C^2(P,Z)`.                                           `(THC5)`

They satisfy `J(K_1)<=K_X`, `S(K_X)<=K_1`, and `SJ=n id`.

For a vertex `x in X`, let

`b_(w,x) in C_1(P_X,Z)`                                              `(THC6)`

be the cellular chain of the lifted `w`-loop based at `x`.

## 3. The modular class and its exact holonomy

Fix `v in K_1`, an integer `q>1`, and suppose there is

`a in C^1(P_X,Z)`

such that

`A_X a=Jv mod q`.                                                    `(THC7)`

Equivalently, `Jv=A_Xa+qz` for an integral relator cochain `z`.

**Lemma 1 (invariant discriminant class).**  Equation `(THC7)` makes

`u=(1/q)Jv`                                                         `(THC8)`

an element of `K_X^#`.  If `v` is primitive, then `u+K_X` is nonzero.

**Proof.**  For `k in K_X`, pair `(THC7)` with `k`:

`<Jv,k>=<a,A_X^*k> mod q=0`.                                       `(THC9)`

Thus `<u,k>` is integral, proving `u in K_X^#`.  If `u` were integral,
then every coordinate of the primitive vector `v` would be divisible by
`q`, impossible.  End proof.

The same calculation is the modular-image implication `(ICD40)=>`
`(ICD33)`, but the cochain `a` retains additional information: its integral
around the radical loop.

Define

`h_x=<a,b_(w,x)> mod q in Z/qZ`.                                    `(THC10)`

**Lemma 2 (deck-independent radical holonomy).**  The value `h_x` is
independent of `x`.

**Proof.**  Let `g in T`.  Equation `(THC7)` and deck invariance of `Jv`
give

`A_X(ga-a)=0 mod q`.                                                 `(THC11)`

Hence exponentiating the phase table `(ga-a)/q` produces an exact monomial
representation of `H` over the given permutation action.  Its image is a
finitely generated linear group, hence residually finite and sofic.  Since
`w in Rad_sof(H)`, this exact representation kills `w`.  Equivariance of
word evaluation now gives

`<a,b_(w,gx)>-<a,b_(w,x)>=0 mod q`.                                 `(THC12)`

Deck transitivity proves the claim.  End proof.

The same radical argument shows that `h_x` is independent of the chosen
solution `a` of `(THC7)`.  Indeed the difference of two solutions lies in
`ker(A_X mod q)` and therefore exponentiates to an exact finite-dimensional
monomial representation, which kills `w`.  Consequently there is a
well-defined homomorphism

`Hol_(w,X,q): J(K_1) intersect im(A_X mod q) -> Z/qZ`,
`Hol_(w,X,q)(Jv)=<a,b_(w,x)> mod q`.                                 `(THC12a)`

This is the finite **radical transgression**.  The FALSE certificate asks
whether it can take a macroscopically nonzero value on a base cycle `v`
whose norm is small compared with `q`.

There is an equivalent filling formula which makes independence of all
choices transparent.  By the finite-index radical theorem in
`FALSE_RADICAL_FILLING_DISCRIMINANT.md`, choose an integral filling

`A_X^* z_(w,x)=b_(w,x)`.                                            `(THC13)`

Pairing `(THC7)` with this filling gives

`h_x=<a,b_(w,x)>`
`   =<A_Xa,z_(w,x)>`
`   =<Jv,z_(w,x)>`
`   =<v,Sz_(w,x)> mod q`.                                           `(THC14)`

Changing the filling adds an element of `K_X`, and `(THC9)` makes the last
value unchanged modulo `q`.  Thus the holonomy is computed entirely in the
fixed-rank base group `K_1`: transfer one integral filling and pair with
`v`.

## 4. The phase microstate

Put

`x=-a/q in C^1(P_X,R)`.                                              `(THC15)`

Equation `(THC7)` gives

`A_Xx=z-(1/q)Jv`                                                     `(THC16)`

for an integral vector `z`.  Exponentiating the edge phases in `(THC15)`
and multiplying by the exact permutation chart gives a monomial map on the
generators of `H`.  Its normalized relator defect is bounded by

`2 pi ||Jv/q||_2/sqrt(rn)`
` =2 pi ||v||_2/(q sqrt(r))`.                                       `(THC17)`

The image of `w` is scalar on every vertex, by Lemma 2, and equals

`exp(-2 pi i h_x/q)`.                                               `(THC18)`

Consequently its normalized Hilbert--Schmidt displacement is exactly

`|exp(2 pi i h_x/q)-1|`.                                            `(THC19)`

The exact paired-carry interpretation is consistent with `(THC16)`: the
cycle representative is `u=Jv/q`, the glued range representative is
`z-u`, and translation by `z` gives

`delta(u+K_X)=dist(Jv/q,Z^(rn))`.                                   `(THC20)`

When the chosen entries of `v/q` lie in `[-1/2,1/2]`, this is exactly
`sqrt(n)||v||/q`; estimate `(THC17)` does not require that centering
assumption.

## 5. Complete FALSE criterion

**Theorem 3 (transfer-holonomy FALSE certificate).**  Suppose there are
regular finite covers `P_(X_j)->P`, integers `q_j>1`, primitive vectors
`v_j in K_1`, and cochains `a_j` satisfying

`A_(X_j)a_j=Jv_j mod q_j`.                                          `(THC21)`

Let

`h_j=<a_j,b_(w,x_j)> mod q_j`.                                      `(THC22)`

If

`||v_j||/q_j ->0`                                                   `(THC23)`

and

`liminf_j |exp(2 pi i h_j/q_j)-1|>0`,                              `(THC24)`

then a hyperlinear nonsofic group exists.

**Proof.**  Equations `(THC17)` and `(THC23)` make every fixed relator
defect tend to zero, so the monomial maps define a homomorphism from `H`
to a tracial matrix ultraproduct.  Equations `(THC19)` and `(THC24)` show
that its image retains the nontrivial element `w`.  The image is hyperlinear.
If it were sofic, the quotient homomorphism from `H` to that image would
kill `w in Rad_sof(H)`, a contradiction.  End proof.

The macroscopic condition `(THC24)` is sufficient but not necessary.
Tensor amplification turns a much smaller holonomy into a fixed
normalized-Hilbert--Schmidt displacement.  For a residue `h in Z/qZ`, put

`H_q(h)=dist(h,qZ) in [0,q/2]`,                                    `(THC24a)`

the absolute value of its centered integer representative.

**Theorem 3a (amplified transfer-holonomy certificate).**  Retain
`(THC21)--(THC22)`.  It is enough to assume

`H_(q_j)(h_j)/||v_j|| ->infinity`.                                `(THC24b)`

In particular, `h_j/q_j` is allowed to tend to zero.

**Proof.**  Let `chi_j` be the normalized character of the monomial
free-group representation constructed from `x_j=-a_j/q_j`, and put

`alpha_j=sum_(r in R)(1-Re chi_j(r))`,
`beta_j=1-Re chi_j(w)`.                                           `(THC24c)`

Equation `(THC16)` shows that the phase of relator `r` at every vertex is
`-v_(j,r)/q_j` modulo integers.  Hence

`alpha_j=sum_(r in R)(1-cos(2 pi v_(j,r)/q_j))`
`        <=2 pi^2 ||v_j||^2/q_j^2`.                               `(THC24d)`

Lemma 2 makes the word phase scalar, so

`beta_j=1-cos(2 pi h_j/q_j)`
`       >=8 H_(q_j)(h_j)^2/q_j^2`.                                `(THC24e)`

Here we used, for `dist(t,Z)<=1/2`,

`8 dist(t,Z)^2 <=1-cos(2 pi t)<=2 pi^2 dist(t,Z)^2`.               `(THC24f)`

Therefore

`beta_j/alpha_j`
` >=(4/pi^2) H_(q_j)(h_j)^2/||v_j||^2 ->infinity`.                 `(THC24g)`

The marked-discriminant divergence theorem in
`FALSE_MARKED_DISCRIMINANT_DIVERGENCE_CRITERION.md` now applies: after
conjugate doubling, either the word displacement is already macroscopic or
`ceil(1/beta_j)` tensor powers make it macroscopic while the total relator
defect still tends to zero.  The resulting hyperlinear image retains
`w in Rad_sof(H)` and is therefore nonsofic.  End proof.

Condition `(THC24b)` automatically implies `(THC23)`, since
`H_q(h)<=q/2`.  Its advantage over `(THC24)` is nevertheless strict: for
bounded nonzero `v_j`, holonomies such as `H_(q_j)(h_j)=sqrt(q_j)` satisfy
`(THC24b)` but have `h_j/q_j->0`.

For compatible moduli `q_j=p^j` and fixed `v`, even the growth assertion
can be removed: `FALSE_PADIC_RADICAL_TRANSGRESSION_CRITERION.md` proves
that it is enough for the compatible holonomies to define any element of
`Z_p minus Z`.

This criterion only needs `q_j` to dominate `||v_j||`; it does **not** need
the stronger instability scale

`q_j/sqrt(|X_j|)->infinity`                                         `(THC25)`

from `(ICD34)`.  The latter makes the phase table far from every exact
phase table.  For the group counterexample, vanishing relator error plus
the marked holonomy is enough.

## 6. Finite computation and the live target

For fixed `v` and `q`, all data are obtained from modular linear algebra:

1. solve the single system `A_Xa=Jv mod q`;
2. evaluate `a` on one lifted word chain `b_(w,x)`;
3. check whether its centered residue is large relative to `||v||`.

Equivalently, one may first compute the fixed-rank transfer subgroup

`M_X=S(K_X)<=K_1`.                                                   `(THC26)`

The largest admissible modulus for `v` is

`q_X(v)=gcd{<v,y>:y in M_X}`,                                       `(THC27)`

up to the saturation obstruction `(ICD56)`.  On saturated charts the
modular solution exists at the maximal modulus.  Formula `(THC14)` then
computes the marked holonomy without constructing a discriminant basis.

The exact remaining arithmetic question is therefore self-contained:

> Is there a finitely presented group `H`, a nontrivial
> `w in Rad_sof(H)`, and regular finite covers for which a virtually
> divisible base two-cycle has unbounded modulus `q_j`, while its modular
> line integral around `w`, in centered residue, grows faster than the norm
> of that base cycle?

A positive answer is the full FALSE proof by Theorem 3a.  A negative answer
would be a new integral holonomy rigidity theorem; it does not follow from
the uniform subgroup-mean no-go.

## 7. A necessary degree-holonomy congruence

The modular holonomy cannot be arbitrary.  Since `w` lies in the sofic
radical, it lies in `[H,H]`; choose once and for all a base integral filling

`A_1^* z_0=b_w`.                                                    `(THC28)`

Here `b_w` is the cellular one-chain of the word in the base presentation
complex.

**Proposition 4 (degree-holonomy congruence).**  Every solution of
`(THC21)` satisfies

`n h_x = n <v,z_0> mod q`.                                         `(THC29)`

Equivalently, with `g=gcd(n,q)`,

`h_x=<v,z_0> mod (q/g)`.                                           `(THC30)`

In particular, if `gcd(n,q)=1`, `q->infinity`, and `||v||` stays bounded,
then `(THC24)` is impossible.

**Proof.**  Sum the lifted word chains over all vertices.  Naturality gives

`sum_(x in X)b_(w,x)=Jb_w=A_X^*Jz_0`.                              `(THC31)`

Lemma 2 says every summand has the same evaluation `h_x`.  Therefore

`n h_x=<a,Jb_w>`
`       =<A_Xa,Jz_0>`
`       =<Jv,Jz_0>`
`       =n<v,z_0> mod q`,                                           `(THC32)`

where `(THC21)` is used in the third equality and `J` multiplies inner
products by the cover degree in the fourth.  This proves `(THC29)`.
Elementary cancellation of the common gcd gives `(THC30)`.  In the coprime
case, the centered residue of `h_x` equals the fixed integer `<v,z_0>`;
division by `q` tends to zero.  End proof.

Proposition 5 of `INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md` independently
gives

`q divides n||v||^2`.                                                `(THC33)`

Thus an unbounded-modulus positive example must deliberately exploit the
common prime-power part of the cover degree and the divisibility modulus.
Searching coprime moduli, or moduli supported away from the cover degree,
cannot produce the required phase.
