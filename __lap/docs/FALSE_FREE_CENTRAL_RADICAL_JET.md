# A free central radical jet and its one-Weyl-pair endpoint

Date: 2026-08-11

## 1. Purpose

The integral lamp group in `FALSE_INTEGRAL_CYCLIC_RADICAL_MODULE.md`
produces an infinite central radical element, but its finite-dimensional
endpoint asks that all conjugates of one lamp approximately commute.  That
commutativity is not needed for the radical argument.  This note removes it.

Starting from one infinite-order element in a full sofic radical, one may
freely adjoin a letter `t` and impose only that the commutator `[s,t]` be
central.  The resulting group still maps onto the integral lamp group, so
the central commutator has infinite order.  Its small-phase endpoint is a
single approximate Weyl relation.

## 2. The free central jet

Let `G` be a countable group and let `s in G` have infinite order.  Use the
commutator convention

`[a,b]=a b a^(-1) b^(-1)`.                            `(FCJ1)`

Define

`J(G,s)=<G,t | [x,[s,t]]=1 for every x in G union {t}>`, `(FCJ2)`

and write

`z=[s,t] in J(G,s)`.                                  `(FCJ3)`

Thus `(FCJ2)` says exactly that `z` is central.  If `X` generates `G`, it
is enough to impose `[x,z]=1` for `x in X union {t}`.  In particular,
finite generation, and finite presentation, pass from `G` to `J(G,s)`.

**Theorem 1 (free central radical jet).**  The element `z` has infinite
order.  If

`s in Rad_sof(G)`,                                      `(FCJ4)`

then

`1 != z in Rad_sof(J(G,s))`.                          `(FCJ5)`

Consequently `J(G,s)` is nonsofic.

**Proof.**  Let

`A_Z=Z[G]/I(s-1)`, `E_Z=A_Z semidirect G`             `(FCJ6)`

be the integral cyclic radical group from
`FALSE_INTEGRAL_CYCLIC_RADICAL_MODULE.md`.  If `v` is the class of `1`,
that note proves that

`z_Z=[s,v]`                                            `(FCJ7)`

is central and has infinite order, and that `G` together with `v`
generates `E_Z`.  Hence the map from the free product `G*<t>` which is the
identity on `G` and sends `t` to `v` factors through a surjection

`J(G,s) -> E_Z`.                                      `(FCJ8)`

It sends `z` to `z_Z`, so `z` has infinite order.

Now let `Phi:J(G,s)->S` be a homomorphism to a sofic group.  Its
restriction to `G` kills `s` by `(FCJ4)`.  Therefore

`Phi(z)=[Phi(s),Phi(t)]=1`.                            `(FCJ9)`

This is `(FCJ5)`.  End proof.

The group has an equivalent HNN description.  Introduce `z` first and put

`B=G times <z>`.                                      `(FCJ10)`

Inside `B`, the subgroup `<s,z>` is isomorphic to `Z^2`.  Then

`J(G,s)=<B,t | t^(-1)s t=z s, t^(-1)z t=z>`.         `(FCJ11)`

The sign of the power of `z` changes if the opposite commutator convention
is used.  Thus `J(G,s)` is the HNN extension which shears one primitive
direction of the edge `Z^2`.  It is not a central HNN extension: the edge
automorphism is the nontrivial unipotent shear.

For the banked Kun--Thom symmetric double `D`, take any infinite-order
`s in Rad_sof(D)` supplied by the fold-word construction.  Theorem 1 gives
an explicit finitely generated nonsofic group `J(D,s)` with a central
infinite cyclic subgroup in its full sofic radical.  When the chosen
presentation of `D` is finite, `(FCJ2)` is finite as well.

## 3. The one-Weyl-pair criterion

All norms below are normalized Hilbert--Schmidt norms.  For unitaries
`S,T`, write

`W(S,T)=S T S^* T^*`.                                 `(FCJ12)`

**Theorem 2 (one-Weyl-pair endpoint).**  Let `epsilon_n>0` tend to zero.
Suppose there are dimensions `d_n`, maps

`U_n:G->U(d_n)`                                       `(FCJ13)`

and unitaries `T_n in U(d_n)` such that, for every fixed `g,h in G`,

`||U_n(g)U_n(h)-U_n(gh)||_2=o(epsilon_n)`,            `(FCJ14)`

and

`||W(U_n(s),T_n)-exp(i epsilon_n)1||_2`
`  =o(epsilon_n)`.                                    `(FCJ15)`

If `(FCJ4)` holds, then a hyperlinear nonsofic group exists.

**Proof.**  Put

`Z_n=W(U_n(s),T_n)`, `lambda_n=exp(i epsilon_n)`.      `(FCJ16)`

Equation `(FCJ15)` automatically makes the defining centrality relations
first-order small.  Indeed, for every unitary `V`,

`||[V,Z_n]-1||_2`
` =||V Z_n V^*-Z_n||_2`
` <=2||Z_n-lambda_n 1||_2=o(epsilon_n)`.              `(FCJ17)`

This applies to `V=T_n` and to every fixed `U_n(g)`.

Choose once and for all a word in `G*<t>` representing each element of
`J(G,s)`, and evaluate it using `U_n` and `T_n`.  This gives maps

`Phi_n:J(G,s)->U(d_n)`.                               `(FCJ18)`

For fixed `a,b in J(G,s)`, a derivation from the chosen word for `a` times
the chosen word for `b` to the chosen word for `ab` uses only finitely many
instances of: multiplication in `G`, the relation `z=[s,t]`, and the
centrality relations for `z`.  Equations `(FCJ14)`, `(FCJ16)`, and
`(FCJ17)`, followed by a finite unitary telescoping sum, therefore give

`||Phi_n(a)Phi_n(b)-Phi_n(ab)||_2=o(epsilon_n)`.       `(FCJ19)`

Moreover

`||Phi_n(z)-lambda_n 1||_2=o(epsilon_n)`.             `(FCJ20)`

Fix `theta in (0,2 pi)` and let

`m_n=floor(theta/epsilon_n)`.                         `(FCJ21)`

Take the `m_n`-fold tensor power of `(FCJ18)`.  The normalized-Hilbert--
Schmidt tensor telescoping inequality and `(FCJ19)` give multiplicative
defect

`m_n o(epsilon_n)=o(1)`.                              `(FCJ22)`

On the central element, `(FCJ20)` gives

`Phi_n(z)^(tensor m_n) -> exp(i theta)1`              `(FCJ23)`

in normalized Hilbert--Schmidt norm.  Hence these maps define a homomorphism
from `J(G,s)` to a tracial matrix ultraproduct whose image `L` retains `z`.
The group `L` is hyperlinear.  If it were sofic, the quotient homomorphism
`J(G,s)->L` would kill `z` by Theorem 1, contradicting `(FCJ23)`.  End
proof.

Compared with the integral lamp criterion, Theorem 2 has no analogue of
the commuting-conjugates condition `(ICR27)`.  The scalar approximation in
`(FCJ15)` already makes the commutator asymptotically central by `(FCJ17)`.

## 4. The Weyl relation already forces trace visibility

The simplification in Theorem 2 is algebraically real, but the remaining
analytic hypothesis must not be understated.  At first order, a scalar
Weyl relation already performs the entire norm-to-trace amplification.

**Proposition 3 (first-order Weyl visibility).**  Let `epsilon_n->0`, let
`S_n,T_n` be finite-dimensional unitaries, and suppose

`||W(S_n,T_n)-exp(i epsilon_n)1||_2=o(epsilon_n)`.     `(FCJ23a)`

Then

`tr(S_n^k)->0`                                        `(FCJ23b)`

for every fixed nonzero integer `k`.  In particular,

`||S_n-1||_2^2 ->2`.                                  `(FCJ23c)`

**Proof.**  Put `lambda_n=exp(i epsilon_n)` and let the error in
`(FCJ23a)` be `r_n=o(epsilon_n)`.  Multiplying

`S_n T_n S_n^* T_n^*-lambda_n 1`

on the right by `T_n S_n` gives

`||S_n T_n-lambda_n T_n S_n||_2=r_n`.                `(FCJ23d)`

Consequently

`||T_n S_n T_n^*-lambda_n^(-1)S_n||_2=r_n`.          `(FCJ23e)`

Taking normalized traces and using conjugation invariance yields

`|1-lambda_n^(-1)| |tr(S_n)|<=r_n`.                  `(FCJ23f)`

Since `|1-lambda_n|` is asymptotic to `epsilon_n`, the right ratio tends
to zero.  For a fixed positive `k`, telescoping `(FCJ23e)` gives

`||T_n S_n^k T_n^*-lambda_n^(-k)S_n^k||_2<=k r_n`.   `(FCJ23g)`

The same trace argument, with
`|1-lambda_n^(-k)|` asymptotic to `k epsilon_n`, proves `(FCJ23b)`.
Negative `k` follows by adjoints.  Finally

`||S_n-1||_2^2=2-2 Re tr(S_n)`,                       `(FCJ23h)`

which proves `(FCJ23c)`.  End proof.

Thus the empirical spectral measures of `S_n` converge weakly to Haar
measure on the circle.  Applied to `(FCJ14)--(FCJ15)`, Proposition 3 says
that the maps `U_n` alone already define a tracial-ultraproduct image of
`G` which retains `s`.  If `s in Rad_sof(G)`, that image is hyperlinear and
nonsofic.  No tensor power and no passage to `J(G,s)` is then necessary.

This is an important calibration:

* the free jet removes the commuting-lamp algebra from the presentation;
* but constructing its `o(epsilon)` Weyl pair is already a complete
  norm-to-trace conversion for the original radical element.

Accordingly, Theorem 2 is best viewed as a sharp spectral reformulation of
the FALSE endpoint, not as a proof that the analytic gate has become easy.

## 5. Clock calibration

The endpoint has a particularly transparent finite-dimensional form.  Let

`C_m=diag(1,omega_m,...,omega_m^(m-1))`,
`S_m e_j=e_(j+1 mod m)`, `omega_m=exp(2 pi i/m)`.      `(FCJ24)`

Up to orientation,

`W(C_m,S_m)=omega_m 1`.                               `(FCJ25)`

Thus it would suffice to construct maps `U_m:G->U(d_m)` and unitaries
`T_m` with

`group defect=o(1/m)`,
`W(U_m(s),T_m)=exp(2 pi i/m)1+o(1/m)`.                `(FCJ26)`

The determinant obstruction is exactly compatible with this scale: an
exact scalar commutator in dimension `d` must be a `d`-th root of unity.
The live issue is not finite-dimensional Weyl quantization; it is putting
the prescribed clock into an `o(1/m)` almost-representation of the whole
group `G`.

Honest finite-dimensional representations cannot do this when `G` is
finitely generated and `s` lies in its full sofic radical.  Their images
are finitely generated linear groups, hence residually finite and sofic, so
they kill `s`.  The vertex model in `(FCJ26)` must therefore be genuinely
nonliftable, just as in the previous cyclic-shear calibrations.

## 6. An exact Mackey carousel

The one-Weyl formulation also identifies an exact infinite-dimensional
source for the clock.  The following statement is useful independently of
the approximation problem.

Assume now that `C=<s>` is malnormal in `G`.  For `theta in R`, put

`chi_theta(s^k)=exp(i k theta)`,
`pi_theta=Ind_C^G(chi_theta)`.                         `(FCJ27)`

**Lemma 4 (cyclic-edge spectral transport).**  For every `theta,alpha`,

`pi_(theta+alpha)|_C`
`  is unitarily equivalent to chi_alpha tensor pi_theta|_C`. `(FCJ28)`

**Proof.**  Mackey restriction decomposes `pi_theta|_C` over
`C\G/C`.  The identity double coset contributes `chi_theta`.  By
malnormality, every other intersection `C intersection g C g^(-1)` is
trivial, so every other summand is a copy of the regular representation of
`C`.  Twisting a regular representation by `chi_alpha` gives a unitarily
equivalent regular representation, while the identity summand becomes
`chi_(theta+alpha)`.  This is `(FCJ28)`.  End proof.

Fix `m>=2`, set `alpha=2 pi/m`, and take the direct sum of

`pi_0, pi_alpha, ..., pi_((m-1)alpha)`.                `(FCJ29)`

Lemma 4 supplies unitary edge intertwiners between consecutive summands;
the final one closes because `pi_(2 pi)=pi_0`.  Choosing their orientations
consistently gives a unitary `T` which cyclically permutes the summands and,
for

`U(g)=directSum_(j=0)^(m-1) pi_(j alpha)(g)`,          `(FCJ30)`

satisfies

`W(U(s),T)=exp(i alpha)1`.                             `(FCJ31)`

Consequently `J(G,s)` has exact infinite-dimensional representations in
which `z` is every prescribed root of unity.  Since `C` is amenable, every
`pi_theta` is weakly contained in the left regular representation of `G`.

This carousel proves that the Weyl relation is compatible with the whole
group at the representation-theoretic level.  It does not supply finite
tracial approximations.  Turning `(FCJ29)--(FCJ31)` into matrices with
error `o(1/m)` is the remaining analytic gate.  Ordinary strong-ideal
homotopy lifting does not give that rate, and projectional cuts would force
coamenability of the cyclic subgroup, as explained in
`FALSE_INDUCED_CHARACTER_HOMOTOPY.md`.

## 7. Updated FALSE target

The integral abelian radical jet required two simultaneous phenomena:

1. an `o(epsilon)` Weyl relation for `s` and one lamp;
2. `o(epsilon)` commutation of all relevant conjugate lamps.

The free central radical jet proves that item 2 is dispensable.  A complete
FALSE proof follows from the self-contained question:

> Does the banked weak-MF Kun--Thom double admit normalized-Hilbert--Schmidt
> almost-representations and one unitary `T_n` satisfying `(FCJ14)--(FCJ15)`
> for some `epsilon_n->0`?

By Proposition 3, a positive answer already makes the spectral law of
`U_n(s)` Haar and therefore solves FALSE directly at the level of `G`.
The remaining obstruction is a single first-order clock insertion into one
nonliftable vertex model, but that insertion is itself the full
norm-to-trace breakthrough.  No Cartan, commuting-lamp, or global coinduced
coordinate approximation is required to state it.
