# Radical holonomy as a paired transferred-filling class

Date: 2026-08-11

## 1. Outcome

The modular radical holonomy of
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md` can be computed without solving the
modular phase equation.  Fix an integral filling of the radical word on the
base.  Transfer any integral filling of one lifted radical loop back to the
base and subtract the fixed filling.  This produces a class

`kappa_(w,X) in K_1/S(K_X)`.                                     `(TFP1)`

For every transferable base cycle `v` and modulus `q`, the nonordinary part
of the holonomy is exactly the lattice pairing

`Hol_(w,X,q)(Jv)-<v,z_0>=<v,kappa_(w,X)> mod q`.                  `(TFP2)`

The right side is well-defined on the quotient because modular transfer
forces `q` to divide all pairings of `v` with `S(K_X)`.  On full-transfer
stages this is a bilinear paired-quotient formula.  It identifies the
degree-torsion character from
`FALSE_FULL_TRANSFER_TORSION_NORMAL_FORM.md` as the rescaled Gram pairing
with one finite quotient-lattice class.

Thus the amplified FALSE numerator is no longer an opaque modular line
integral: it is the marked pairing of a canonical relative filling class in
the fixed-rank transfer quotient.

## 2. The relative transferred-filling class

Let `P_X->P` be a connected regular presentation cover with deck group `T`.
Use

`K_X=ker(A_X^*)`,  `K_1=ker(A_1^*)`,
`M_X=S(K_X)<=K_1`,                                               `(TFP3)`

where `S` is coordinate sum, equivalently cellular pushforward.  Fix

`1!=w in Rad_sof(H)`                                             `(TFP4)`

and one integral base filling

`A_1^*z_0=b_w`.                                                  `(TFP5)`

For a vertex `x in X`, choose an integral lifted filling

`A_X^*z_(w,x)=b_(w,x)`.                                          `(TFP6)`

Such fillings exist by the finite-index radical filling theorem already
used in `(THC13)`.

Cellular naturality gives

`A_1^*S z_(w,x)=S A_X^*z_(w,x)=S b_(w,x)=b_w`.                   `(TFP7)`

Consequently

`kappa_tilde_(w,X,x)=S z_(w,x)-z_0 in K_1`.                      `(TFP8)`

**Proposition 1 (well-defined filling-transfer class).**  The residue class

`kappa_(w,X)=[kappa_tilde_(w,X,x)] in K_1/M_X`                   `(TFP9)`

is independent of the lifted filling and of the base vertex `x`.

**Proof.**  Two fillings of the same lifted loop differ by an element of
`K_X`, so their coordinate sums differ by an element of `M_X`.

For vertices `x,y`, choose a deck transformation `t in T` with `tx=y`.
If `z_(w,x)` fills the loop at `x`, then `t z_(w,x)` fills the loop at `y`.
Coordinate sum is deck invariant, so

`S(t z_(w,x))=S z_(w,x)`.                                       `(TFP10)`

The preceding filling-independence handles any other choice at `y`.  End
proof.

The class is relative to the fixed base filling `z_0`.  Replacing `z_0` by
`z_0+k_0`, with `k_0 in K_1`, translates `kappa` by `-[k_0]`; all formulas
below remain unchanged because the ordinary filling functional changes by
the opposite pairing.

The transfer quotient is finite and killed by the cover degree `n`, since

`nK_1=SJ(K_1)<=S(K_X)=M_X`.                                      `(TFP11)`

Thus `kappa_(w,X)` is a finite degree-torsion class before any modulus is
chosen.

## 3. Exact paired holonomy formula

Let `v in K_1`, let `q>1`, and suppose the modular transfer equation is
solvable:

`A_Xa=Jv mod q`.                                                  `(TFP12)`

As in `(THC9)`, pairing `(TFP12)` with `k in K_X` gives

`<v,Sk>=<Jv,k>=0 mod q`.                                         `(TFP13)`

Therefore the pairing

`<v,[u]>_q=<v,u> mod q`,  `[u] in K_1/M_X`,                      `(TFP14)`

is well-defined for this particular transferable pair `(v,q)`.

**Theorem 2 (paired transferred-filling formula).**  Under `(TFP12)`,

`Hol_(w,X,q)(Jv)`
` =<v,z_0>+<v,kappa_(w,X)>_q mod q`.                              `(TFP15)`

**Proof.**  Pair the modular solution with an integral lifted filling:

`Hol(Jv)=<a,b_(w,x)>`
`       =<A_Xa,z_(w,x)>`
`       =<Jv,z_(w,x)> mod q`
`       =<v,Sz_(w,x)> mod q`.                                    `(TFP16)`

Insert `Sz_(w,x)=z_0+kappa_tilde_(w,X,x)` from `(TFP8)`.  Equation
`(TFP13)` makes the second pairing independent of the representative of
`kappa` modulo `M_X`, proving `(TFP15)`.  End proof.

Formula `(TFP15)` also gives a conceptual proof of the degree congruence.
Since `n kappa_tilde in M_X` by `(TFP11)`,

`n(Hol(Jv)-<v,z_0>)=0 mod q`.                                    `(TFP17)`

## 4. Full-transfer paired quotient

Assume now that the whole base lattice transfers modulo `q`:

`J(K_1)<=im(A_X mod q)`.                                         `(TFP18)`

Then `(TFP13)` holds for every `v in K_1`, so

`<K_1,M_X> subset qZ`.                                           `(TFP19)`

Hence there is a well-defined homomorphism

`beta_(X,q):K_1/M_X->Hom(K_1,Z/qZ)`,
`beta_(X,q)([u])(v)=<v,u> mod q`.                                 `(TFP20)`

Its kernel and image are explicit:

`ker(beta_(X,q))=(qK_1^# intersect K_1)/M_X`,                    `(TFP21)`

`im(beta_(X,q))` is isomorphic to
`K_1/(qK_1^# intersect K_1)`.                                    `(TFP22)`

Here `K_1^#` is the dual lattice in `K_1 tensor R`.  Inclusion of `M_X` in
the numerator of `(TFP21)` is exactly `(TFP19)`.

**Proof.**  Well-definedness is `(TFP19)`.  The character associated to
`u in K_1` vanishes precisely when `<K_1,u> subset qZ`, equivalently when
`u in qK_1^# intersect K_1`.  The first isomorphism theorem gives
`(TFP21)--(TFP22)`.  End proof.

In this notation Theorem 2 becomes the identity of characters

`Hol_(w,X,q) compose J`
` =phi+beta_(X,q)(kappa_(w,X))`,                                  `(TFP23)`

where `phi(v)=<v,z_0> mod q`.

This is the promised paired-discriminant geometry: the marked nonlinear
holonomy is the image of one transfer-quotient filling class under the
mod-`q` Gram pairing.

## 5. Relation to the degree-torsion character

Put

`g=gcd(n,q)`,  `e=q/g`.                                           `(TFP24)`

By Proposition 1 of `FALSE_FULL_TRANSFER_TORSION_NORMAL_FORM.md`, full
transfer implies that `e` divides every Gram pairing on `K_1`.  Therefore

`psi_(w,X,q)(v)`
` =<v,kappa_tilde_(w,X)>/e mod g`                                 `(TFP25)`

is well-defined, independent of the representative modulo `M_X`, and is
exactly the unique character in `(FTN13)`.

Indeed, representative independence follows from `(TFP19)`: changing
`kappa_tilde` by `m in M_X` changes the integer quotient in `(TFP25)` by a
multiple of `q/e=g`.  Formula `(TFP15)` gives

`Hol(Jv)=<v,z_0>+e psi_(w,X,q)(v) mod q`.                         `(TFP26)`

Thus the apparently arbitrary character `psi:K_1->Z/gZ` lies in the image
of the rescaled Gram map and is marked by the single class
`kappa_(w,X)`.

## 6. Integral matrix formula

Choose an integral basis `v_1,...,v_k` of `K_1`.  Let

`G=(<v_i,v_j>)_(i,j)`                                            `(TFP27)`

be its Gram matrix, let `m_X in Z^k` be the coordinate vector of any
representative `kappa_tilde_(w,X)`, and put

`f_i=<v_i,z_0>`.                                                  `(TFP28)`

Then the entire basis-holonomy vector is

`h=f+Gm_X mod q`.                                                 `(TFP29)`

If full transfer holds, changing `m_X` by the coordinate lattice of `M_X`
does not change `Gm_X mod q`.  Furthermore `G/e` is integral and the
degree-torsion vector is

`t=(G/e)m_X mod g`.                                               `(TFP30)`

Combining `(TFP29)` with Theorems 1--2 of
`FALSE_BASE_HOLONOMY_DUAL_NORM.md` gives an exact finite formula for the
optimal amplified slope.  In particular, if the centered vector

`center_q(f+Gm_X)`                                               `(TFP31)`

is unbounded along full-transfer stages, then a hyperlinear nonsofic group
exists.

This computation needs an integral kernel basis only to determine
`M_X=S(K_X)` and one integral lifted filling to determine `m_X`.  It needs
no modular phase solution, no full discriminant basis, and no optimization
over base cycles.

## 7. Bounded marked torsion versus bounded quotient exponent

The transfer quotient is always killed by the cover degree, but in useful
families it may be killed by a fixed integer.  Contrary to a possible first
impression, such bounded torsion does not make holonomy small.  A nonzero
element of bounded order in `Z/qZ` has magnitude proportional to `q`.

**Theorem 3 (persistent bounded torsion proves FALSE).**  Fix a primitive
`v in K_1`.  Suppose there are regular covers `X_j`, moduli `q_j->infinity`,
and modular transfers

`A_(X_j)a_j=Jv mod q_j`.                                          `(TFP32)`

Suppose one fixed integer `E>=2` satisfies

`E kappa_(w,X_j)=0 in K_1/M_(X_j)`                               `(TFP33)`

for every `j`.  If the paired residues

`alpha_j=<v,kappa_(w,X_j)>_(q_j) in Z/q_jZ`                       `(TFP34)`

are nonzero for infinitely many `j`, then a hyperlinear nonsofic group
exists.

**Proof.**  Pass to the subsequence on which `alpha_j!=0`.  Transferability
of `v` makes the pairing `(TFP34)` well-defined.  Equation `(TFP33)` shows
that the additive order `d_j` of `alpha_j` divides `E`, so

`2<=d_j<=E`.                                                      `(TFP35)`

A nonzero element of order `d_j` in `Z/q_jZ` is a multiple of
`q_j/d_j` by a unit modulo `d_j`.  Its centered size therefore satisfies

`H_(q_j)(alpha_j)>=q_j/d_j>=q_j/E`.                               `(TFP36)`

Put `f=<v,z_0>`, which is fixed.  The paired formula `(TFP15)` and the
`1`-Lipschitz property of distance to `q_j Z` give

`H_(q_j)(Hol(Jv))>=H_(q_j)(alpha_j)-|f|`
`                    >=q_j/E-|f| ->infinity`.                    `(TFP37)`

Since `v` is fixed, Theorem 3a of
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md` applies.  End proof.

It is essential that `(TFP33)` only bounds the order of the **marked class**.
If the entire transfer quotient has uniformly bounded exponent, the
conclusion is instead a TRUE-side no-go.  More precisely, suppose

`E K_1<=M_(X_j)`.                                                 `(TFP38)`

For fixed nonzero `v`, put

`g(v)=gcd{<v,u>:u in K_1}>0`.                                    `(TFP39)`

Transferability modulo `q_j` gives `q_j divides <v,M_(X_j)>` by `(TFP13)`.
Applying this to `Eu in M_(X_j)` for every `u in K_1` yields

`q_j divides E g(v)`.                                             `(TFP40)`

Thus the transferable moduli are uniformly bounded.  By `(ICD81)--(ICD83)`
in `INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md`, `(TFP38)` holds for every
finite cover if `H_2(H,Z)` has finite exponent `E`.  Finite-exponent second
homology therefore closes the fixed-cycle modular-transfer route rather
than furnishing a bounded-torsion example.

Theorem 3 remains nonvacuous only when the individual classes
`kappa_(w,X_j)` have bounded order while the exponents of the ambient
quotients `K_1/M_(X_j)` grow.  Other quotient directions can then support
unbounded transfer moduli even though the marked direction stays bounded.

## 8. What remains

The FALSE construction problem on full-transfer charts is now exact:

1. compute the finite transfer quotient `K_1/M_X`;
2. locate the relative radical filling class `kappa_(w,X)` in it;
3. impose a modulus `q` for which `<K_1,M_X> subset qZ` and modular-image
   saturation holds;
4. make the centered Gram pairing `(TFP31)` unbounded.

The class `kappa_(w,X)` can have growing order because the quotient is only
killed by the cover degree.  Theorem 3 shows that its own order need not
grow, provided the ambient quotient exponent does.  If the ambient exponent
is uniformly bounded, `(TFP40)` closes the route.  This note does not prove
that a detectable class persists in the growing-exponent case.  It proves
that this one paired quotient-lattice class is the entire nonlinear
integral numerator.  Any TRUE theorem ruling out the FALSE route must
eventually annihilate these marked pairings; any FALSE construction need
only keep one of them nonzero while other quotient directions permit
unbounded transfer.
