# Integral chain comparison transports harmonic carry decoders

Date: 2026-08-11

## Purpose

The first cuspidal projective chart now has two exact descriptions:

* a compact rank-two Ash--Grayson--Green function lattice; and
* the degree-two harmonic lattice in the large HAP cellular complex.

`TRUE_P53_CUSPIDAL_FUNCTION_LATTICE.md` left an explicit integral comparison
map between them as the next finite task.  This note proves the precise
transport theorem that such a comparison must satisfy.

An integral chain-homotopy equivalence transports the harmonic lift exact
sequence and every integral decoder.  If the degree-`r` comparison maps have
operator norms `F` and `G`, then both the optimal nonlinear lift distortion
and the least integral-section norm change by at most the factor `FG`.

The important point is that no inverse harmonic matrix and no rational basis
of the large harmonic plane is needed.  Orthogonal projection is only used
in the proof; the transported decoder itself is the integral composite

`f^r compose s compose g_H`.                                      `(CDT1)`

This is a fixed-chart and family-level reduction.  It does not construct the
still-missing AGG--HAP chain maps.

## 1. Harmonic lift sequence of an integral cochain complex

Let `C` be a finite cochain complex of finite-rank free abelian groups.  In
the relevant three degrees write

`C_Z^(r-1) --d_C--> C_Z^r --e_C--> C_Z^(r+1)`,                    `(CDT2)`

and equip the realifications with Euclidean inner products.  Put

`W_C=ran_R(d_C)`,
`L_C=W_C intersect C_Z^r`,                                       `(CDT3)`

`M_C=ker_R(e_C) intersect C_Z^r`,
`H_C=ker_R(e_C) intersect W_C^perp`.                             `(CDT4)`

Let `pi_C:ker_R(e_C)->H_C` be orthogonal projection and define the harmonic
integral lattice

`Q_C^#=pi_C(M_C)`.                                               `(CDT5)`

**Lemma 1 (canonical lift sequence).**  Projection gives a short exact
sequence of free abelian groups

`0 -> L_C -> M_C --pi_C--> Q_C^# -> 0`.                          `(CDT6)`

**Proof.**  Surjectivity is the definition of `Q_C^#`.  If `m in M_C` has
zero harmonic projection, then `m in W_C`; integrality gives `m in L_C`.
Conversely every element of `L_C` is a cocycle because `e_C d_C=0` and has
zero harmonic projection.  End proof.

This is exactly the sequence

`0 -> L -> M_Sigma -> Q^# -> 0`                                  `(CDT7)`

from `TRUE_HARMONIC_INTEGRAL_LIFT_SEQUENCE.md`: there `M_Sigma` is the
integral cocycle lattice, `L` is the saturated coboundary lattice, and
`Q^#` is the harmonic representative lattice.

For `u in Q_C^#`, define

`lambda_C(u)=min{||m||:m in M_C, pi_C(m)=u}`,                     `(CDT8)`

and the nonlinear lift distortion

`kappa_C=sup_(0!=u in Q_C^#) lambda_C(u)/||u||`.                 `(CDT9)`

Let

`mu_C=inf{||s||:s:Q_C^#->M_C is a Z-linear section of pi_C}`.    `(CDT10)`

The infimum is a minimum, but only its functorial bounds will be needed.

## 2. Harmonic maps induced by integral cochain maps

Let `D` be a second such complex and let

`f:C->D`                                                         `(CDT11)`

be an integral cochain map.  Its degree-`r` map sends `M_C` to `M_D` and
`L_C` to `L_D`.  Define

`f_H:H_C->H_D`, `f_H(h)=pi_D(f^r h)`.                            `(CDT12)`

**Lemma 2 (integral harmonic functoriality).**  The map `f_H` sends
`Q_C^#` to `Q_D^#`, and for every `m in M_C`,

`pi_D(f^r m)=f_H(pi_C m)`.                                      `(CDT13)`

Moreover

`||f_H||<=||f^r||`.                                              `(CDT14)`

**Proof.**  Write `m=pi_Cm+b` with `b in W_C`.  Since `f` is a cochain map,
`f^r b in W_D`, so its harmonic projection is zero.  This proves `(CDT13)`
and shows that `f_H(pi_Cm)` lies in `Q_D^#`.  Orthogonal projection is a
contraction, giving `(CDT14)`.  End proof.

Now suppose there is an integral cochain map

`g:D->C`                                                         `(CDT15)`

and integral cochain homotopies

`g f homotopic to id_C`, `f g homotopic to id_D`.                `(CDT16)`

**Lemma 3 (exact harmonic inverse).**  The harmonic maps are inverse
Euclidean lattice isomorphisms

`g_H f_H=id_(H_C)`, `f_H g_H=id_(H_D)`,                          `(CDT17)`

and restrict to inverse isomorphisms

`Q_C^# ~= Q_D^#`.                                                `(CDT18)`

**Proof.**  A harmonic vector is a cocycle.  The difference `(gf-id)h` is
therefore a real coboundary by the chain-homotopy identity, and harmonic
projection kills it.  Replacing `fh` by its harmonic projection changes it
by a coboundary; applying `g` still gives a coboundary.  Hence

`g_H f_H h=pi_C(g^r f^r h)=h`.                                  `(CDT19)`

The other identity is identical.  Lemma 2 then gives `(CDT18)` over the
integral harmonic lattices, not merely over their real spans.  End proof.

Only the conclusion `(CDT17)--(CDT18)` is needed below.  Thus a pair of
integral cochain maps inducing inverse maps on the relevant free cohomology
summands is enough; a global chain-homotopy equivalence is a convenient
sufficient condition.

## 3. Decoder transport

**Theorem 4 (integral decoder transport).**  Under `(CDT11)--(CDT16)`,

`kappa_D<=||f^r|| ||g^r|| kappa_C`,
`kappa_C<=||g^r|| ||f^r|| kappa_D`,                              `(CDT20)`

and

`mu_D<=||f^r|| ||g^r|| mu_C`,
`mu_C<=||g^r|| ||f^r|| mu_D`.                                   `(CDT21)`

More explicitly, if `s_C:Q_C^#->M_C` is an integral section, then

`s_D=f^r compose s_C compose g_H:Q_D^#->M_D`                    `(CDT22)`

is an integral section and

`||s_D||<=||f^r|| ||g^r|| ||s_C||`.                             `(CDT23)`

**Proof.**  For `u in Q_D^#`, put `v=g_Hu`.  Choose a shortest lift
`m in M_C` of `v`.  Lemma 2 and `(CDT17)` give

`pi_D(f^r m)=f_H(v)=u`.                                         `(CDT24)`

Therefore

`lambda_D(u)<=||f^r|| lambda_C(g_Hu)`
` <=||f^r|| kappa_C ||g_Hu||`
` <=||f^r|| ||g^r|| kappa_C ||u||`.                             `(CDT25)`

Taking the supremum proves the first half of `(CDT20)`; interchange `C,D`
and `f,g` for the second.

The composite `(CDT22)` is integral by `(CDT18)`.  Using Lemma 2 and the
section identity,

`pi_D s_D=f_H pi_C s_C g_H=f_H g_H=id`.                          `(CDT26)`

Thus it is a section.  Its norm satisfies `(CDT23)` by `(CDT14)`, and taking
the least section norm proves `(CDT21)`.  End proof.

No norm of either chain homotopy occurs.  Homotopies certify that the
harmonic maps are inverse; the quantitative loss comes only from the two
degree-`r` comparison maps.

### Sector version

Let `U_C subset Q_C^#` and `U_D subset Q_D^#` be primitive sublattices such
that `f_H,g_H` restrict to inverse isomorphisms between them.  Replace
`M_C,M_D` by the inverse images of `U_C,U_D` under harmonic projection.
The proof of Theorem 4 is unchanged.  Hence the theorem applies directly to
a cuspidal direct summand even when the comparison maps are not equivalences
on Eisenstein or torsion sectors.

## 4. Uniform local comparisons

Consider families `C_n,D_n` with normalized counting norms.  Suppose the
integral comparison maps satisfy

`sup_n ||f_n^r||<=F`, `sup_n ||g_n^r||<=G`.                       `(CDT27)`

Then Theorem 4 gives

`(FG)^(-1) kappa_(C_n)<=kappa_(D_n)<=FG kappa_(C_n)`,             `(CDT28)`

and the same statement for `mu`.  Therefore uniform boundedness, or
divergence, of the harmonic integral decoder is invariant under a uniformly
bounded integral chain comparison.

This is the correct family-level target for local cellular models.  A map
defined by a fixed number of bounded-coefficient incidences per cell has
uniform normalized `L2` operator norm by the Schur bound.  Thus a
bounded-propagation comparison between the projective modular-symbol complex
and the fixed HAP resolution would preserve the carry-decoder problem with
one explicit universal factor.

## 5. Consequence for the level-53 chart

At level `53`, the free cuspidal harmonic rank is two.  The compact function
lattice has the exact Gram matrix

`[[7872,-3264],[-3264,71424]]`.                                  `(CDT29)`

Theorem 4 changes the required finite computation.  It is enough to produce
integral degree-two comparison maps `f^2,g^2` which induce inverse maps on
the two-dimensional free cuspidal cohomology.  Given two integral lifts in
the compact model, formula `(CDT22)` produces two integral HAP lifts
directly.  The HAP decoder bound is then

`mu_HAP<=||f^2|| ||g^2|| mu_AGG`.                                `(CDT30)`

One modular comparison can identify the two directions, while exact integer
chain identities certify integrality and the induced inverse relation.  A
28,630-coordinate rational harmonic reconstruction is unnecessary.

For a TRUE family theorem, the comparison must be local enough that the two
operator norms in `(CDT27)` remain uniform in `p`, and the compact model must
itself admit uniformly bounded integral sections.  The present result
separates these two questions exactly:

`uniform compact decoder + uniform integral chain comparison`
`                    => uniform HAP harmonic decoder.`            `(CDT31)`

The remaining arithmetic task is now to construct either side of `(CDT31)`,
not to compare anonymous high-dimensional harmonic bases.

For fixed free `Z[G]` resolutions, the uniform comparison required here is
automatic.  `TRUE_FIXED_RESOLUTION_DECODER_INVARIANCE.md` constructs fixed
group-ring comparison matrices and bounds every finite-chart specialization
by their coefficient `l1` Schur norms.  Proper cellular models with finite
stabilizers have the same property after inverting the stabilizer orders;
the remaining failure of integral comparison is therefore bounded-primary
torsion, not growth of the real comparison norm.
