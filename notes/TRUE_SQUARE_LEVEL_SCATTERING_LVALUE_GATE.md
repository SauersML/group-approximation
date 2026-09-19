# The square-level scattering denominator is a critical-value lattice gate

## Outcome

For the square-level projective family

\[
\Gamma_0(p^2,3)\subset \mathrm{SL}_3(\mathbb Z),
\]

the degree-two Eisenstein image is already known to be the graph of

\[
C_p^*(0):S_3(\Gamma_1(p))_{P_1}
   \longrightarrow S_3(\Gamma_1(p))_{P_2}.
\]

This note identifies the arithmetic content of that graph more precisely.
On every Hecke packet, the operator is a rational normalized local
intertwiner multiplied by an algebraic scattering slope.  The
Harder--Raghuram rational comparison identifies the transcendental content
of that slope, up to a nonzero arithmetic comparison factor in the Hecke
field, with the ratio of the two critical values

\[
\boxed{
\frac{L^{\rm coh}(1)}{\Omega^\varepsilon L^{\rm coh}(2)}.
}
\]

The arguments really are `1` and `2`: they follow by applying the
Harder--Raghuram weight formula to the balanced length-one Kostant
representative for the trivial coefficient system on `GL_3`.

This comparison factor cannot be discarded in an integral problem.
Harder--Raghuram work over the rationality field, where every nonzero field
element is invertible.  Proving that it is a unit in the localized ring of
integers is precisely an additional integral comparison theorem.  The 2026
work of Narayanan--Raghuram establishes such control, away from explicit
exceptional primes, in an analogous `GL_4` setting; it is not yet available
for this square-level `GL_3` family.

There is also an exact local lattice consequence.  The basis-independent
quantity is the sum of the absolute Smith exponents of the full scattering
map relative to the two localized boundary lattices.  If a Hecke block has
slope

\[
C_f=\alpha_fR_f
\]

and the normalized operator `R_f` is an isomorphism of the two localized
boundary lattices at a prime `q`, then the two projection indices of the
primitive graph have total `q`-adic length

\[
\boxed{
\operatorname{length}_{\mathfrak q}\operatorname{coker}(\operatorname{pr}_1)
+
\operatorname{length}_{\mathfrak q}\operatorname{coker}(\operatorname{pr}_2)
=r\,|v_{\mathfrak q}(\alpha_f)|,
}
\]

where `r` is the rank of the block over the local coefficient ring.  Thus
the integral graph detects the full numerator *and* denominator of the
scattering slope.  They cannot disappear through a fortunate choice of
which maximal face is used as the domain.

Consequently the square-level TRUE gate splits into four independent
pieces:

1. valuations of the full algebraic slopes, separated into their
   critical-value and integral-comparison factors;
2. the conductor of the one ramified normalized local operator at `p`;
3. the finite saturation group of the actual integral Eisenstein image;
4. comparison of the automorphic boundary norm with the fixed cellular
   norm used by the decoder.

All unramified finite places are harmless after normalization.  This is a
substantial sharpening of “understand `C_p^*(0)`”: it gives the exact
arithmetic quantities that a uniform projective decoder theorem must
control.

It does **not** prove that those quantities are uniformly bounded.

## 1. The Hecke-isotypic scattering operator

Let `V_p=S_3(\Gamma_1(p))` denote the weight-three cusp module occurring on
either of the two middle maximal-parabolic faces.  The preceding boundary
calculation gives

\[
H^2_{\rm Eis}(\Gamma_0(p^2,3);\mathbb C)
=\{\phi\oplus C_p^*(0)\phi:\phi\in V_p\}.
\tag{1}
\]

The operator commutes with the Hecke algebra away from the level.  Extend
scalars to a splitting field and fix a simple Hecke packet `f`.  Write
`V_{1,f}` and `V_{2,f}` for the corresponding summands on the two faces.
The rank-one Eisenstein-cohomology theorem of Harder--Raghuram identifies
the restriction graph with

\[
\{(\xi,T_{\rm Eis,f}\xi):\xi\in V_{1,f}\},
\tag{2}
\]

where `T_Eis,f` is defined over the rationality field `E_f`.  After an
embedding `E_f -> C`, this is the map induced by the global standard
intertwining operator.  Their equations for the global-to-local
factorization give

\[
T_{\rm Eis,f}
\sim_{E_f^\times}c_\infty\,
\frac{L^{\rm coh}(\sigma_f\times\sigma_f'{}^\vee,m_0)}
     {\Omega^\varepsilon(\sigma_f)
      L^{\rm coh}(\sigma_f\times\sigma_f'{}^\vee,m_0+1)}
\,R_f.
\tag{3}
\]

where the comparison is through their rational arithmetic maps.  More
intrinsically, and in the form needed below, write

\[
T_{\rm Eis,f}=\alpha_fR_f,
\qquad
\alpha_f
=u_fc_\infty
\frac{L^{\rm coh}(\sigma_f\times\sigma_f'{}^\vee,m_0)}
     {\Omega^\varepsilon(\sigma_f)
      L^{\rm coh}(\sigma_f\times\sigma_f'{}^\vee,m_0+1)},
\tag{3a}
\]

where `u_f in E_f^x` is the arithmetic comparison factor.  The rational
theorem proves algebraicity and Galois equivariance of the critical-value
ratio; it does **not** prove that `u_f` is an algebraic-integer unit in a
family of integral lattices.

Here:

- `(sigma_f,sigma'_f)` is the `GL_2 x GL_1` inducing packet;
- `Omega^epsilon` is the relative period required in the even--odd case;
- `c_infinity` is the fixed nonzero archimedean rational normalization
  (including the fixed power of `i`); and
- `R_f` is the tensor product of normalized local intertwining operators.

At every finite unramified place, the normalized local operator takes the
normalized spherical vector to the normalized spherical vector.  In this
family all varying finite local arithmetic is therefore concentrated at
the level prime `p`.  The archimedean factor depends on the fixed weights,
not on `p` or on the packet.

Equation (3a) is basis-dependent only in the expected way.  Changing an
arithmetic generator multiplies `u_f` and conjugates the integral lattice.
Once the two modular-symbol lattices and the normalized local newvectors
are fixed, the nonunit valuations of the *product* `alpha_f` are intrinsic.
Separating those valuations between the critical ratio and `u_f` requires
an integral comparison theorem.

## 2. Why the critical arguments are exactly 1 and 2

This specialization is short enough to compute directly.

Take the standard parabolic of type `(2,1)` in `GL_3`, and let

\[
\lambda=(0,0,0)
\]

be the trivial highest weight.  The balanced Kostant representative has
length one; choose `w=s_2`.  With
`rho=(1,0,-1)`, its dot action gives

\[
w\cdot\lambda=w(\rho)-\rho=(0,-1;1).
\tag{4}
\]

Thus the `GL_2` weight is `mu=(0,-1)` and the `GL_1` weight is `mu'=1`.
In the notation of Harder--Raghuram, the `GL_2` weight has

\[
a_1=2,\qquad d=-\frac12,\qquad \mathbf w=2,
\]

while the `GL_1` weight has

\[
d'=1,\qquad \mathbf w'=0.
\]

Since `N=2+1=3`, their critical point formula becomes

\[
\begin{aligned}
m_0
&=-\frac N2+\frac{\mathbf w+\mathbf w'}2-(d-d')\\
&=-\frac32+1-\left(-\frac12-1\right)=1.
\end{aligned}
\tag{5}
\]

Therefore (3) uses the two successive critical cohomological values at
`1` and `2`.  In classical language these are the two critical values of
the weight-three degree-two `L`-function attached to the inducing
`GL_2 x GL_1` packet.  The `GL_1` character records the nebentypus/central
character of the particular `Gamma_1(p)` packet, so it is safer to retain
the Rankin--Selberg notation than to suppress that twist.

Put

\[
\alpha_f:=u_fc_\infty
\frac{L^{\rm coh}(\sigma_f\times\sigma_f'{}^\vee,1)}
     {\Omega^\varepsilon(\sigma_f)
      L^{\rm coh}(\sigma_f\times\sigma_f'{}^\vee,2)}.
\tag{6}
\]

Then the packetwise scattering map has the promised form

\[
\boxed{C_f=\alpha_fR_f.}
\tag{7}
\]

## 3. An exact Smith-height lemma for primitive graphs

The following elementary lemma is the useful integral interface.  Its
general form matters because the splitting `C_f=alpha_f R_f` depends on the
normalization of `R_f`, whereas the Smith exponents of the full map do not.

### Lemma 1 (the primitive graph records the full Smith height)

Let `O` be a discrete valuation ring with uniformizer `pi` and fraction
field `K`.  Let `L_1,L_2` be free `O`-modules of rank `r`, and let

\[
C:L_1\otimes K\overset\sim\longrightarrow L_2\otimes K
\]

be a `K`-linear isomorphism.  Choose Smith bases so that

\[
Ce_i=\pi^{a_i}f_i,
\qquad a_i\in\mathbb Z.
\tag{8a}
\]

For the primitive graph lattice

\[
G_C=(L_1\oplus L_2)\cap\{(x,Cx):x\in L_1\otimes K\},
\]

one has

\[
\operatorname{length}\frac{L_1}{\operatorname{pr}_1(G_C)}
=\sum_i\max(0,-a_i),
\qquad
\operatorname{length}\frac{L_2}{\operatorname{pr}_2(G_C)}
=\sum_i\max(0,a_i).
\tag{8b}
\]

Consequently

\[
\boxed{
\operatorname{length}\operatorname{coker}(\operatorname{pr}_1)
+\operatorname{length}\operatorname{coker}(\operatorname{pr}_2)
=\sum_i|a_i|.
}
\tag{8c}
\]

#### Proof

Writing `x=sum_i x_i e_i`, membership in `G_C` is coordinatewise

\[
x_i\in O,
\qquad
\pi^{a_i}x_i\in O.
\]

Thus `x_i` belongs to `pi^{max(0,-a_i)}O`.  The first projection
therefore has elementary divisors `max(0,-a_i)`.  Applying `C` shows that
the second projection has elementary divisors

\[
a_i+\max(0,-a_i)=\max(0,a_i).
\]

Summing the two lengths gives (8c). \(\square\)

### Corollary 2 (a scalar slope records both signs of its valuation)

Let `O` be a discrete valuation ring with uniformizer `pi`, fraction field
`K`, and valuation `v`.  Let `L_1,L_2` be free `O`-modules of rank `r`, and
let

\[
R:L_1\overset\sim\longrightarrow L_2
\]

be an `O`-linear isomorphism.  For `alpha in K^x`, let

\[
G_\alpha=(L_1\oplus L_2)\cap
\{(x,\alpha Rx):x\in L_1\otimes K\}
\]

be the primitive graph lattice.  Then

\[
\operatorname{pr}_1(G_\alpha)
=\pi^{\max(0,-v(\alpha))}L_1,
\tag{8}
\]

and

\[
\operatorname{pr}_2(G_\alpha)
=\pi^{\max(0,v(\alpha))}L_2.
\tag{9}
\]

In particular,

\[
\operatorname{length}\frac{L_1}{\operatorname{pr}_1(G_\alpha)}
+\operatorname{length}\frac{L_2}{\operatorname{pr}_2(G_\alpha)}
=r|v(\alpha)|.
\tag{10}
\]

#### Proof

A point of the rational graph belongs to `L_1+L_2` precisely when

\[
x\in L_1,\qquad \alpha Rx\in L_2.
\]

Since `R` is an integral isomorphism, this is equivalent to

\[
x\in L_1\cap\alpha^{-1}L_1
=\pi^{\max(0,-v(\alpha))}L_1.
\]

This proves (8).  Multiplication by `alpha R` sends that lattice onto
`pi^{max(0,v(alpha))}L_2`, proving (9).  Taking lengths gives (10).
\(\square\)

### Corollary 3 (the exact local obstruction)

Let `mathfrak q` be a prime of `E_f` at which `R_f` identifies the two
localized modular-symbol lattices.  If `G_f` is the primitive integral
graph of `C_f`, then

\[
\operatorname{length}_{\mathfrak q}\operatorname{coker}
 (\operatorname{pr}_1:G_f\to L_{1,f})
+
\operatorname{length}_{\mathfrak q}\operatorname{coker}
 (\operatorname{pr}_2:G_f\to L_{2,f})
=r_f|v_{\mathfrak q}(\alpha_f)|.
\tag{11}
\]

Hence changing from one maximal face to the other merely exchanges the
positive and negative parts of the valuation.  It cannot remove the
arithmetic height of the scattering slope.

If `R_f` is not an integral isomorphism and has Smith exponents `b_i`, then
the full map has Smith exponents

\[
a_i=v_{\mathfrak q}(\alpha_f)+b_i,
\]

and the intrinsic obstruction is

\[
\sum_i|v_{\mathfrak q}(\alpha_f)+b_i|.
\tag{11a}
\]

It would be incorrect to replace (11a) by
`r|v(alpha_f)|+sum_i|b_i|`: cancellation can occur.  Moving a scalar
between `alpha_f` and `R_f` changes the two displayed contributions but
leaves the Smith height (11a) unchanged.  In this family the nonzero `b_i`
can vary only at the ramified level prime `p`, apart from a fixed finite set
caused by the coefficient-system and archimedean normalizations.

## 4. Relation with the actual Eisenstein lattice

Let `L_p` be the full integral middle boundary lattice and let

\[
E_p=\operatorname{im}
\bigl(H^2(\overline Y_p;\mathbb Z)\to
H^2(\partial\overline Y_p;\mathbb Z)\bigr)/\text{torsion}.
\]

Its primitive saturation is

\[
E_{p,\rm sat}=L_p\cap(E_p\otimes\mathbb Q).
\]

Rationally, `E_p tensor Q` is the scattering graph (1), so packetwise
`E_{p,sat}` is the primitive graph lattice of Lemma 1.  The finite quotient

\[
E_{p,\rm sat}/E_p
\tag{12}
\]

is an additional obstruction, not part of the critical-value slope itself.
The integral duality theorem already shows that (12) injects into a torsion
subquotient of absolute degree-two homology.

Thus there are three distinct integral phenomena:

- **graph arithmetic:** the valuations in (11), including both the
  critical-value ratio and the arithmetic comparison factor `u_f`;
- **local arithmetic:** the conductor of the ramified normalized operator
  `R_f`;
- **failure of primitivity:** the saturation group (12).

Conflating them can make a computation look more mysterious than it is.

## 5. What the recent integral refinement adds

Narayanan--Raghuram refine the Harder--Raghuram construction at the level
of integral cohomology for a `GL_4` rank-one Eisenstein problem.  Their
analysis is not a theorem for this `GL_3` family, but it confirms exactly
the arithmetic fault lines isolated above.  Their integral comparison
must exclude:

- primes dividing the level;
- primes supporting torsion in integral Eisenstein cohomology;
- a fixed set of small/archimedean primes; and
- primes introduced by ramified local intertwining calculations.

In particular, rationality of `T_Eis` does not by itself give a uniform
integral theorem as the level varies.  It does not even show that the
comparison factor `u_f` has zero valuation.  The level prime, comparison
lattices, and Eisenstein torsion must be treated rather than hidden in a
rational change of basis.

## 6. The sharpened TRUE target

For the square-level projective charts, a sufficient family theorem now
has a concrete form.  It would be enough to prove all of the following
uniformly in `p` and in every weight-three Hecke packet `f`:

1. the valuations `|v_q(alpha_f)|`, measured in the relevant integral
   modular-symbol normalizations, have bounded decoder cost; equivalently,
   one must control both the critical ratio and the comparison factor
   `u_f` without assuming cancellation;
2. the normalized `p`-local intertwiner `R_{p,f}` and its inverse have
   bounded integral elementary divisors after the chart normalization;
3. the saturation groups `E_{p,sat}/E_p` admit uniformly bounded sections;
4. the automorphic/modular-symbol norm and the fixed cellular norm have
   uniformly bounded comparison on the dangerous paired-discriminant
   directions.

The first item is a critical-value/congruence-ideal problem, the second is
a single local newvector calculation, the third is torsion topology, and
the fourth is metric comparison.  They are logically independent.

Conversely, Corollary 2 shows that any proof claiming a uniformly integral
two-sided scattering graph must account for the nonunit valuations of
`alpha_f`; an Atkin--Lehner or functional-equation slogan alone is not an
integral proof.

This square-level theorem remains a test-family theorem.  Even after it is
completed, the universal hyperlinear-to-sofic implication still requires
the separate Cartan-selection and arbitrary-colored-action phase-completion
steps recorded in `TRUE_SELECTED_CHART_QUANTIFIER_BOUNDARY.md`.

## Sources

- Ronnie Lee and Joachim Schwermer, *Cohomology of arithmetic subgroups of
  `SL_3` at infinity*, J. reine angew. Math. 330 (1982), Section 6.1,
  especially equation (9) and the sentence immediately following it.
- Gunter Harder and A. Raghuram, *Eisenstein Cohomology for `GL_N` and
  ratios of critical values of Rankin--Selberg `L`-functions*,
  arXiv:1405.6513, especially the rank-one Eisenstein graph theorem, the
  global-to-local formula for `T_st`, equation defining the normalized
  finite local operator, and Theorem 7.36.
- P. Narayanan and A. Raghuram, *Eisenstein cohomology and congruences for
  the ratios of Rankin--Selberg `L`-functions*, arXiv:2512.02927v2,
  especially Sections 5--7 and the exceptional-prime discussion in the
  introduction.
- `TRUE_SQUARE_LEVEL_EISENSTEIN_GRAPH.md` for the descent to the two middle
  faces and the dimension formula.
- `TRUE_BOUNDARY_KERNEL_IS_EISENSTEIN_DUAL.md` for the integral saturation
  sequence.
