# Infinite abelian lamps give one common hard group factor

Date: 2026-08-12

## 1. Outcome

Let `Gamma<G` be one of the residually finite Kazhdan infranormal pairs of
Kun--Thom, put

\[
 X=G/\Gamma,
\]

and, for a countable abelian group `A`, define

\[
 W_A=A^{(X)}\rtimes G.
 \tag{ILF1}
\]

If `A` and `B` are countably infinite abelian groups, then

\[
 \boxed{L(W_A)\cong L(W_B)}
 \tag{ILF2}
\]

by a trace-preserving isomorphism carrying the canonical copy of `L(G)`
onto the canonical copy of `L(G)`.

Thus the Connes-embeddability question for the hard generalized Bernoulli
crossed product is independent of the choice of an infinite abelian lamp.
In particular,

\[
 L\!\left((\bigoplus_{\mathbf N}C_2)^{(X)}\rtimes G\right)
 \cong
 L\!\left(\mathbf Z^{(X)}\rtimes G\right)
 \cong
 L\!\left(\mathbf Q^{(X)}\rtimes G\right).
 \tag{ILF3}
\]

The group on the left of `(ILF3)` is nonsofic because it contains the
Kun--Thom group `C_2^{(X)} semidirect G`.  Consequently, proving that any
one of the factors in `(ILF3)` is Connes embeddable would produce a
hyperlinear nonsofic group immediately.

This does not by itself prove Connes embeddability.  It does show that the
binary lamp is not load bearing for the operator-algebraic problem: one may
replace it by a torsion-free, divisible, or otherwise convenient infinite
abelian lamp without changing the finite factor.

## 2. Fourier form of the generalized wreath factor

Let `A` be countable abelian and let

\[
 K_A=\widehat A
\]

with Haar probability measure `m_A`.  Pontryagin--Fourier transform gives
a trace-preserving isomorphism

\[
 L(A^{(X)})\cong
 L^\infty(K_A^X,m_A^X).
 \tag{ILF4}
\]

Under `(ILF4)`, the action of `G` on the lamp group by coordinate
permutations becomes the generalized Bernoulli action

\[
 (g\cdot z)_x=z_{g^{-1}x}.
 \tag{ILF5}
\]

Therefore

\[
 L(W_A)\cong
 L^\infty(K_A^X,m_A^X)\rtimes G.
 \tag{ILF6}
\]

No soficity or approximation assertion is used here; `(ILF6)` is the
ordinary Fourier identification of a semidirect-product group algebra with
its group-measure-space crossed product.

## 3. Coordinatewise conjugacy for nonatomic bases

**Theorem 1 (infinite-lamp factor universality).**  If `A` and `B` are
countably infinite abelian groups, then `(ILF2)` holds.

**Proof.**  Haar measure on the compact metrizable group `K_A` has an atom
if and only if `K_A` is finite.  Indeed, translation invariance makes every
point have the same mass, and a positive point mass forces the compact group
to have finitely many points.  By Pontryagin duality, `K_A` is finite if and
only if `A` is finite.  Hence `(K_A,m_A)` and `(K_B,m_B)` are nonatomic
standard probability spaces.

Choose a measure-space isomorphism

\[
 \phi:(K_A,m_A)\longrightarrow(K_B,m_B)
 \tag{ILF7}
\]

modulo null sets.  Apply it in every coordinate:

\[
 \Phi:K_A^X\longrightarrow K_B^X,
 \qquad
 \Phi((z_x)_{x\in X})=(\phi(z_x))_{x\in X}.
 \tag{ILF8}
\]

The map `(ILF8)` is a measure-space isomorphism and, because the action
only permutes coordinates,

\[
 \Phi(g\cdot z)=g\cdot\Phi(z)
 \tag{ILF9}
\]

for every `g in G` and almost every `z`.  Pullback by `Phi` therefore gives
a trace-preserving, `G`-equivariant isomorphism between the two Bernoulli
Cartan algebras.  Extending it by the identity on the canonical group
unitaries gives an isomorphism of the crossed products in `(ILF6)`.  End
proof.

The conjugacy in Theorem 1 is only measurable.  The map `phi` need not be a
homomorphism of compact groups, and generally it is not.  That is precisely
why the two semidirect-product groups in `(ILF2)` can have very different
algebraic lamp groups while their group factors agree.

## 4. A nonsofic member of the common factor class

Put

\[
 A_\infty=\bigoplus_{n\in\mathbf N}C_2.
 \tag{ILF10}
\]

Choose one direct summand `C_2<A_infty`.  Coordinatewise inclusion gives a
`G`-equivariant embedding and hence a group embedding

\[
 C_2^{(X)}\rtimes G
 \hookrightarrow
 A_\infty^{(X)}\rtimes G.
 \tag{ILF11}
\]

Kun--Thom prove that the group on the left of `(ILF11)` is nonsofic.  Since
subgroups of sofic groups are sofic, the group on the right is nonsofic.

If the common factor `(ILF2)` is Connes embeddable, then `W_Ainfty` is
hyperlinear.  Together with `(ILF11)`, this gives a hyperlinear nonsofic
group.  Equivalently, it is enough to prove Connes embeddability for the
torsion-free lamp model

\[
 W_{\mathbf Z}=\mathbf Z^{(X)}\rtimes G.
 \tag{ILF12}
\]

The last reformulation is potentially useful because the lamp algebra is
now the integral permutation module `Z[X]`, rather than a Boolean algebra.
It may admit linear, Gaussian, or module-theoretic approximations which are
not visible in the binary presentation.

## 5. Why finite coordinatewise carry does not help

Suppose instead that one groups finitely many binary lamps at every site
and changes the compact group law on the resulting uniform finite base.
Every abelian group of order `2^m` contains a subgroup of order two.  Its
dual discrete lamp group therefore still contains `C_2`, and the analogue
of `(ILF11)` again embeds the Kun--Thom nonsofic group.  Thus no finite
coordinatewise carry can produce a sofic partner.

The passage to an infinite nonatomic base is the first place where the
factor can forget the algebraic lamp group completely.  Even there,
Theorem 1 gives factor isomorphism, not Connes embeddability.

## 6. Exact surviving target

The new endpoint is

\[
 \boxed{
 L\!\left(\mathbf Z^{(G/\Gamma)}\rtimes G\right)
 \text{ is Connes embeddable.}}
 \tag{ILF13}
\]

By Theorem 1 and `(ILF11)`, `(ILF13)` would solve the hyperlinear-versus-
sofic problem negatively.

There are two immediate falsification tests for an attempted proof of
`(ILF13)`.

1. Residual finiteness of `G` does not give finite models of the coset
   action `G curvearrowright G/Gamma`; Kun--Thom prove that action is
   nonsofic.  Any argument which silently replaces the permutation module
   `Z[X]` by finite quotient modules has assumed the missing theorem.
2. Connes embeddability of `L(G)` does not imply Connes embeddability of an
   arbitrary crossed product by `G`.  The action, not just the abstract
   quotient group, must be approximated.

What the reduction does permit is a change of technology.  Instead of
trying to approximate Boolean lamp projections, one can now search for a
matrix model of the integral module `Z[X]` and its covariance with `G`.
Any such model must be genuinely unitary rather than permutational, since a
diagonal-preserving/permutation model would make the forbidden generalized
Bernoulli action sofic.

## 7. Equivalent Gaussian formulation

Let `gamma` be the standard Gaussian probability measure on `R`.  The
product action

\[
 G\curvearrowright(\mathbf R^X,\gamma^X)
 \tag{ILF14}
\]

is the classical Gaussian action associated with the real quasi-regular
representation on `ell^2(X)`: the coordinate Gaussian variables form its
first chaos, and `G` permutes them through the representation
`lambda_(G/Gamma)`.

Both `(R,gamma)` and `(T,Haar)` are nonatomic standard probability spaces.
A measure-space isomorphism between them, applied coordinatewise, conjugates
`(ILF14)` to the torus generalized Bernoulli action.  Hence the common
factor also has the form

\[
 \boxed{
 L(W_A)\cong
 L^\infty(\mathbf R^{G/\Gamma},\gamma^{G/\Gamma})\rtimes G
 }
 \tag{ILF15}
\]

for every countably infinite abelian `A`.

This formulation isolates the one-particle representation which a matrix
construction must approximate.  The distinguished Gaussian coordinate at
`Gamma` is fixed by `Gamma` and moved by every element outside its coset
stabilizer.  It is therefore the classical relative-commutant wall from
`FALSE_RELATIVE_BICOMMUTANT_ENDPOINT.md`.

The standard easy Gaussian criterion does not apply: the quasi-regular
representation `lambda_(G/Gamma)` is weakly contained in the left regular
representation exactly when `Gamma` is amenable, whereas the Kun--Thom
subgroup is a nonamenable Kazhdan group.  Thus replacing the torus by
Gaussian coordinates changes the available analytic language but does not
silently supply the missing approximation.

The sharp representation-theoretic target is now:

> construct finite-dimensional almost representations of `G` carrying a
> positive-trace Gaussian/Clifford amplification of an almost
> `Gamma`-fixed vector which is moved by the strict predecessor.

Exact finite-dimensional representations cannot do this: the
finite-representation matching theorem makes their `Gamma`-fixed subspace
invariant under every compressor and hence under its inverse predecessor.
Any successful Gaussian model must therefore be genuinely nonliftable.

### Fermionic amplification threshold

There is a natural noncommutative attempt to turn a one-particle vector
into an order-one tracial wall.  For a finite-dimensional Hilbert space
`H`, let

\[
 \mathcal F_-(H)=\bigoplus_{j=0}^{\dim H}\bigwedge^jH
\]

be fermionic Fock space and let `Gamma_-(U)` be second quantization of
`U in U(H)`.  The normalized matrix trace satisfies the exact identity

\[
 \operatorname{tr}_{\mathcal F_-(H)}(\Gamma_-(U))
 =\det\!\left(\frac{I+U}{2}\right).
 \tag{ILF16}
\]

Consequently, for `U,V in U(d)`,

\[
 \|\Gamma_-(U)-\Gamma_-(V)\|_2^2
 =2-2\operatorname{Re}
   \det\!\left(\frac{I+U^*V}{2}\right).
 \tag{ILF17}
\]

Formula `(ILF17)` shows that normalized Hilbert--Schmidt closeness on the
one-particle space is not enough.  For example, if `U^*V` is `-1` on one
line and `1` on its orthogonal complement, then

\[
 \|U-V\|_{2,d}=\frac2{\sqrt d}\longrightarrow0,
\]

but the determinant in `(ILF17)` is zero and the amplified squared defect
is exactly `2`.  A sufficient dimension-uniform regime is unnormalized
trace-norm convergence

\[
 \|U-V\|_{1,\mathrm{unnormalized}}\longrightarrow0,
 \tag{ILF18}
\]

because the determinant product in `(ILF17)` is then forced to one.
Unnormalized Hilbert--Schmidt convergence alone controls the modulus but
does not control the accumulated determinant phase: taking
`U^*V=exp(i/d)I_d` makes the Frobenius defect tend to zero while the phase
of `(ILF16)` tends to `exp(i/2)`.  One can discard that phase only in a
projective model, not in the required honest unitary representation.
Ordinary normalized-HS microstates supply neither form of control.

Thus CAR/Clifford amplification does create a positive-trace Majorana wall,
but it magnifies low-rank relation errors instead of washing them out.  Any
CAR proof must first produce a superaccurate one-particle model or a new
amplification whose trace is Lipschitz in normalized Hilbert--Schmidt norm.
Simply second-quantizing a candidate quasi-regular microstate is invalid.

## 8. Amenable rounding leaves one basis-synchronization cocycle

The quantitative theorem of Burton--Chaudkhari--Juschenko--Muliarchyk says
that a hyperlinear approximation of an amenable group is close to a
sofic-induced approximation.  Applied to a hypothetical hyperlinear model
of `W_A`, this gives substantial local information.  If

\[
 B=A^{(X)},
\]

then, for every `g in G`,

\[
 B\rtimes\langle g\rangle
 \tag{ILF19}
\]

is amenable.  The restriction of the hypothetical model to `(ILF19)` can
therefore be rounded, on any prescribed finite window, to permutation
matrices.

This does not yet round the whole group.  The phrase "sofic-induced" is
basis dependent.  The rounding for `g` produces an orthonormal permutation
basis `E_g`, while the rounding for a second element `h` produces another
basis `E_h`.  Both rounded models are close to the same lamp microstate on
their overlap, but the transition unitary

\[
 T_{g,h}:E_g\longrightarrow E_h
 \tag{ILF20}
\]

is controlled only modulo the commutant of the common finite lamp
representation.  For a regular finite abelian lamp window with multiplicity
`k`, that commutant contains a full `M_k(C)` multiplicity factor.  It does
not shrink as the lamp window grows through a fixed microstate.

The transitions `(ILF20)` form an approximate unitary cocycle over the
finite `G`-window.  A common permutation basis exists precisely when this
cocycle can be gauged into the monomial normalizer with vanishing defect.
That is the same nonliftable multiplicity seam isolated by the relative-
commutant and atlas analyses.

This observation prevents an invalid but seductive argument.  Rounding the
restriction to every cyclic subgroup separately and then using the triangle
inequality would appear to turn any hyperlinear approximation into a sofic
one.  The rounded matrices are permutations in different bases, so the
triangle inequality cannot be applied inside one symmetric group.  The
common lamp subgroup supplies overlap data, but not automatic synchronization
of those bases.

Accordingly, amenable rounding reduces `(ILF13)` to the following sharp
finite problem:

> prove or disprove that the overlap cocycle of the locally rounded groups
> `B semidirect <g>` can be synchronized inside the lamp multiplicity
> commutants with dimension-independent normalized-HS control.

Successful synchronization would make the generalized Bernoulli action
sofic, contradicting Kun--Thom.  Therefore a hyperlinear model, if one
exists, must carry a genuinely nonmonomial commutant cocycle which survives
every finite lamp refinement.

## 9. Status

Proved here:

* the common-factor theorem `(ILF2)` for all countably infinite abelian
  lamps;
* a nonsofic group in that common factor class; and
* the torsion-free-lamp CE reduction `(ILF13)`; and
* the equivalent Gaussian crossed-product formulation `(ILF15)`.

Not proved:

* Connes embeddability of the common factor;
* hyperlinearity of any Kun--Thom generalized wreath product; or
* existence of a hyperlinear nonsofic group.
