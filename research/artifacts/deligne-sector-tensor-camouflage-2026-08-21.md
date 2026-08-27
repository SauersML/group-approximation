# Deligne sector tensor camouflage

Date: 2026-08-21

## The theorem

For Deligne's central extension

\[
1\longrightarrow \langle z\rangle\cong \mathbf Z/3
\longrightarrow E_3\longrightarrow
\Gamma=\operatorname{Sp}_4(\mathbf Z)\longrightarrow 1,
\]

the proposed dimension-free mod-three Maslov projective-defect gap is
equivalent to non-hyperlinearity of `E_3`.  The apparently weaker assertion
that every finite-dimensional normalized-HS almost representation collapses
the single word `z` is equivalent to the same statement.

This is a closure of an attack, not a proof that `E_3` is non-hyperlinear.  It
shows that the direct Deligne lane has not reduced the terminal problem.

## 1. Tensor camouflage

Fix a section `s:Gamma->E_3` and write

\[
s(g)s(h)=z^{c(g,h)}s(gh),\qquad c(g,h)\in\mathbf Z/3.
\]

Put `omega=exp(2 pi i/3)`.  Suppose there are finite-dimensional maps `U_n`
with presentation-window defect tending to zero for the multiplier

\[
\alpha(g,h)=\omega^{c(g,h)}.
\]

Thus, on every fixed tested product,

\[
\|U_n(g)U_n(h)-\alpha(g,h)U_n(gh)\|_2\to0.
\]

The arithmetic group `Gamma` is residually finite.  Choose finite quotients
separating an exhausting sequence of finite subsets and let `V_n` be their
left-regular representations.  Then `V_n` are exact on `Gamma` and, for every
fixed `g!=1`,

\[
\operatorname{tr}(V_n(g))=0
\]

eventually.  Define on a finite presentation of `E_3`

\[
\rho_n(z)=\omega I,
\qquad
\rho_n(s)=U_n(s)\otimes V_n(s)
\]

for quotient generators `s`.  Every relator evaluation is a tensor product;
the scalar projective phase exactly supplies its prescribed power of `z`.
The normalized-HS tensor identity

\[
\|A\otimes W\|_2=\|A\|_2
\quad(W\text{ unitary})
\]

shows that the defects tend to zero.

These tuples induce a homomorphism from `E_3` to a tracial matrix
ultraproduct.  It is injective.  Every element has a unique form `z^k s(g)`.
If `g!=1`, normalized traces factor and the regular quotient factor gives

\[
\operatorname{tr}(\rho_n(z^ks(g)))
=\omega^k\operatorname{tr}(U_n(g))
 \operatorname{tr}(V_n(g))\longrightarrow0,
\]

so its ultraproduct image is not the identity.  If `g=1` and `k!=0`, its
image is the nonidentity scalar `omega^k I`.  Hence `E_3` is hyperlinear.

Notice why canonical trace is not required on the centre: hyperlinearity is
faithful metric-ultraproduct embeddability.  The scalar images of `z` and
`z^2` remain a fixed positive distance from the identity.  The quotient
regular tensor supplies faithfulness everywhere else.

The same proof works for the `alpha^2` sector with `rho_n(z)=omega^2 I`.

## 2. Cutting a hyperlinear embedding into Maslov sectors

Conversely suppose `E_3` is hyperlinear.  Represent a faithful embedding by
finite presentation microstates.  Functional calculus rounds the image of
`z` to an exact order-three unitary.  Approximate centrality makes its three
spectral projections asymptotically invariant, and polar correction produces
projective almost representations on the spectral blocks, as recorded in
`finite-central-hs-sector-decomposition`.

Faithfulness implies that the image of `z` is not the identity in the metric
ultraproduct.  Therefore the sum of the traces of the `omega` and `omega^2`
blocks is positive.  Since there are only two blocks, one has positive trace
along a subsequence.  The dimension-weighted defect tends to zero, so the
defect within that positive-density block tends to zero.  It is an
`alpha`- or `alpha^2`-projective almost representation.  The anti-symplectic
automorphism from `maslov-inverse-sector-symmetry` interchanges them without
changing defect.  Thus

\[
E_3\text{ hyperlinear}
\iff \inf_{d,U}\operatorname{def}_{\alpha}(U)=0
\iff \inf_{d,U}\operatorname{def}_{\alpha^2}(U)=0.
\]

Taking negations gives the claimed equivalence between non-hyperlinearity and
the uniform projective defect gap.

## 3. Equivalence with central-mark collapse

If `E_3` is hyperlinear, faithful microstates keep `z` a positive distance
from the identity, so universal central-mark collapse fails.

In the other direction, suppose central-mark collapse fails.  After a
subsequence there is `epsilon>0` with

\[
\|\rho_n(z)-I\|_2\ge\epsilon.
\]

The finite central-sector decomposition then puts positive asymptotic weight
in at least one nontrivial sector.  Because the total dimension-weighted
relator defect tends to zero, that sector contains a sequence with projective
defect tending to zero.  Tensor camouflage from Section 1 makes `E_3`
hyperlinear.  Consequently

\[
\text{central-mark HS collapse}\iff E_3\text{ is non-hyperlinear}.
\]

## 4. Consequence for the direct Deligne route

Deligne's theorem plus Malcev proves that every exact finite-dimensional
representation kills `z`.  This says only that each fixed-dimensional defect
infimum is nonzero or unattained at zero.  It does not control the infimum as
dimension tends to infinity.  The desired uniform control is already exactly
non-hyperlinearity.

Property (T) may still be useful in a future proof of that terminal fact, but
it does not turn the Maslov gap or one-word collapse into a logically weaker
intermediate theorem.  Any successful Deligne attack must therefore add a
new dimension-uniform mechanism; finite-dimensional invisibility plus
sectorization alone cannot provide one.

