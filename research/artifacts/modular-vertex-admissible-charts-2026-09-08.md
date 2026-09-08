# Exact modular vertex parameterizations with uniform Schatten control

2026-09-08. A direct finite-matrix proof. No local code, remote numerical
job, or build was used. This supplies an explicit admissible
parameterization with the bounds requested by the Iwahori quadratic-repair
proposal. It supplies no residual-canceling direction and does not settle
that repair problem or nonhyperlinearity.

## 1. The representation-preserving map

Use the presentation

```text
V=SL_2(Z)=<s,b | s^4=1, s^2=b^3> = C_4 *_(C_2) C_6,
z=s^2=b^3.
```

The element `z` is central and has order two. Let `rho:V->U(d)` be
any representation, and write `S=rho(s)`, `B=rho(b)`, and `Z=rho(z)`.
The representation need not factor through a congruence quotient.
The matrix `Z` can have both signs in its spectrum.

Let `E_rho` be the real vector space of triples of anti-Hermitian
matrices `H=(H_0,H_4,H_6)` satisfying

```text
Ad(Z)H_0=-H_0,             [H_4,Z]=[H_6,Z]=0.
```

For every `H` in this entire vector space define

```text
S_H=e^(H_0) e^(H_4) S e^(-H_4) e^(-H_0),
B_H=e^(H_0) e^(H_6) B e^(-H_6) e^(-H_0).                 (MC1)
```

All exponentials are unitary. The inner exponentials commute with `Z`,
and therefore

```text
S_H^2=e^(H_0) Z e^(-H_0)=B_H^3,
S_H^4=B_H^6=I.                                         (MC2)
```

Thus `(MC1)` defines an exact representation `Psi_rho(H)` for every
parameter value. Its domain contains every straight segment needed for
Taylor expansion. No operator-norm smallness or inverse-function
argument is needed for this forward map.

For matrix tuples set `||H||_p=max_j ||H_j||_(p,d)`. The cocycle norm is
`||c||_p=max(||c(s)||_(p,d),||c(b)||_(p,d))`. For pairs of vertices use
the maximum over the two vertices as well. All traces are normalized.

## 2. A linear lift of every cocycle

Our conventions are

```text
c(gh)=c(g)+Ad(rho(g))c(h),
delta H(g)=H-Ad(rho(g))H.
```

Thus conjugating a representation by `exp(tH)` has right-logarithmic
derivative `delta H`: the derivative at `g`, multiplied on the right
by `rho(g)^*`, is `delta H(g)`.

Let `c:V->u(d)` be any such cocycle. Since `z^2=1`,

```text
c(z)+Ad(Z)c(z)=0.
```

Set `H_0=c(z)/2`. Then `Ad(Z)H_0=-H_0` and
`delta H_0(z)=c(z)`. Since `zg=gz`, the two cocycle expansions give

```text
(I-Ad(rho(g)))c(z)=(I-Ad(Z))c(g).
```

Consequently the residual cocycle is exactly the central conditional
average

```text
c_0(g):=c(g)-delta H_0(g)=P_Z c(g),
P_Z=(I+Ad(Z))/2.                                       (MC3)
```

It commutes with `Z` and satisfies `c_0(z)=0`.

Write `a=c_0(s)` and `T=Ad(S)`. Since `s^2=z`,

```text
(I+T)a=0.
```

Hence `H_4=a/2` satisfies `(I-T)H_4=a`.

Write `b_0=c_0(b)` and `Q=Ad(B)`. The equation `b^3=z` gives

```text
(I+Q+Q^2)b_0=0,             Q^3 b_0=b_0.
```

Set

```text
H_6=(b_0-Q^-1 b_0)/3.                                  (MC4)
```

On this vector, `Q^-1=Q^2`, so

```text
(I-Q)H_6=(2I-Q-Q^-1)b_0/3=b_0.                         (MC5)
```

Both `H_4` and `H_6` commute with `Z`. They are anti-Hermitian, since
all formulas use real combinations of unitary conjugations of
anti-Hermitian matrices. Thus `J_rho(c)=(H_0,H_4,H_6)` lies in `E_rho`.
Every operation is real-linear in the cocycle.

Differentiating `(MC1)` at zero gives right-logarithmic derivatives

```text
c_H(s)=delta(H_0+H_4)(s),
c_H(b)=delta(H_0+H_6)(b).                              (MC6)
```

Equations `(MC3)`--`(MC5)` show `c_H(s)=c(s)` and `c_H(b)=c(b)`.
A cocycle is determined by its values on generators, so the derivative
of `Psi_rho` composed with `J_rho` is the identity on all cocycles.
In particular every cocycle is the derivative of an explicit curve of
exact vertex representations. This is a statement about one vertex;
it does not assert compatibility of the resulting two-vertex curve.

## 3. Simultaneous norm control and tuple flatness

Unitary conjugation preserves every Schatten norm, and `P_Z` is the
average of two such isometries, hence contractive. Since
`c(z)=c(s)+Ad(S)c(s)`, for every `1<=p<=infinity`,

```text
||H_0||_p <= ||c(s)||_p,
||H_4||_p <= (1/2)||c(s)||_p,
||H_6||_p <= (2/3)||c(b)||_p.
```

In tuple norms this proves

```text
||J_rho(c)||_p <= ||c||_p.                             (MC7)
```

Conversely `(MC6)` and `||delta K(g)||_p<=2||K||_p` give

```text
||c||_p <= 4 ||J_rho(c)||_p.                           (MC8)
```

The same lift works simultaneously for `p=2,4,6,infinity` and all other
Schatten exponents. If `||c||_6<=kappa||c||_2`, then

```text
||J_rho(c)||_6 <= ||c||_6
   <= kappa ||c||_2 <= 4 kappa ||J_rho(c)||_2.          (MC9)
```

This transfers flatness of the generator cocycle tuple to flatness of
the whole parameter tuple. It does not promise relative flatness of
each parameter matrix separately: a projection or difference can
remove most of an entry's HS mass. The tuple estimate is what the
derivative and repair bounds use.

The map is an admissible parameterization with a uniformly bounded
tangent right inverse. It is not asserted to have a global inverse.
In each fixed dimension one can restrict the parameter space to the
linear subspace `J_rho(Z^1(V,Ad rho))`; the derivative is then an
isomorphism onto the tangent space. The usual fixed-dimensional local
chart statement follows on the corresponding representation stratum.
No uniform normalized-HS inverse-chart radius is claimed or needed.

## 4. Derivatives of unitary exponentials

For anti-Hermitian `H` and anti-Hermitian directions `X_1,...,X_j`,
the mixed derivative of the exponential is

```text
D^j exp(H)[X_1,...,X_j]
 = sum_(sigma in Sym(j)) int_(t_i>=0, sum_(i=0)^j t_i=1)
     e^(t_0 H) X_(sigma(1)) e^(t_1 H) ...
       X_(sigma(j)) e^(t_j H) dt.                    (MC10)
```

The simplex uses its standard `j` independent coordinates and has
volume `1/j!`. This formula follows by differentiating Duhamel's
formula repeatedly; ordering the insertion times gives the displayed
simplexes and permutations. All intervening exponentials are unitary.

If `1/r=sum_i 1/p_i` with `r>=1`, normalized Schatten Hoelder bounds
each integrand by `product_i ||X_i||_(p_i,d)`. There are `j!`
permutations and each integration volume is `1/j!`, so

```text
||D^j exp(H)[X_1,...,X_j]||_r
    <= product_i ||X_i||_(p_i,d).                    (MC11)
```

This also covers the operator norm, taking all exponents infinite,
and the derivatives of `exp(-H)`, with the directions negated. The
bound does not involve `||H||_op`.

## 5. Word derivatives and movement

A generator or its inverse under `(MC1)` has four exponential slots,
separated by fixed unitary matrices. A word of length `ell` therefore
has at most `K=4 ell` slots. Each slot depends on one signed parameter
coordinate. In the mixed `j`th product derivative, assign each of the
`j` labeled directions to a slot. There are `K^j` assignments. A slot
receiving several directions contributes its mixed exponential
derivative. Apply `(MC11)` inside each slot, and Hoelder across the
product. Taking the maximum coordinate norm of each direction gives

```text
||D^j(w o Psi_rho)(H)[X_1,...,X_j]||_r
   <= (4 ell)^j product_i ||X_i||_(p_i),              (MC12)
```

whenever `1/r=sum_i 1/p_i` and `r>=1`. This holds at every parameter
base point. For the Taylor estimates of interest, take `r=2` and
all `p_i=2j`, giving second derivatives controlled by fourth moments
and third derivatives controlled by sixth moments.

Integrating `(MC12)` with `j=1` along `tH` gives

```text
||w(Psi_rho(H))-w(rho)||_p <= 4 ell ||H||_p.           (MC13)
```

For a generator `ell=1`; because the dimensions agree, its normalized
HS distance is exactly its zero-padding distance. In particular the
movement needed in the repair proposal is at most `4||H||_2`.

These are mixed-Schatten estimates. They do not bound a second
derivative by a dimension-independent constant times the product of
two normalized HS norms; the existing rank-one obstruction to that
different assertion still applies.

## 6. Two vertices and the exact part of the Iwahori obligation

Apply the construction independently to both modular vertices of a
pair `pi=(pi_+,pi_-)`. Their central involutions need not agree. The
product parameterization maps every parameter value to a pair of
exact vertex representations, and its linear lift and all tuple
norm bounds retain the same constants.

Let `F` be the Iwahori mismatch after this parameterization. Each
coordinate of `F` is the difference of two fixed words, each of
length at most `L`. Thus

```text
||D^2F(H)[X,Y]||_2 <= 2(4L)^2 ||X||_4 ||Y||_4,
||D^3F(H)[X,X,X]||_2 <= 2(4L)^3 ||X||_6^3.            (MC14)
```

Together with `(MC13)`, this chosen parameterization satisfies the
existence, derivative, and movement clauses `(NQ2)` in
`iwahori-admits-neutral-quadratic-directions`. This asserts nothing
about an arbitrary different parameterization selected in that proposal.
They hold at every exact vertex pair, including pairs with nonzero
Iwahori defect, after any chosen padding by exact vertex blocks.

For completeness, let `A` denote the intrinsic linear mismatch on
the space of pairs of vertex cocycles, and let `T=D Psi(0)` in
right-logarithmic coordinates. Then `T J=I` and the coordinate
linear mismatch is `L=A T`. Hence `ran L=ran A`. If a right inverse
`R_A` for `A` is supplied, then `R=J R_A` is a right inverse for `L`
and `||R||_2<=||R_A||_2`. Flatness of a supplied cocycle correction
also transfers by `(MC9)`. This statement supplies neither the
right inverse for the mismatch nor its dimension-independent bound.

To use this parameterization for quadratic repair would additionally
require flat neutral and linear correction parameters with the stated
projected quadratic cancellation, together with any required padding
whose defect remains `O(e)`. The chart construction gives no such
existence statement, and in particular gives no reason to assume those
parameters exist universally. Operator-norm movement `(MC13)` is an
additional constraint on this particular proposal, even though the
desired final comparison uses normalized HS norm.
In particular an arbitrary inexact block of relative size `O(e)`
can still raise defect to `O(sqrt e)`; all parameter estimates above
start after that separate choice has been made.

The independently checked
`dilution-obstructs-flat-quadratic-iwahori-repair` gives a concrete
limitation: a fixed incompatible character diluted into `n` trivial
coordinates has defect `2/sqrt(n)`, yet any superlinear defect
improvement with bounded relative padding needs operator-norm
movement bounded away from zero. Sixth-flat parameters of HS size
`O(sqrt(e))` have operator norm `O(n^(-1/12))`, contradicting `(MC13)`.
Thus the universal flat-direction proposal fails in this natural
parameterization. Its exact admissibility and derivative bounds remain
valid, and concentrated corrections or different parameterizations
are separate possibilities. The example itself has an exact HS
repair of cost `e`, so it does not obstruct HS stability.

## 7. Repository scope

Searches covered modular-vertex charts, admissible parameterizations,
central-involution splitting, cyclic cocycle averaging, and the
existing Iwahori second-order nodes. The fourth-moment word estimate
already supplies the ambient product differentiation idea, but its
independent generator exponentials do not preserve the vertex
relations. The exact-point integrability proof already gives
fixed-dimensional smoothness. The new content is the explicit
representation-preserving parameterization, the simultaneous
contractive linear lift, and the global mixed-Schatten derivative
bounds that close the previously isolated chart obligation.
