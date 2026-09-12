# Audit: arbitrary finite-factor weighted loop fillings

## Scope checked

This audit checks the passage from projection-weight loop fillings to
arbitrary positive weights in a separable `II_1` factor.  Matrix factors
are included to verify that the same argument and constants apply there.

## Potential discontinuities

* The full polar frame `x b^(-1/2)` is never used.  On each fixed band
  `r_n`, the inverse `b^(-1/2)r_n` is bounded, so the boundary band frame is
  genuinely `2`-continuous.
* No moving spectral projection is selected.  The `r_n` are fixed spectral
  projections of the fixed fibre weight `b`.
* No arbitrary disk field of projections is trivialized.  The initial
  high complement has a unitary trivialization furnished by the lifted
  high filling, and formula `(UL4)` explicitly propagates a trivialization
  after every finite band.
* The countably many unitary trivializations need not converge.  Only the
  orthogonal weighted sums converge, uniformly by `(UL7)`.

## Unitary-lift check

For matrices, a Stiefel filling over `D^2` pulls back the ordinary
principal unitary bundle; contractibility of `D^2` gives a section.  For a
diffuse nonquantitative filling, Farah--Vaccaro lifts the boundary loop and
Jekel contracts the lifted unitary loop.  For the quantitative diffuse
filling, the localized formula

```text
B=a(f_0+cR_0)a^*
```

is unitary and satisfies `Bq=a(f_0+cw_0)a^*`; the controlled annulus is
already implemented by left unitaries `D(z,t)`.  On the common circle the
formula `C(z,t)=D(z,t)D(z,1)^*B(z)` glues the disk lift to an annulus lift
without changing a single projected frame, so metric control is untouched.
In the whole-source alternative, any lifted nonquantitative filling obeys
the predecessor bound because the entire Stiefel space has the required
small `2`-diameter.  Thus metric control and the lift are simultaneously
available.  The complementary projection must be
nonzero only in the matrix case; strict total support slack supplies this.

## Algebraic and metric checks

The multicopy-to-one-frame identification has exact Hilbert-sum metric.
At every band the remaining target trace exceeds the trace of the next
combined source by at least the final strict slack.  Orthogonality makes
the squared tail norm exactly the scalar spectral tail in `(UL7)`, and
bounded `L^2` convergence preserves the source and range equations in
`L^1`.  More explicitly, the finite weighted band sums have norm at most
`sqrt(eta)`, hence their `L^2` limits lie in `N`; the finite identities
`X_(j,k)^*X_(j,k)=b sum_(n<=k)r_n` and
`X_(i,k)^*X_(j,k)=0` pass to `L^1`.  Therefore the limits have exact source
`b` and exact pairwise range orthogonality.  The low piece costs at most
`2sqrt(m tau(b))`; for
`b=ap_l<=eta p_l`, this is at most `2sqrt(eta)`.

With `eta=(epsilon_0/12)^2` and the projection Stiefel modulus
`rho_St(t)=min(t,1)^2/2560`, the admissible weighted radius is

```text
sqrt(eta) rho_St(epsilon_0/3)
= (epsilon_0/12)(epsilon_0^2/(9*2560))
= epsilon_0^3/276480.
```

The high and low radii are at most `epsilon_0/3` and `epsilon_0/6`.

## Conclusion

The relative positive-weight extension is unconditional for loops in every
normalized matrix factor and every separable `II_1` factor under strict
total support slack.  The proof does not establish higher-sphere filling
in arbitrary `II_1` factors and makes no claim without strict slack.
Global simple connectivity uses the same relative theorem directly with
`b=a`, `eta=1`, and constant moving complement `g=1`; the bands cover all
of `(0,1]`, and strict slack leaves room at every finite recursive stage.

For a countably generated factorial bundle, stabilization embeds every
fibre `L^2` space in `ell^2`, so all factor fibres have separable predual.
The predecessor correction lemma supplies lower semicontinuity, while this
theorem supplies simple connectivity and uniform equi-`LC^1` (the maximum
and Hilbert-sum tuple metrics are bi-Lipschitz for each fixed replication
number).  For an arbitrary ambient centre in the maximum tuple metric, use
`2sqrt(m)delta<=rho(epsilon/2)` and `delta<=epsilon/2`; choosing a loop point
as the fibre centre then keeps the fill in the desired ambient
`epsilon`-ball.  Thus the degree-one Michael theorem applies over bases of
dimension at most two.  This consequence does not extend to dimension three:
uniform fillings of `2`-spheres in arbitrary finite factors remain open.
