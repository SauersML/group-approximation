# Independent audit of the September 7 logarithmic seed route

Date: 2026-09-07. Scope: the Osgood extraction argument, its logarithmic
specialization, and possible input from the coset hyperlinearity
equivalence. This audit does not prove the arithmetic seed or a
nonhyperlinear group.

## Verdict and precise remaining assertion

No error was found in the finite extraction argument or its stated
logarithmic rates. The missing assertion is exactly a dimension-uniform
bound, for every sufficiently small-defect inverse-compatible SL5 tuple,

```text
lambda_min(Delta_(Q_(2n),U))
 <= B delta(U)^2 log(e/delta(U)^2).
```

The existence of a finite host containing all potential low-energy types
does not establish a low-energy type for the particular approximate tuple.
The extraction proof is conditional on that first vector at the stated
rate, including for every residual tuple it constructs.

## Independently checked estimates

The supporting `sequential-corner-trace-deficiency-proof` is valid as
written. At each polar completion the complementary trace-norm deficiency
is at most the squared retained-column error. In the final real trace
overlap, all occurrences of one deficiency are paired once with the
unitary direct sum of subsequent blocks. This gives the constant-three
squared-error ledger without dependence on the number of cuts.

Writing `x_i=n_i/d`, `A_i=d^(-1) sum_(j<i) xi_j^2 r_j`, and
`y_i=delta_0^2+3 ell^2 A_i`, relator telescoping indeed gives

```text
delta_i^2 <= 2y_i/x_i.
```

For fixed `theta`, every step taken with `x_i>theta` obeys

```text
y_(i+1) <= y_i+3 ell^2 psi(2y_i/theta) r_i/d.
```

The clock `sum r_i/d` is at most one, including the cut that first
crosses the stopping threshold. Since the scalar right side is
nondecreasing, its positive autonomous flow dominates each Euler step.
The divergent Osgood integral makes the time-one value vanish with its
initial value. This is sufficient to verify the residual seed threshold
inductively; it is not assumed while deriving the bound.

The three stopping cases also check out. A small residual costs at most
`3A+4theta`; an exact residual costs at most `3A`; a padded full residual
correction costs at most `6A+2psi(delta_residual^2)` with relative padding
at most `psi(delta_residual^2)`. The last estimate correctly normalizes
the whole corrected tuple by its total padded dimension.

For `psi(t)=K t log(e/t)`, let `C=6K ell^2` and
`L=log(e/delta_0^2)`. The residual clock `sum r_i/n_i` is at most
`1+log(1/theta)`. The scalar solution

```text
Y(t)=e exp(-L exp(-Ct))
```

with `theta=L^(-1/(2C))` is bounded through the last cut by
`e exp(-exp(-C) sqrt(L))`. This divided by theta tends to zero,
so it also proves admissibility of every pre-cut residual. The original
artifact's error `O(L^(-1/(4C)))` and padding
`O(L^(-1/(2C)))` follow. The padding bound is deliberately loose in
the only stopping case that uses padding.

The conversion from the spectral seed to the two extraction alternatives
has the stated constants: for `a=2h epsilon^2/kappa^2<=1/2`,
`xi<=sqrt(h)(1+4/kappa)epsilon` and padding is at most
`4h epsilon^2/kappa^2`.

## What the existing heat estimate would need

This calculation makes the remaining quantitative gap explicit. It is a
consequence of the existing heat theorem, not a proof of new spectral
mass. Let `epsilon_*` and `C_H` be its fixed cutoff and constant, so

```text
N_U(eta)/n >= (3/4)min(N_U(epsilon_*)/n,1)
             -C_H delta^2 log(1/delta)-C_H delta^2/eta^2.
```

Suppose one could prove, uniformly over all the tuples needed for the
seed, a coarse count bound

```text
N_U(epsilon_*)/n >= c/log(e/delta^2)                 (A)
```

with fixed `c>0`. Set `L=log(e/delta^2)` and
`eta^2=B delta^2 L`, choosing `B>=8C_H/c`. At small defect the
minimum term is at least `c/L`, and the last error is at most
`c/(8L)`. Also `C_H delta^2 log(1/delta)<=c/(8L)` for sufficiently
small defect. Thus `N_U(eta)/n>=c/(2L)>0`, proving the missing
logarithmic first-vector estimate under (A).

This locates a weaker coarse-count target than positive limiting density.
But (A) remains unproved. A merely nonzero coarse space can have count
`1/n`, which gives no bound comparable to `1/log(e/delta^2)` without
an additional dimension-versus-defect constraint. The existing heat
argument therefore cannot be invoked to upgrade an arbitrary microscopic
coarse seed to the needed logarithmic seed.

## Why the coset equivalence currently supplies no seed

`binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` identifies
existence of matrix models for seven associated objects. Its tensor-lamp
construction starts from an existing canonical model of a whole wreath
group, changes that model through tensor powers, and produces a relative
conditional expectation. It does not correct the actor lifts into exact
finite-dimensional representations. Its Gaussian construction likewise
preserves a limiting actor action without producing an exact actor lift.

The logarithmic spectral seed requires a map into a genuine finite actor
representation and a bound measured against the defect of the prescribed
input tuple. Neither of those conclusions is in the coset equivalence.
An argument applying it to arbitrary actor tuples would additionally need
to extend those particular tuples to canonical wreath models and retain
quantitative control; that extension is not supplied either.

Consequently the equivalence permits the final nonhyperlinearity
contradiction to be stated using ordinary wreaths, free wreaths, doubles,
HNN groups, or scalar relative embeddability. It presently supplies no new
arithmetic contradiction for the thin co-dense SL5 pair and does not remove
the seed hypothesis. No additional Cairn claim or route has been created
from the elementary conditional count calculation above.

Repository duplicate searches found the earlier linear extraction ledger,
the fixed-cutoff heat transfer, and the new Osgood files. They did not find
the logarithmic coarse-count calculation (A). This is a local search
observation, not a claim of mathematical novelty.
