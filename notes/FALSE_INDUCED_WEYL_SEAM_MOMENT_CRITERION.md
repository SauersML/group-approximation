# An induced Weyl seam is controlled by two Schreier moments

Date: 2026-08-11

## 1. Outcome

The local Weyl branch cut from
`FALSE_CLOCK_POSITIVE_WEYL_SEAM.md` extends to a permutation bundle with
nonconstant transition labels.  The extension requires no operator
optimization.  Its normalized Hilbert--Schmidt error is bounded by two
scalar moments of the transition coordinates.

Let

`A_M=(Z/M Z)^2`, `zeta=exp(2 pi i/M)`,

and use the Weyl multiplier

`Omega((r,a),(r',a'))=zeta^(a r')`.                  `(IWS1)`

Suppose a fixed generator of a finite permutation bundle has, over a base
point `x`, transition coordinate

`v_x=(r_x,a_x) in A_M`.                              `(IWS2)`

Choose centered integer representatives and put

`R^2=(1/|X|) sum_x |r_x|^2`,
`A=(1/|X|) sum_x |a_x|`.                             `(IWS3)`

There is an explicit block-diagonal seam gauge for which the squared
normalized Hilbert--Schmidt discrepancy between the Weyl-twisted and
ordinary bundle operators is at most

`8 pi^2 (L^2/M^2) R^2+8 A/L`                        `(IWS4)`

for every divisor `L|M`.  If `M=p^k`, choosing the nearest `p`-power to the
continuous optimum gives

`error^2 <= C_p (R A/M)^(2/3)`                       `(IWS5)`

when `R,A` are nonzero and the optimum lies away from the endpoints.  The
endpoint regimes require separate control.

For one transition family, a seam width with vanishing bound exists exactly
when

`R_k=o(M_k), A_k=o(M_k), R_k A_k=o(M_k).`            `(IWS6)`

For finitely many fixed generators, the same three conditions must hold for
the separate maxima `R_* = max_s R_s` and `A_* = max_s A_s`.  The product
condition alone is not sufficient when one moment approaches zero while the
other remains linear in `M`.

This is strictly weaker than requiring every transition coordinate to be
bounded.  In the common case in which the coefficient coordinate has
bounded RMS, it is enough that the centered stable-letter exponent have
mean absolute value `o(M_k)`.

The theorem does not prove that the natural Kun--Thom Schreier bundles
satisfy `(IWS6)`.  It identifies the exact quantitative globalization gate.
The local order-`p` Bockstein holonomy is unchanged by the block-diagonal
gauge, so `(IWS6)`, together with the already proved clock transport, would
complete the phase-splitting construction.

## 2. The one-fiber seam

Let `lambda` be the ordinary left regular representation of `A_M`, and let
`lambda_Omega` be the twisted left regular representation associated to
`(IWS1)`.  Write

`e_1=(1,0)`, `e_2=(0,1)`.                            `(IWS7)`

Choose a divisor `L|M`.  For `0<=s,t<M`, define

`f(t)=t mod L in {0,...,L-1}`,
`b(s,t)=zeta^(-s f(t))`,                              `(IWS8)`

and let `W_L` be the diagonal unitary with diagonal `b`.  The elementary
calculation gives

`||W_L lambda_Omega(e_1) W_L^*-lambda(e_1)||_2^2`
` <=4 pi^2 L^2/M^2`,                                 `(IWS9)`

`||W_L lambda_Omega(e_2) W_L^*-lambda(e_2)||_2^2`
` <=4/L`.                                            `(IWS10)`

We need the nonuniform power version.  Use the canonical lift

`T_Omega(r,a)=lambda_Omega(e_1)^r lambda_Omega(e_2)^a`,
`T(r,a)=lambda(e_1)^r lambda(e_2)^a`.                 `(IWS11)`

Changing the order in `(IWS11)` changes only the familiar central Weyl
scalar.  In an application, `(IWS11)` is the chosen section of the central
extension.

**Lemma 1 (power seam estimate).**  For centered representatives
`|r|,|a|<=M/2`,

`||W_L T_Omega(r,a) W_L^*-T(r,a)||_2^2`
` <=8 pi^2 r^2 L^2/M^2+8 |a|/L`.                    `(IWS12)`

**Proof.**  For the first coordinate, direct use of `(IWS8)` shows that the
coefficient ratio on the row with second coordinate `t` is

`zeta^(-r f(t))`.                                    `(IWS13)`

Its distance from one is at most `2 pi |r|L/M`, proving the squared first
term with constant `4 pi^2`.

For the second coordinate, the gauge cancels the Weyl phase whenever the
path from `t` to `t+a` does not cross an `L`-block seam.  If `|a|<L`, the
fraction of starting rows which cross a seam is at most `|a|/L`.  If
`|a|>=L`, the trivial fraction bound one is still at most `|a|/L`.
Every squared chordal error is at most four, so

`||W_L lambda_Omega(e_2)^a W_L^*-lambda(e_2)^a||_2^2`
` <=4 |a|/L`.                                        `(IWS14)`

Insert the intermediate product in `(IWS11)` and use unitary invariance and
the triangle inequality.  Squaring the sum and using
`(u+v)^2<=2u^2+2v^2` gives `(IWS12)`.  End proof.

The use of `|a|`, rather than `a^2`, is load bearing.  A long vertical move
only sees the density of block seams it crosses.  Telescoping the unit-step
estimate would lose this improvement.

## 3. Permutation bundles

Let `X` be a finite set.  Give every `x in X` a copy `H_x` of
`ell^2(A_M)` and put

`H_X=directSum_(x in X) H_x`.                         `(IWS15)`

Fix a permutation `sigma` of `X`.  Define ordinary and twisted monomial
operators `U,V` from `H_x` to `H_(sigma x)` by the fiber maps

`U|H_x=T(r_x,a_x)`,
`V|H_x=T_Omega(r_x,a_x)`.                             `(IWS16)`

Let

`mathcal W=directSum_(x in X) W_L`.                   `(IWS17)`

The permutation of the fibers is the same in `U` and `V`, and the same seam
gauge is used on every fiber.  Therefore the squared normalized
Hilbert--Schmidt norm is exactly the average of the squared fiber errors:

`||mathcal W V mathcal W^*-U||_2^2`
` =(1/|X|) sum_x`
`   ||W_L T_Omega(r_x,a_x)W_L^*-T(r_x,a_x)||_2^2.`   `(IWS18)`

**Theorem 2 (two-moment bundle bound).**  With `(IWS3)`, inequality
`(IWS4)` holds.

**Proof.**  Average `(IWS12)` over `x` and use the definitions in `(IWS3)`.
End proof.

This statement remains true with unequal fiber multiplicities after
replacing the averages by their dimension weights.  It also remains true
for a direct sum of several bundle orbits, for the same reason.

## 4. Optimization at prime-power order

Assume `M=p^k`.  Ignoring constants, the right side of `(IWS4)` has the
form

`R^2 L^2/M^2+A/L`.                                   `(IWS19)`

When `R,A>0`, its continuous minimizer has scale

`L_*=(A M^2/R^2)^(1/3)`.                             `(IWS20)`

Choose a divisor `L=p^ell` within a factor `p` of `L_*`, clipped to
`[1,M]`.  Substitution in `(IWS4)` gives `(IWS5)` with a constant depending
only on `p`.

In the interior regime `R,A>=1`, the product condition `RA=o(M)` implies
both separate sublinearity conditions.  Then `(IWS20)` tends to infinity and

`L_*/M=(A/(R^2 M))^(1/3)=o(1)`.                      `(IWS21)`

Thus clipping is eventually unnecessary and `(IWS5)` tends to zero.

The endpoint conditions are load bearing.  If `R=0`, taking `L=M` makes
`(IWS4)` equal to at most `8A/M`, which vanishes exactly under `A=o(M)`.
If `A=0`, take `L=1`; the actual first-coordinate formula `(IWS13)` gives
squared error at most `4 pi^2R^2/M^2`, which requires `R=o(M)`.  More
generally, the endpoint audit proves that some allowed `p`-power seam makes
`(IWS19)` vanish if and only if all three conditions in `(IWS6)` hold.

Necessity follows directly from `1<=L<=M`:

`R/M <= RL/M`, `A/M <= A/L`,

and

`RA/M=(RL/M)(A/L)`.

The sufficiency proof uses the interior optimizer when it lies in `[1,M]`
and `L=1` or `L=M` in the two clipped regimes.  See
`FALSE_INDUCED_WEYL_SEAM_ENDPOINT_AUDIT.md` for the complete case split.

For a finite generating set, put `R_*=max_s R_s` and `A_*=max_s A_s` and
apply `(IWS6)` to this pair.  Choosing one `L_k` from these maxima makes the
same block gauge work for all generators simultaneously.  Checking only the
individual products is insufficient because different generators can force
opposite endpoint choices.

## 5. Shapiro specialization

For the finite clock construction, write a Schreier transition in
metacyclic normal form as

`beta_tau(x,s)=h^(a_tau(x,s)) c^(t_tau(x,s)).`        `(IWS22)`

The explicit mixed cocycle evaluates the transition through a Weyl
coordinate.  After choosing the finite induced-module generators, denote
the other, coefficient coordinate by `r_tau(x,s)`.  Define

`R_(s,k)^2=(1/|X_k|)sum_x |r_tau(x,s)|_(M_k)^2`,
`A_(s,k)=(1/|X_k|)sum_x |a_tau(x,s)|_(M_k)`.          `(IWS23)`

Changing the Schreier transversal changes these coordinates by the twisted
gauge law proved in `FALSE_MIXED_LHS_COCYCLE_FORMULA.md`.  Thus the useful
invariant is the infimum of the right side of `(IWS4)` over transversals,
followed by the choice of `L`.

**Corollary 3 (induced clock seam criterion).**  Suppose transversals can be
chosen so that, with `R_(s,k),A_(s,k)` as in `(IWS23)` and maxima over the
fixed positive generating set,

`R_(*,k)=o(M_k)`,
`A_(*,k)=o(M_k)`,
`R_(*,k) A_(*,k)=o(M_k)`.                             `(IWS24)`

Then the Weyl-twisted and ordinary induced clock sectors become equal in
normalized Hilbert--Schmidt norm on every fixed positive word.

**Proof.**  Apply Theorem 2 simultaneously to the finite generating set and
then use the unitary telescoping inequality for fixed words.  End proof.

The macroscopic clock holonomy is gauge invariant.  If the growing fold
collision represents the Bockstein power

`u_k p^(k-1) kappa_k`, `p` not dividing `u_k`,        `(IWS25)`

then the primitive clock character evaluates it as

`exp(2 pi i u_k/p)`,                                  `(IWS26)`

which stays a fixed positive distance from one.  Hence `(IWS24)`, together
with the already established finite clock transport into the vertex
models, supplies the edge-matching part of the phase-splitting criterion.

## 6. What has and has not been proved

The local Fourier calculation and its induction across arbitrary
permutation fibers are now closed.  The remaining task is finite and
scalar:

1. choose the Shapiro transversals;
2. compute the two centered moments `(IWS23)` for the fixed positive
   generators; and
3. prove all three limits in `(IWS24)` without destroying the fold value
   `(IWS26)`.

A bounded transition coordinate is sufficient but unnecessary.  The exact
threshold permits a sparse set of macroscopic transitions, as long as their
mean seam-crossing contribution is sublinear after coupling to the RMS
coefficient coordinate.

Property `(T)` rules out some globally cohomologically nontrivial regular
seams, as recorded in the older finite-image descent theorem.  It does not
invalidate Theorem 2: failure must appear quantitatively as the impossibility
of `(IWS24)` for the actual Shapiro transition system.  Thus `(IWS24)` is
also the precise statistic on which a no-go theorem would have to place a
linear lower bound.
