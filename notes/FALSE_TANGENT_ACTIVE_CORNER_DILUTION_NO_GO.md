# A small active corner cannot dilute tangent-heat covariance defects

Date: 2026-08-12

## 1. Outcome

The tangent-heat endpoint in `notes/NOTEPAD.md` asks for matrix models at
times `t_n->0` whose multiplication and trace errors are `o(t_n)`.  Clifford
central-limit quantization solves the additive lamp law once one supplies a
non-profinite approximate covariance model.

A tempting construction is to realize the required quasi-regular orbit chart
on a small active corner, complete all partial orthogonal maps arbitrarily on
that corner, and add a very large exact representation to dilute the
completion errors.  The following elementary estimate rules this out.

**Theorem 1 (active-corner dilution barrier).**  Let `t_n>0`, `t_n->0`, and
write

```text
C^(D_n)=H_(0,n) directSum H_(1,n),
r_n=dim(H_(1,n))/D_n.                                  (ACD1)
```

Suppose a marked kernel element is represented by

```text
U_n=1_(H_(0,n)) directSum W_n,       W_n unitary.      (ACD2)
```

If, for some `c>0`,

```text
tr_(D_n)(U_n)=1-c t_n+o(t_n),                          (ACD3)
```

then

```text
liminf_n r_n/t_n >= c/2.                               (ACD4)
```

Now suppose one tested multiplication relation has exact inactive block and
active normalized-Hilbert--Schmidt defect `eta_n`; equivalently its full
defect is

```text
Delta_n=0_(H_(0,n)) directSum E_n,
||E_n||_(2,H_(1,n))=eta_n.                             (ACD5)
```

Then

```text
||Delta_n||_(2,D_n)=sqrt(r_n) eta_n.                   (ACD6)
```

Consequently:

1. if `liminf eta_n>0`, then the full defect is `Omega(sqrt(t_n))` and
   cannot be `o(t_n)`;
2. more generally, `(ACD3)` and `||Delta_n||_(2,D_n)=o(t_n)` force

   ```text
   eta_n=o(sqrt(t_n)).                                 (ACD7)
   ```

Thus a large exact summand cannot repair an arbitrary completion of a finite
quasi-regular chart.  The active covariance law must already be accurate at
the square-root heat scale.

## 2. Proof

Equation `(ACD2)` gives

```text
1-tr_(D_n)(U_n)=r_n(1-tr_(H_(1,n))(W_n)).              (ACD8)
```

The normalized trace of a unitary has modulus at most one, so

```text
|1-tr_(D_n)(U_n)| <= 2r_n.                             (ACD9)
```

Taking real parts in `(ACD3)` and using `(ACD9)` yields

```text
c t_n+o(t_n) <= 2r_n,
```

which is `(ACD4)`.

For `(ACD6)`, use the definition of normalized Hilbert--Schmidt norm:

```text
||Delta_n||_(2,D_n)^2
 =Tr(E_n^*E_n)/D_n
 =r_n Tr(E_n^*E_n)/dim(H_(1,n))
 =r_n eta_n^2.                                        (ACD10)
```

If `eta_n>=eta>0` along a subsequence, `(ACD4)--(ACD6)` give

```text
||Delta_n||_(2,D_n)
 >=eta sqrt((c/2-o(1))t_n),                            (ACD11)
```

which is not `o(t_n)`.  In general `(ACD4)` and `(ACD6)` imply

```text
eta_n
 <=||Delta_n||_(2,D_n)/sqrt((c/2-o(1))t_n).
```

If the numerator is `o(t_n)`, the right side is `o(sqrt(t_n))`.  This proves
`(ACD7)`.

## 3. Application to finite orbit charts

Fix a finite multiplication window in the residually finite acting group
`Q` and a finite set of path vectors in `Z[Q/Gamma]`.  One can always form a
finite partial quasi-regular chart on which the selected translations of the
selected vectors are exact, and extend every partial permutation to a
unitary of a finite-dimensional active space.

This gives exact vector covariance on the chosen chart, but arbitrary
completion generally leaves at least one tested quotient multiplication law
with order-one active defect.  Adding an exact representation on
`H_(0,n)` makes the global normalized-HS defect only `O(sqrt(r_n))`.
Theorem 1 shows why this is insufficient for tangent heat amplification:

* retaining the primitive path energy in the trace requires `r_n=Omega(t_n)`;
* tangent amplification requires every global group-law defect to be
  `o(t_n)`;
* hence every active completion defect must be `o(sqrt(t_n))`, not merely
  bounded.

The same argument applies if the inactive summand is any exact
finite-dimensional representation rather than the trivial representation,
provided the marked kernel element is identity there.  It also applies to a
finite direct sum of active charts after replacing `r_n` by their total
relative dimension.

## 4. Relation to Clifford second quantization

There is an additional reason not to regard a small normalized-HS defect of
the underlying orthogonal maps as sufficient.  Clifford second quantization
acts on an algebra of dimension exponential in the real orthogonal
dimension.  A discrepancy supported on even one orthogonal direction can
produce an order-one discrepancy between the induced Koopman implementers.
Therefore diluting the orthogonal defect by appending many trivial real
directions does not establish the implementer estimate `(CCB1)` from the
tangent covariance budget.

The correct positive target is consequently stronger and now quantitative:

> On each growing finite window, construct non-profinite covariance
> implementers whose multiplication errors are `o(t_n)` and whose vector
> covariance errors are `o(sqrt(t_n))`, while the primitive path norm stays
> bounded away from zero.

Qualitative errors can still suffice if they occur in these two different
places before `t_n` is chosen: after obtaining implementer errors
`epsilon_n->0` and vector errors `delta_n->0`, one may pass to a subsequence
and choose `t_n->0` slowly enough that

```text
epsilon_n=o(t_n),       delta_n=o(sqrt(t_n)).          (ACD12)
```

What Theorem 1 excludes is manufacturing `epsilon_n->0` solely through
small-corner dilution while asking that same corner to carry first-order
heat energy.

## 5. Consequence for the FALSE program

The infinitesimal Gaussian/Clifford route remains live, but its remaining
lemma cannot be replaced by a finite partial action plus arbitrary boundary
completion.  Such a construction has exactly the wrong scaling.

Any successful model must spread the covariance correction diffusely as
small angles, or supply a genuinely nonliftable approximate representation
whose active multiplication law already converges before trace dilution.
This is the same multi-directional normalized-HS wall isolated by the
relative-bicommutant and flexible-instability notes.

## 6. Scope after quadratic trace-gap amplification

The barrier above remains correct for the **tangent-heat construction**,
which asks for raw multiplication error `o(t_n)` before taking the heat
limit.  It is no longer the optimal threshold for merely retaining one
marked word in a hyperlinear quotient.

The phase-cancelled tensor amplifier in
`FALSE_ONE_NUMBER_RELATIVE_COMMUTANT_CRITERION.md` only requires

```text
(full multiplication defect)^2
  =o(marked trace gap).                               (ACD13)
```

In the notation of Theorem 1, suppose `r_n` is comparable to `t_n`, the
marked wall has order-one size on the active corner, and the active
multiplication defect is `eta_n`.  Then

```text
marked trace gap asymptotic t_n,
(full multiplication defect)^2=r_n eta_n^2
                                =O(t_n eta_n^2).
```

Consequently `(ACD13)` holds as soon as `eta_n->0`, with no requirement
that `eta_n=o(sqrt(t_n))`.  Arbitrary boundary completion with an
order-one active defect is still excluded, but a shrinking active corner
carrying any genuinely convergent covariance model is again a viable FALSE
input.  Theorem 1 should therefore not be cited as a no-go for such a
model; it only rules out obtaining convergence from dilution alone.
