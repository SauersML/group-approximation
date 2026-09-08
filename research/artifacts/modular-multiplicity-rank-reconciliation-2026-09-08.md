# Exact modular multiplicity reconciliation at quadratic rank cost

2026-09-08. Elementary finite-dimensional proof, followed by an
application of the established modular stratum coordinate theorem.
Both comparison representations are supplied. This artifact does
not construct a compatible Iwahori endpoint from a small defect.
No code, build, numerical experiment, or git mutation was used.

## 1. Statement

Let `rho,rho':SL_2(Z)->U(d)` be exact. Use the presentation

```text
SL_2(Z)=<s,b | s^4=1, s^2=b^3>,
S=rho(s), B=rho(b), Z=S^2=B^3,
S'=rho'(s), B'=rho'(b), Z'=(S')^2=(B')^3.
```

The common central matrices `Z,Z'` are self-adjoint involutions.
Write

```text
delta=max(||S-S'||_2,||B-B'||_2),
K=1+2sqrt(3),        C=pi(1+pi)/sqrt(3),                 (MR1)
```

where `||A||_2^2=Tr(A*A)/d`. For generator tuples use maximum
norms and maximum normalized ranks. We prove that there is an
exact `rho_tilde` having the generator multiplicities of `rho'`
and satisfying

```text
rank(S_tilde-S)/d <= 2delta^2,
rank(B_tilde-B)/d <= 3delta^2,
||rho_tilde-rho||_2 <= 2sqrt(3)delta,
||rho_tilde-rho'||_2 <= K delta.                        (MR2)
```

No generator or central multiplicity agreement is assumed.
The construction uses the same `d`-dimensional Hilbert space.

## 2. Spectral separation bounds multiplicity discrepancy

Let `U=sum_lambda lambda P_lambda` and
`V=sum_lambda lambda Q_lambda` be unitaries with spectra in a
fixed finite subset `Lambda` of the unit circle. Zero spectral
projections are allowed. Let its minimum separation be `gamma`.
Define the integer

```text
t(U,V)=(1/2)sum_lambda |rank P_lambda-rank Q_lambda|.
```

This is the number of labels that must be changed to turn one
eigenvalue multiplicity vector into the other. Put
`a_(lambda,mu)=Tr(P_lambda Q_mu)`. These numbers are nonnegative,
their row sums are `rank P_lambda`, and their column sums are
`rank Q_mu`. In particular

```text
sum_lambda a_(lambda,lambda)
    <= sum_lambda min(rank P_lambda,rank Q_lambda)
     = d-t(U,V).
```

Expanding the squared unnormalized HS distance gives the exact
identity and ensuing bound

```text
d||U-V||_2^2
 = sum_(lambda,mu) |lambda-mu|^2 a_(lambda,mu)
 >= gamma^2 sum_(lambda!=mu) a_(lambda,mu)
 >= gamma^2 t(U,V).                                   (MR3)
```

For `S,S'` the allowed spectrum is `{1,i,-1,-i}` and
`gamma=sqrt(2)`. For `B,B'` it consists of the sixth roots of
unity and `gamma=1`. Hence, writing `t_S=t(S,S')` and
`t_B=t(B,B')`,

```text
t_S <= d delta^2/2,        t_B <= d delta^2.             (MR4)
```

Let

```text
k=|dim ker(Z-I)-dim ker(Z'-I)|.
```

The positive multiplicity of `Z` is the sum of the `S` labels
whose squares are `1`, and also the sum of the `B` labels whose
cubes are `1`. Taking a marginal of two equally sized
multiplicity vectors cannot increase their half-L1 distance.
Explicitly the absolute discrepancy in any subset of labels is
at most the sum of all positive discrepancies, which equals
that half-L1 distance. Therefore

```text
k <= min(t_S,t_B).                                    (MR5)
```

These bounds use no alignment of the eigenspaces.

## 3. Change the central sign on one common subspace

If `k=0`, skip this section and set `S_1=S`, `B_1=B`, `Z_1=Z`.
Otherwise let `epsilon in {1,-1}` be the central sign having
excess multiplicity in `Z` compared with `Z'`. Choose any
`k`-dimensional subspace

```text
F <= ker(Z-epsilon I).
```

There is enough room because that eigenspace has at least `k`
excess dimensions. We will make `F` a common reducing subspace
for the two modified generators and reverse its central sign.
It need not reduce the original generators.

We use one construction for `U=S,m=2` and for `U=B,m=3`.
Both generators preserve the original central-sign spaces, and
on `ker(Z-epsilon I)` they obey `U^m=epsilon I`. Their cyclic
spans of `F` are

```text
W_U=F+UF+...+U^(m-1)F,
k <= dim W_U <= mk.                                   (MR6)
```

The relation `U^m=epsilon I` shows `UW_U=W_U`; unitarity then
makes `W_U` reducing. It lies wholly in the sign-`epsilon`
space. Its original eigenvalues satisfy `lambda^m=epsilon`.

Write their multiplicities in `U|W_U` as `n_lambda`. Choose
integers `0<=a_lambda<=n_lambda` with
`sum_lambda a_lambda=k`; this is possible because
`dim W_U>=k`. Define a replacement `U_1` as follows:

- On `W_U^perp`, keep `U_1=U`.
- On `F`, let `U_1` be any scalar root of
  `lambda^m=-epsilon`, repeated `k` times.
- On `W_U intersect F^perp`, choose an orthogonal spectral
  decomposition with eigenvalue multiplicities
  `n_lambda-a_lambda`, all satisfying `lambda^m=epsilon`.

The last multiplicities sum to `dim W_U-k`, so they can be
realized on that space. These three spaces are orthogonal and
sum to the whole Hilbert space. The replacement is unitary;
it differs from `U` only on `W_U`, and its eigenvalue
multiplicity vector is obtained by changing exactly `k`
labels from central sign `epsilon` to central sign
`-epsilon`. Consequently

```text
rank(S_1-S) <= 2k,          t(S_1,S) = k,
rank(B_1-B) <= 3k,          t(B_1,B) = k.               (MR7)
```

Although `W_S` and `W_B` may differ, the powers of the
replacements agree on the entire space:

```text
S_1^2=B_1^3=Z_1=Z-2epsilon P_F.                       (MR8)
```

Indeed, each replacement reverses its power only on the same
space `F`, retains the old central sign on `W_U intersect
F^perp`, and is unchanged on `W_U^perp`. Since `F` is in an
eigenspace of `Z`, `(MR8)` is again a self-adjoint involution.
Thus `S_1^4=B_1^6=I`, and the vertex relations hold exactly.
By the choice of `k` and `epsilon`, `Z_1` and `Z'` have
identical positive and negative multiplicities.

This is the required compatibility step. The finite cyclic
spans permit the generators to be modified on different small
spaces while changing their central powers on one identical
space. It does not require a small common reducing summand of
the original representation.

## 4. Relabel within the two common central spaces

Since `S_1^2=B_1^3=Z_1`, each spectral subspace of either
generator lies in the central sign determined by its label.
For each central sign, its total dimension now equals the
corresponding dimension for the target `rho'`.

Within each sign space, change surplus eigenvalue labels to
deficit labels, preserving an orthonormal eigenbasis of the
generator being changed. This produces `S_tilde` with the
same multiplicities as `S'`, and independently `B_tilde` with
the same multiplicities as `B'`. Every new label stays within
its central sign. Therefore

```text
S_tilde^2=B_tilde^3=Z_1
```

still holds exactly. There are no further relations between
`s` and `b` in the amalgam presentation, so these matrices
define an exact modular representation `rho_tilde`.

The relabeling rank is exactly the number of labels changed.
The half-L1 distance is a metric on multiplicity vectors;
using `(MR7)` gives

```text
rank(S_tilde-S_1)=t(S_1,S') <= t_S+k,
rank(B_tilde-B_1)=t(B_1,B') <= t_B+k.                  (MR9)
```

The total relabeling is possible separately in the sign
spaces because their source and target totals agree. Thus
there is no extra transportation cost hidden in `(MR9)`.
Combining the ranks in `(MR7)` and `(MR9)` gives the more
precise estimates

```text
rank(S_tilde-S) <= t_S+3k <= 4t_S <= 2d delta^2,
rank(B_tilde-B) <= t_B+4k <= t_B+4t_S <= 3d delta^2.    (MR10)
```

For unitaries, every singular value of their difference is at
most `2`, so

```text
||U-V||_2 <= 2sqrt(rank(U-V)/d).                      (MR11)
```

Equations `(MR10)` and `(MR11)` prove the movement bound in
`(MR2)`; its last bound follows by the triangle inequality.
The case `delta=0` is handled by taking `rho_tilde=rho=rho'`.
In fact the construction works for every `delta`, with no
smallness threshold.

## 5. Coordinates and exact operator/rank factorization

The established claim
`modular-strata-have-linear-coordinates-and-rank-splits`,
with full proof in
`research/artifacts/modular-stratum-coordinate-coverage-2026-09-08.md`,
says that two exact modular representations with matching
generator multiplicities can be joined by the natural chart
with parameter HS norm at most `C` times their generator HS
distance. Applying it to `rho_tilde,rho'` gives parameters
with norm at most `CK delta`. This is a globally chosen
coordinate tuple, not a continuous or unique inverse chart.

For an operator/rank factorization starting at the original
`rho`, first reverse the roles of the endpoints in Sections
2--4. This yields an exact `rho_hat` with the multiplicities
of `rho` and

```text
max_g rank(rho_hat(g)-rho'(g))/d <= 3delta^2,
max_g ||rho_hat(g)-rho(g)||_2 <= K delta.              (MR12)
```

Choose natural chart parameters `H` at `rho` reaching
`rho_hat`, with `||H||_2<=CK delta`. The prerequisite proves
that truncating each anti-Hermitian parameter spectrally at
`theta>0` preserves the central commutation or anticommutation
conditions, hence preserves exact vertex relations. Its
resulting exact representation `rho_lo` satisfies

```text
max_g ||rho_lo(g)-rho(g)||_op <= 4theta,
max_g rank(rho_lo(g)-rho_hat(g))/d
    <= 4C^2 K^2 delta^2/theta^2.                      (MR13)
```

Adding `(MR12)` and `(MR13)` in rank proves

```text
max_g rank(rho_lo(g)-rho'(g))/d
    <= 3delta^2+4C^2 K^2 delta^2/theta^2.              (MR14)
```

Thus the exact intermediate operator/rank factorization
extends to all multiplicity strata, with a discrete surgery
before the coordinate step. For `theta=sqrt(delta)>0`, the
operator movement is `4sqrt(delta)` and the normalized-rank
movement is at most `3delta^2+4C^2 K^2 delta`, which tends to
zero. For `delta=0` use the constant intermediate.

## 6. What this proves for Iwahori pairs

Apply the construction separately to the two modular
vertices and take maximum norms. All estimates and constants
remain unchanged. Suppose the second pair is a supplied
compatible pair, and `delta` is the generator HS distance to
it. Then the first pair can be replaced by an exact vertex
pair in that comparison pair's generator multiplicity
stratum, at movement at most `2sqrt(3)delta`.

For any fixed word `w` of length `ell`, unitary telescoping
gives

```text
||w(rho_tilde)-w(rho)||_2 <= ell ||rho_tilde-rho||_2.
```

The same estimate holds for inverse letters because
`U^*-V^*=-U^*(U-V)V^*`. For a compatibility residual
`R=w_1-w_2`, let `L` be the sum of the two word lengths.
Then

```text
||R(rho_tilde)-R(rho)||_2 <= 2sqrt(3)L delta.           (MR15)
```

Taking the maximum over the finitely many Iwahori rows also
bounds the change in the scalar defect by a dimension-free
constant times `delta`. Consequently, as `delta->0`, both
the pair movement and its defect change are `o(1)`.

This proves the literal qualitative bookkeeping assertion
in `iwahori-torsion-multiplicity-stratum-reconciliation`
when a nearby compatible comparison pair in the same
dimension is supplied: the resulting pair and that unchanged
comparison point lie in one multiplicity stratum. The
additional assumption there that the multiplicity discrepancy
is `o(d)` is automatic from `(MR3)` when `delta->0`.

Several stronger statements do not follow:

- The new pair need not itself be compatible. Equation
  `(MR15)` controls its defect but does not make it vanish.
- The argument uses the supplied endpoint distance `delta`.
  A small defect by itself does not supply that endpoint, or
  prove `delta=O(defect)`. Thus this proof does not establish
  the optional defect-proportional strengthening proposed in
  the old claim.
- The within-stratum normalized-HS Newton argument remains
  invalidated by
  `normalized-hs-taylor-remainder-is-not-dimension-free`.
  Finding a common stratum does not fix its Taylor estimate.
- If only a larger-dimensional compatible comparison is
  known, this theorem applies after a specified exact padding
  and in that common dimension. It supplies no padding budget
  and no same-dimensional compatible comparison point.
- Each intermediate is exact at each modular vertex. Neither
  the surgery nor the parameter truncation is asserted to
  preserve Iwahori compatibility between vertices.

In particular there is no conflict with a deleted-line
flexible-versus-strict stability example: such an example
does not provide the nearby exact compatible endpoint in
the original dimension required here.

## 7. Necessary discrete cost and sharp scale

Let `rho` be the `d`-dimensional trivial representation, and
let `rho'` be the direct sum of `d-1` trivial characters and
the character

```text
chi(s)=-1,       chi(b)=1.
```

This is a modular character because `chi(s)^4=1` and
`chi(s)^2=chi(b)^3=1`. Here `delta=2/sqrt(d)`. Any exact
intermediate with the `S` multiplicities of `rho'` has one
`-1` eigenvalue, and therefore its `S` difference from `I`
has rank at least `1`. Its normalized rank is at least
`1/d=delta^2/4`, its normalized HS distance from `I` is
`delta`, and its operator distance from `I` is `2`.

Thus the quadratic normalized-rank scale and linear HS
scale are optimal up to constants, and a universal small
operator-norm multiplicity change is impossible. Natural
modular chart maps alone also cannot cross this example's
strata: they conjugate each generator and hence preserve its
spectrum with multiplicity. The discrete rank leg is
essential; it is precisely what the surgery supplies.

The rank estimates do not imply support in a common reducing
summand for the original representation. The construction
uses different finite cyclic spans for the two generators,
followed by separate relabelings inside the common central
spaces. Nor does the factorization assert a uniformly flat
Schatten parameter tuple. These restrictions retain the
scope of the existing concentration obstructions.

## 8. Repository relation and proof dependencies

Repository searches covered modular and Iwahori multiplicity
strata, spectral relabeling, finite-spectrum rank bounds,
and cyclic-span surgery before this claim was written. The
existing stratum coordinate theorem assumes matching
multiplicities and explicitly leaves unequal multiplicities
untreated. Sections 2--4 here remove that hypothesis with a
complete central-compatible construction; Section 5 then
imports that theorem's coordinate and truncation conclusions.
No literature priority claim or external theorem is needed
for the finite-dimensional surgery proof.
