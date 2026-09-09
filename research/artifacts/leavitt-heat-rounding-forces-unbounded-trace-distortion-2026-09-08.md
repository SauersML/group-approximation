# Native compression forces trace distortion and a diffuse central part in any rounded heat algebra

2026-09-08. Written finite-matrix estimates. No computation, build, or new
Lean verification. This is a conditional obstruction for the same group
`H=L_(F_2)(1,2)^x`; its hyperlinearity remains undecided.

The positive input is
[reversal for finite algebras with controlled trace weights](leavitt-regular-trace-cp-reversal-2026-09-08.md).
The result below applies it to the manuscript's actual compressor. It
identifies an additional sufficient input for nonhyperlinearity and proves
that any successful expectation approximation would have to violate it.

The subsequent
[two-use rounding theorem](leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md)
removes a separate trace-weight or embedding-center premise under
universal heat rounding. Its component selection and native generation
argument make that universal rounding property sufficient by itself.
The finite bounds below remain valid necessary conditions for any
individual rounded native model. Rounding itself is still unproved.

## 1. Fixed native words and quantitative heat estimates

Use the rank-four cell, with `L=EL_3(R)` on the first three coordinates:

```text
u L u^(-1) <= L,
z=diag(1,1,1,1+et) in C_H(L),
y=u z u^(-1)=x_12(e),
ell=x_23(1),       [y,ell]=x_13(e)!=1.
```

Here `z` is the centralizing involution, not the marked order-three
generator. Fix a symmetric list `S` of literal generating words for `L`
containing `ell`, with inverse spellings paired as adjoints. Put `m=|S|`.
For each `s`, fix a word `w_s` over `S` representing `u s u^(-1)` and put
`Lambda=(sum_s |w_s|^2)^(1/2)`. Fix a Kazhdan sum-of-squares certificate
with gap `kappa>0` and residual constant `C`, as in the
[heat-inclusion proof](leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md).

Evaluate the native words on a unitary tuple in dimension `n`, writing
`U,Z,E,V_s` for `u,z,ell,s` and `Y=UZU*`. Suppose the fixed certificate
rows, compressor rows, and commutator rows `[s,z]` have normalized HS
defect at most `epsilon`. Assume also

```text
|tr(Y* E Y E*)| <= xi < 1.                            (1)
```

This is a trace bound on one literal nonidentity native word. It can
be imposed directly in canonical microstates or supplied by the
[single-cycle trace certificate](leavitt-single-c-trace-certificate-2026-09-08.md).
No equality of different word spellings is used in the matrix calculation.

On `L^2(M_n,tr_n)`, define

```text
A=I-(1/m) sum_s Ad(V_s),
P=exp(-t A),       Q=Ad(U) P Ad(U*),       t>0.
```

These maps are self-adjoint, bistochastic, completely positive contractions.
As Hilbert-space operators, `0<=P,Q<=I`. The earlier heat estimate gives

```text
||QP-P||_(infinity -> 2) <= delta_t,

delta_t = Lambda sqrt(2t) exp(-kappa t)
          + Lambda sqrt(C t epsilon/kappa)
          + sqrt(2t) epsilon.                        (2)
```

## 2. A lower bound for reverse inclusion on the native unitary

The commutator rows give

```text
<AZ,Z> <= epsilon^2/2,
||PZ-Z||_2 <= a_t := epsilon sqrt(t/2).               (3)
```

The second inequality uses `(1-exp(-t lambda))^2<=t lambda` for
`lambda>=0`. Consequently `||QY-Y||_2<=a_t`.

The certificate's heat-energy estimate, applied to the unitary `Y`, is

```text
<A PY,PY> <= 2 exp(-2 kappa t) + C epsilon/kappa.
```

Since `ell` occurs in `S`, this implies

```text
||E(PY)E* - PY||_2 <=
 b_t := sqrt(2m (2 exp(-2 kappa t)+C epsilon/kappa)). (4)
```

On the other hand, expanding the norm using (1) gives
`||EYE*-Y||_2>=sqrt(2-2xi)`. Since `||Ad(E)-I||_(2->2)<=2`,

```text
||PY-Y||_2 >= (sqrt(2-2xi)-b_t)_+/2.
```

Finally, `||P-I||_(2->2)<=1` and (3) imply

```text
||PQ-Q||_(infinity -> 2) >= ||PQY-QY||_2 >= chi_t,

chi_t := ((sqrt(2-2xi)-b_t)_+/2 - a_t)_+.            (5)
```

If `epsilon,xi -> 0` and `t=kappa^(-1) log(1/epsilon)`, then
`delta_t -> 0` whereas `chi_t -> 1/sqrt(2)`. All relation lists
used above are fixed once the certificate and native words are fixed;
only the analytic heat time changes with the error.

For a **full canonical microstate sequence**, there is the stronger
asymptotic conclusion

```text
||P_n Y_n||_2 -> 0,
||(P_n Q_n-Q_n)Y_n||_2 -> 1,
||P_n Q_n-Q_n||_(infinity -> 2) -> 1.               (5a)
```

To prove it, pass to any tracial-ultraproduct subsequential limit.
The elements `V_n=P_nY_n` are operator-norm contractions, and (4),
applied to every generator in `S`, makes their limit `V` commute with
the represented `L`. Put `A_0=pi(L)''`. The canonical restriction
identifies `A_0` with `L(L)`, a factor. Therefore the conditional
expectation of `V` onto `A_0` is scalar. The fixed word `Y=pi(y)`
belongs to `A_0` and has trace zero, giving `tau(Y*V)=0`.

Since `0<=P_n<=I`,

```text
||P_nY_n||_2^2 <= <P_nY_n,Y_n> -> 0.
```

The argument applies to every subsequence, so this is ordinary
convergence. Together with `||Q_nY_n-Y_n||_2 -> 0` from (3), it gives

```text
||(P_nQ_n-Q_n)Y_n+Y_n||_2
 <= ||P_nY_n||_2+2||Q_nY_n-Y_n||_2 -> 0.
```

Finally `||P_nQ_n-Q_n||_(infinity->2)<=1`, because `I-P_n` contracts
`L^2` and `Q_n` sends contractions to contractions. This proves (5a).
This sharper conclusion uses full canonical microstates; it does not
replace the explicitly finite hypotheses in (1)-(5).

## 3. Any expectation approximation must pay trace distortion

Let `D` be any unital finite-dimensional subalgebra of `M_n`, and set

```text
eta=||E_D-P||_(infinity -> 2).
```

Write its represented block form and physical trace weights as

```text
D ~= direct_sum_j (M_(a_j) tensor I_(b_j)),
t_j=a_j b_j/n,
R_D = max_j(t_j/a_j^2) / min_j(t_j/a_j^2)
    = max_j(b_j/a_j) / min_j(b_j/a_j) >= 1.          (6)
```

For a matrix factor `R_D=1`. More generally `R_D=1` exactly when
the trace weights are proportional to the squared simple degrees.

Let `F=Ad(U) E_D Ad(U*)`, the expectation onto `UDU*`. Conjugation
gives `||F-Q||_(infinity->2)=eta`. Expanding the three differences,
using `2->2` contractivity on the left and operator-unit-ball
contractivity on the right, gives

```text
||F E_D-E_D||_(infinity->2) <= delta_t+3eta.
```

The finite-algebra reversal theorem then gives

```text
||E_D F-F||_(infinity->2) <= sqrt(2 R_D)(delta_t+3eta).
```

Transferring back to `P,Q` costs another `3eta`. Together with (5),
this proves the necessary inequality

```text
chi_t <= 3eta + sqrt(2 R_D)(delta_t+3eta).            (7)
```

In particular, if `chi_t>3eta` and `delta_t+3eta>0`, then

```text
R_D >= (chi_t-3eta)^2 / (2(delta_t+3eta)^2).          (8)
```

If the denominator vanishes while `chi_t>0`, (7) is impossible.
For the heat time above, an approximation with `eta=O(delta_t)`
therefore requires

```text
R_D = Omega(1/(epsilon log(1/epsilon))).             (9)
```

The implicit constants depend only on the fixed native certificate and
the constant in `eta=O(delta_t)`, and not on matrix dimension.

## 4. Distortion cannot be confined to a vanishing central part

The conclusion can be strengthened using central corners. Let
`p in Z(D)` have `tr(p)=1-s>0`, and let `R_p` be the distortion
of the retained algebra `pDp` in its normalized corner trace.
The central-corner version of the reversal theorem gives

```text
||PQ-Q||_(infinity -> 2)
 <= 3eta + sqrt(2R_p(delta_t+3eta)^2+2(R_p+1)s).      (10)
```

This follows by first comparing the heat maps to `E_D` and its
conjugate, applying the central-corner bound, then comparing back.
It does not require that the native compressor preserve `p`.

For a full canonical microstate sequence, (5a) makes the left side
tend to one. Thus if `eta -> 0` and `R_p<=R_0` for a fixed `R_0`,
the omitted physical trace must satisfy

```text
liminf s >= 1/(2(R_0+1)).                           (11)
```

In particular, an expectation approximation cannot explain away the
large distortion in (8) by confining it to central blocks of vanishing
physical trace. Every central part with uniformly bounded distortion
must omit a definite trace mass, with the stated dependence on its bound.
In particular, a single simple central block has `R_p=1`, so no such
block can have limiting physical trace larger than `3/4`.

### Uniform rounding forces a nonfactorial relative commutant

Let `M=product_omega M_(n)` be the tracial matrix ultraproduct of a
full canonical sequence, and suppose `eta_n -> 0`. Write `D_n` for
the rounded finite algebras. The
[full commutant identification (8b)](leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md)
and uniform rounding give the equality of represented algebras

```text
C := pi(L)' intersect M = product_omega D_n.        (12)
```

Indeed the heat maps fix every bounded representative of an element
of `C` in the ultraproduct, so `E_(D_n)` gives representatives in
`D_n`. Conversely, for contractions in `D_n`, uniform rounding makes
their heat images asymptotically equal to themselves, placing their
ultraproduct in `C`.

Coordinate central projections therefore define central projections
of `C`. In general, if a tracial ultraproduct of finite-dimensional
algebras is a factor, its largest central-block trace must tend to
one along the ultrafilter: otherwise, for some `c>0`, all atoms have
trace at most `1-c` on an ultrafilter-large set. Greedily summing atoms
until their trace first reaches `c/2` gives a central projection with
trace in `[c/2,1-c/2]`, contradicting factoriality.

Here (11), applied to a largest central block at each coordinate,
instead gives `limsup max_j t_(n,j)<=3/4`. More explicitly, choose a
central atom of trace at least `1/4` if one exists; otherwise sum atoms
until their trace first reaches `1/4`, which gives trace below `1/2`.
The resulting central projection in `C` satisfies

```text
1/4 <= tau(p) <= 3/4,    p in Z(C).                 (13)
```

Thus uniform expectation rounding is impossible for a canonical
embedding whose `L`-relative commutant is a factor. This concerns the
full external relative commutant, not the factor `pi(L)''`.

Selecting such an embedding of the entire pair `(H,L)` is an additional
unproved input, and rounding would have to hold for that same embedding.
Even the unrestricted factorial-commutant embedding problem for
embeddable factors into `R^omega` remains listed as
[Problem 37 in the February 2026 problem list](https://arxiv.org/html/2511.20377v2).
An abstract factorial-commutant embedding of `L(L)` would still need
to extend to `L(H)` in the required matrix-ultraproduct target.

## 5. Central block counts and the diffuse central part

The balanced-flow argument in
[the finite-algebra reversal proof](leavitt-regular-trace-cp-reversal-2026-09-08.md)
also gives a bound depending only on the number `k_D` of simple central
blocks of `D`, with no restriction on their degrees or trace weights:

```text
||E_D F-F||_(infinity -> 2)^2
 <= 2 k_D ||F E_D-E_D||_(infinity -> 2)^2.
```

The same heat-to-expectation comparison therefore gives

```text
rho_t := ||PQ-Q||_(infinity -> 2)
 <= 3eta + sqrt(2 k_D)(delta_t+3eta).               (14)
```

Whenever `rho_t>3eta` and the denominator is nonzero, this implies

```text
k_D >= (rho_t-3eta)^2/(2(delta_t+3eta)^2).           (15)
```

If the denominator vanishes, (14) is already a contradiction. For
full canonical microstates, `rho_t -> 1`. Consequently uniform
expectation rounding requires `k_D -> infinity`; if `eta=O(delta_t)`
at the heat time used above, it requires
`k_D=Omega(1/(epsilon log(1/epsilon)))`. This conclusion is separate
from the necessary divergence of the trace distortion `R_D`.

There is a stronger qualitative consequence. For each `n`, order the
central physical weights `t_(n,j)` of `D_n` decreasingly and pad by
zeros. For a free ultrafilter `omega`, set

```text
t_j=lim_omega t_(n,j),          beta=sum_j t_j.
```

The countable-flow extension of the same reversal argument proves
that forward error tending to zero forces reverse error tending to
zero if `beta=1`. Its proof uses the fact that every positive edge of
a countable balanced flow of finite total mass lies on a finite
directed cycle. It does not impose a rate on the tails of the weights.

For a tracial ultraproduct of finite algebras,
`Z(product_omega D_n)=product_omega Z(D_n)`, and `beta` is precisely
the total trace of the atomic part of this center. Applying the
countable-flow theorem to (12), (5a), and the uniform expectation
approximation gives

```text
beta < 1.                                         (16)
```

Thus `Z(pi(L)' intersect M)` has a nonzero diffuse part whenever
these native heat maps admit uniform expectation rounding. A purely
atomic center is excluded, even with infinitely many atoms and no
trace-weight bound. This is stronger than the nonfactoriality
conclusion above. It does not give a universal positive lower bound
on `1-beta`, nor prove the existence of the rounded algebras.

## 6. The missing sufficient input, with its quantifiers

No canonical microstate sequence for `H` can have conditional-expectation
approximations to these heat maps with `eta -> 0` and bounded `R_D`.
More generally (7) excludes approximations satisfying
`sqrt(R_D)(delta_t+3eta) -> 0`.

For full canonical sequences, (5a) sharpens this to
`liminf sqrt(2R_D)(delta_t+3eta) >= 1` whenever `eta -> 0`.

Thus nonhyperlinearity would follow from a theorem guaranteeing such
approximations for a hypothetical canonical microstate sequence of this
same `H`. The guarantee is not proved here. Near idempotence of a heat
map does not by itself identify its range with a matrix subalgebra, and
factoriality of the limiting group trace does not supply the required
coordinate trace weights.

Alternatively, it would suffice to obtain uniform expectation rounding
for an embedding of the entire pair `(H,L)` whose `L`-relative commutant
has purely atomic center. Neither that embedding selection nor that
rounding is established. The nonzero diffuse part forced by (16) is a
necessary feature of a hypothetical rounded model, not a contradiction
to hyperlinearity on its own.

Exact finite-group packets do have regular trace weights under their
canonical traces, including for their commutant algebras. However, they
have not been shown to approximate the full native Kazhdan heat maps
uniformly on the operator unit ball. Replacing that missing assertion
with fixed-word convergence would change the hypothesis and would not
justify applying (7).
