# Prune--double--root iteration: contracting edits, collapsing certified gap

2026-09-20. Proof-only audit of
`research/artifacts/hrf-stability-next-gap-rounding-2026-09-20.md`
and `research/artifacts/hrf-stability-next-single-core-2026-09-20.md`.
Their calculations check out, including the rank-two gap argument,
the reducing-partition factor 2, and the irreducible rounded example.
No correction to those shared files is needed. This note does not
claim a non-RF hyperbolic group or refute finite-order-preserving
modified-core extraction.

The concrete advance is an exact recurrence for the proposed
prune--double--root iteration. Its edits contract, but its certified
gap deteriorates too quickly to iterate to a uniformly gapped,
finite-order result. An explicit order-seven compression also
rules out a superlinear rounding-error estimate that could have
repaired this numerical argument.

## 1. Nearest roots minimize HS distance even among noncommuting competitors

Let `q7` round each circle point to a nearest seventh root. If `Z`
is unitary and `V^7=I` is unitary in the same matrix algebra, then

```
||Z-q7(Z)||_2 <= ||Z-V||_2.                         (1)
```

Diagonalize `Z`, with eigenvalues `z_j`. Write
`V=sum_(k=0)^6 zeta^k E_k`, where `(E_k)` is its spectral PVM.
Every diagonal coefficient `a_jk=(E_k)_jj` is nonnegative and
`sum_k a_jk=1`. Consequently

```
Re Tr(Z* V)
 =sum_j sum_k a_jk Re(conj(z_j) zeta^k)
 <=sum_j max_k Re(conj(z_j) zeta^k)
 =Re Tr(Z* q7(Z)).
```

Since the squared HS distance of two unitaries is twice the
dimension minus twice this real trace, (1) follows. Ties may be
resolved arbitrarily. If `Z` reduces a core, so does `q7(Z)`.

This is stronger than estimating seventh-power defects by word
telescoping and then rounding. In particular, no factor 7 or 49
is needed in the next step.

## 2. The normalized recurrence

Allow `h` generators, since doubling changes their number. Let

```
E_T(X)=(1/(4h)) sum_(t=1)^h ||[T_t,X]||_2^2.
```

Suppose `W` has scalar gap `c>0`, each `V_t` has exact seventh
power one, and put

```
mu=(1/h) sum_t ||W_t-V_t||_2^2.
```

For a projection `p` of trace at most one half, the orthogonal
off-diagonal-block identity gives
`sum_t ||[W_t-V_t,p]||_2^2<=2h mu`. Hence

```
E_V(p) >= (1/2)E_W(p)-mu/2
       >= (c/4)tau(p)-mu/2.                       (2)
```

Use Jihao Liu's pruning lemma with `theta=c/4`, `xi=mu/2`.
For `mu<=c/16`, its one-block construction gives a retained core
of trace `r` and `2h` unitary copies `Z_t^+/-`, with

```
r >= 1-16mu/(7c),
gap(Z|R) >= c^2/1024,
sum_(t,sign) ||Z_t^sign-V_t||_2^2 <= 8h mu/7.     (3)
```

The edit estimate in (3) is in the ambient trace, and includes the
discarded corner. Apply (1) to every ambient pair `Z_t^sign,V_t`.
Restrict to `R`, divide by `r`, and average over the new `2h`
generators. The new exact-order tuple
`Vnew=q7(Z|R)` satisfies

```
mu_new=(1/(2h))sum_(t,sign)
             ||Z_t^sign|R-Vnew_t^sign||_(2,R)^2
       <= (4/(7r)) mu.                            (4)
```

In the admissible regime `mu<=c/16`, (3) gives `r>=6/7`, so
`mu_new<=2mu/3`. Thus the *mean squared edit* really does contract.
The earlier six-generator total-error formulation obscures this
benefit because the number of generators doubles.

But the guaranteed gap obeys

```
c_new=c^2/1024.                                   (5)
```

Using these certified constants repeatedly gives

```
c_j=1024 (c_0/1024)^(2^j).
```

Thus any unbounded number of iterations destroys the available
dimension-independent positive gap. A finite number of passes
does not finish: stopping at the `Z` stage leaves nonexact orders;
stopping at the `q7(Z)` stage leaves no guaranteed scalar gap.
The preceding artifacts prove that the latter gap is not an
automatic consequence of small HS edit, even on actual GHB7
approximate models.

There is also an admissibility problem in the recursively propagated
bounds. Even if we optimistically set every `r=1`, the prescribed
error and gap bounds give

```
(mu_new/c_new)/(mu/c)=4096/(7c).
```

This exceeds one for `c<=1`. Starting with a positive certified
error bound, these numerical bounds eventually leave the condition
`mu<=c/16`. This is a failure of the *available estimates*, not a
proof that the actual error or actual gap follows the worst-case
recurrence.

There is a separate marking issue: this recurrence allows
`h_j=2^j h_0`. It does not identify the growing collection of copies
back with the fixed doubled six-generator GHB7 tuple while keeping
the gap. The numerical obstruction already occurs in this more
permissive, growing-list formulation.

## 3. Changing the pruning threshold does not fix those estimates

The proof of Liu's pruning lemma permits a smaller cutoff
`kappa=rho theta`, with `0<rho<=1/8`. The same first-crossing
argument works under `xi<=theta/8`: if removed mass first reaches
one quarter, its boundary is at most `5kappa/8`, whereas the
original defective expansion gives at least `theta/8`.

After ruling out that crossing, the final removed mass `a` and
boundary `b` obey

```
a <= xi/(theta-kappa),
b <= kappa xi/(theta-kappa).
```

The paired-contraction Cheeger estimate gives gap `kappa^2`.
The doubled edit cost is `16h b`. Substituting the parameters in
(2) and again using nearest-root optimality gives

```
1-r <= 2mu/[c(1-rho)],
c_new = rho^2 c^2/16,
mu_new <= [4rho/((1-rho)r)] mu.                   (6)
```

Taking smaller `rho` improves the edit bound linearly but degrades
the gap quadratically. Even with the optimistic normalization
`r=1`, the ratio of the propagated bounds is multiplied by

```
64/[rho(1-rho)c] >= 256/c.
```

So choosing a tiny cutoff cannot close the same numerical induction.
A successful proof needs an additional mechanism: for example a
gap comparison stronger than the generic Cheeger square, or an
edit estimate with extra smallness not supplied by the boundary
alone. Reusing the original gap as a fixed anchor is not automatic,
because its comparison error is the accumulated distance to the
original tuple, not just the latest contracted rounding error.

## 4. Exact C7 compressions forbid a superlinear boundary-to-rounding estimate

This is an explicit obstruction, not merely unhelpful upper bounds.
Fix `0<alpha<pi/7`, and let `P` be a projection in `M_d`. Put

```
A=I-(1-cos(alpha))P.
```

This positive contraction is a compression of an exact order-seven
unitary. To see this, put `zeta=exp(2pi i/7)` and

```
t=(1-cos(alpha))/(2(1-cos(2pi/7))),
u=(sqrt(1-2t),sqrt(t),sqrt(t)) in C^3.
```

Then `0<t<1/2`, `||u||=1`, and
`u* diag(1,zeta,zeta^-1)u=cos(alpha)`. On `ran(P)` use this
three-dimensional dilation tensor the identity; on `ker(P)` use
the identity. The isometry sending each vector in `ran(P)` to
its tensor with `u` compresses the resulting order-seven unitary
to `A`. The ambient dimension is `d+2rank(P)`.

Liu's two-unitary construction for this positive contraction is
exactly

```
Z^+/-=A +/- i sqrt(I-A^2)=exp(+/- i alpha P).
```

Both round to `I`. The contraction defect and rounding cost are

```
tau(I-A*A)=sin(alpha)^2 tau(P),
sum_sign ||Z^sign-q7(Z^sign)||_2^2
 =4(1-cos(alpha))tau(P)
 =[4/(1+cos(alpha))] tau(I-A*A).                 (7)
```

Take `rank(P)=1` and `d -> infinity`, with alpha fixed. The defect
tends to zero, but the ratio in (7) remains strictly positive
(indeed bigger than 2). Thus no uniform `o(boundary)` or quadratic
boundary-to-rounding-error estimate holds for the polar doubling
of exact C7 compressions. Boundary here is genuinely the dilation
leakage: for the isometry `J` and the ambient unitary `U`,
`|| (I-JJ*) UJ ||_2^2=tau(I-A*A)`, with the norm normalized by
the source dimension.

This example does not impose a full-tuple scalar gap or the actual
pruning selection rule. It refutes the proposed local superlinear
estimate in those variables; it does not refute a more selective
algorithm using additional full-tuple information.

## 5. Audit and boundary of the result

The rank-two construction in the first artifact remains valid:
opposite-copy products recover `Pi(s)^2`, their fourth powers
recover `Pi(s)`, and the exchange kills the only remaining
trace-zero block scalar. The strengthened construction in the
second artifact also checks: its difference-square isolates the
e/f plane, the average reconstructs `Pi(a)`, and the off-diagonal
entry removes the residual two-block commutant. Its upper gap
bound is a Rayleigh quotient, not a claim that all gaps vanish.

Prior-art and duplicate inspection used the established
`defective-block-expansion-prunes-to-doubled-gaps` claim and proof,
Section D of the Liu proof-acceptance artifact, and repository
searches for finite-order pruning and rounding iterations. All
pruning, Cheeger, and two-unitary dilation inputs are credited to
Jihao Liu. The quantitative recurrence and explicit finite-order
compression in this note are proved here; no novelty priority or
new canonical theorem is asserted.

No computation, jobs, commits, or edits of shared artifacts were
performed. A finite-order-preserving modified-core theorem is
still not established. Even such a theorem would leave the
separate noncentral GHB7 relator-correction problem; nothing here
is a full solution of the hyperbolic residual-finiteness question.
