# An exact primal/dual test for local syndrome proposals

This note follows the joint-support audit. It gives a finite synthesis
criterion, a direct proof of a separating-certificate inequality, and
matching positive and negative certificates for the paired-projector
examples. It supplies no polynomial-time QMA reduction, uniform-cost
amplifier, or proof of quantum PCP. The tools are elementary POVM dilation
and semidefinite weak duality; no novelty claim is made for those tools.

## 1. Fix the instance and all energy neighborhoods

Let `h_1,...,h_m >= 0` act on a nonzero finite-dimensional space of dimension
`D`. For every term label `a`, fix a neighborhood `N(a) subset [m]` and set

```text
A_a = sum_(b in N(a)) h_b.
```

Let `F` be the feasible fault sets:
`S in F` if and only if `intersection_(b not in S) ker h_b != {0}`.
An empty intersection denotes the entire input space. Fix `C_0 >= 0`.

The following is a semidefinite feasibility problem in matrices `E_S`:

```text
E_S >= 0,                           for every S subset [m],
sum_S E_S = I,
E_S = 0,                            for S not in F,
sum_(S containing a) E_S <= C_0 A_a, for every a.             (Primal)
```

All inequalities refer to operators on the same original input space.
The last line uses marginal flag effects `F_a`. It is the third line,
on the **joint** effects, that prevents the false empty-syndrome example.

## 2. Necessary and sufficient, before physical implementation constraints

**Theorem 1.** (Primal) is feasible if and only if there exists an exactifying
instrument whose marginal fault effects obey `F_a <= C_0 A_a` on every
input. Here the instrument and recovery may be arbitrary finite-dimensional
channels; no geometry, efficiency, or preservation of a logical algebra is
asserted.

**Proof, necessity.** An instrument's effects are a normalized POVM.
The fixed-measurement support theorem implies `E_S=0` for infeasible labels,
since such a label cannot be followed by an exact normalized state. The
assumed marginal inequalities are the last line of (Primal).

**Proof, sufficiency.** From a feasible POVM, the isometry
`Wv=sum_S |S> tensor sqrt(E_S)v` and the commuting syndrome-bit projectors
realize its joint effects. For each feasible `S` choose a unit vector from
the common kernel of the retained terms. Conditioned on the measured label,
prepare this vector on the original input space. This is an exactifying
instrument by `joint-syndrome-support-characterizes-exactifiability`, and
its marginals are the matrices in the last line of (Primal).

If each energy term occurs in at most `R` neighborhoods, summing gives

```text
E|S| = Tr[(sum_a F_a) rho]
     <= C_0 Tr[(sum_a A_a) rho]
     <= C_0 R sum_b Tr(h_b rho).
```

Thus the unrestricted rounder constant is at most `C_0 R`. If `W` is
already given by a physical proposal, use that proposal's actual joint
effects and Theorem 1's recovery argument; do not substitute a different
dilation without checking its geometry and logical action.

**Size and implementation boundary.** This SDP has up to `2^m` effects,
each acting on dimension `D`, and determining feasible labels uses global
common kernels. In a qudit system `D` itself is exponential in the number
of sites. The statement is a finite audit criterion, not an efficient
synthesis algorithm. Feasibility does not imply a bounded-horizon local
realization of the displayed square-root isometry.

## 3. A separating certificate that needs no solver trust

**Theorem 2 (weak dual certificate).** Let `X_a >= 0` and let `Y` be
Hermitian; `Y` need not be positive. Suppose that

```text
sum_(a in S) X_a >= Y          for every S in F.               (Dual)
```

Set `q=sum_a Tr(X_a A_a) >= 0`. Every feasible (Primal) obeys

```text
C_0 q >= Tr(Y).                                               (Bound)
```

In particular, `q=0` and `Tr(Y)>0` rule out every finite `C_0`. If `q>0`,
they give the rigorous lower bound `C_0 >= Tr(Y)/q`.

**Proof.** Positivity of `X_a` and `C_0 A_a-F_a` gives
`C_0 Tr(X_a A_a) >= Tr(X_a F_a)`. Sum and expand the marginals:

```text
C_0 q >= sum_a Tr(X_a F_a)
       = sum_(S in F) Tr[E_S (sum_(a in S) X_a)]
       >= sum_(S in F) Tr(E_S Y)
       = Tr(Y).
```

The second inequality uses positivity of `E_S` and the corresponding slack
matrix in (Dual). Products need not commute: for positive `U,V`,
`Tr(UV)=Tr(U^(1/2)V U^(1/2)) >= 0`. This proves (Bound) directly.
No assumption of strict feasibility or strong duality is needed or made.

If the empty label is feasible, (Dual) includes `0 >= Y`, so the trace
cannot be positive. This is consistent with the zero-cost exactifier for
frustration-free instances; a dual certificate cannot manufacture a
positive lower bound in that case.

## 4. Singleton neighborhoods: an explicit infinite-cost certificate

For clarity, the projectors of the previous audit are

```text
P = diag(0,1),
w = (2N,N^2-1)^T/(N^2+1),       Q_N = w w^*.
```

Here `w^*w=1`. Use `N>1`, and put

```text
d=N^2+1,  s=2N/d,
A_P=P,    A_Q=Q_N,
X_P=I-P,  X_Q=I-Q_N,
Y=(X_P+X_Q-s I)/2.
```

The feasible labels are the three nonempty subsets. The two singleton
slacks are `(s I + Q_N-P)/2` and `(s I - (Q_N-P))/2`.
Direct multiplication gives `(Q_N-P)^2=s^2 I`, and `Tr(Q_N-P)=0`.
Thus the Hermitian difference has eigenvalues `+s,-s`, and both singleton
slacks are positive. The two-label slack is `(X_P+X_Q+s I)/2`, also positive.
All coefficients are rational functions of the positive integer `N`.

But `q=Tr[(I-P)P]+Tr[(I-Q_N)Q_N]=0` and

```text
Tr(Y)=1-s=(N-1)^2/(N^2+1)>0.
```

Theorem 2 therefore gives an exact certificate that no finite local charge
constant is possible. Allowing indefinite `Y` is important: requiring
`Y>=0` would unnecessarily discard this separating certificate.

## 5. Both-term neighborhoods: a sharp constructive certificate

Now choose `A_P=A_Q=K=P+Q_N` for `N>=1`. The good syndrome from the previous
audit has `E_{P}=E_{Q}=I/2`, with all other effects zero. It is feasible at

```text
C_0=d/4,
```

Indeed the orthonormal vectors `g=(N,-1)^T/sqrt(d)` and
`f=(1,N)^T/sqrt(d)` obey `Kg=(2/d)g` and `Kf=(2N^2/d)f`, giving
`K >= (2/d)I`. The exact preparation states are `I-Q_N` for label
`{P}` and `I-P` for label `{Q}`.

For a matching lower certificate let `G=gg^*` and choose
`X_P=X_Q=Y=G`. Each feasible label is
nonempty, so all dual slacks are nonnegative multiples of `G`. Since
`Kg=(2/d)g`, we have `q=4/d` and `Tr(Y)=1`. Theorem 2 gives `C_0>=d/4`.
Thus the displayed primal and dual certificates prove the **exact optimum**.

Occurrence is two, so the resulting global constant is `C_0 R=d/2`,
matching the optimal unrestricted rounder constant. Enlarging the
neighborhood has removed the absolute kernel obstruction, but the sharp
constant still diverges quadratically. This candidate therefore does not
provide the uniform-cost construction needed by the QPCP route.

At the boundary `N=1`, the projectors are orthogonal. Singleton
neighborhoods admit effects `E_{P}=P`, `E_{Q}=Q_1` with `C_0=1`.
The choice `X_P=X_Q=Y=I` gives `Tr(Y)/q=1`, proving sharpness there too.
This checks the strict `N>1` hypothesis in section 4.

## 6. Integration into the open construction

The new shared-data claim
`amplifier-has-compatible-local-syndrome-effects` requires one tuple
`(W,B,N,C_0,R)` for the same amplifier and Hamiltonian, with uniform local
energy bounds, joint feasibility, and the required physical realization.
The rounder route now consumes this common witness explicitly.

An exact SDP solution would settle only the unrestricted mathematical
part for that instance. The remaining QPCP step is a uniform construction
of such compatible data for a polynomial-time, completeness-preserving
constant-locality and constant-alphabet amplifier. No such construction is
proved here. Cairn's QPCP root and this shared-data claim remain OPEN.

Run `python3 scripts/check_qpcp_syndrome_sdp.py` to verify the explicit
primal/dual witnesses in exact rational arithmetic. The replay lists every
matrix, every feasible label, and the resulting lower bound for the tested
parameters. The analytic proofs above cover all stated `N`; the finite
replay is not a QMA-hardness proof or Lean verification.
