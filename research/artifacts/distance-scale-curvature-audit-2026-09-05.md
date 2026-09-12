# Distance-scale audit: regular tangents improve, diluted obstructions remain singular

There is a useful positive result at the distance to the exact
representation variety: a uniformly integrable normalized displacement
from a nearby exact representation can be removed by conjugation, provided
the defining defect is smaller than that displacement. But uniform
integrability of the *relator errors* does not give this displacement
hypothesis. In fact any hypothetical failure of flexible HS stability for
a Kazhdan group can be diluted into tuples approaching the exact variety
whose nearest-representation displacements necessarily fail that hypothesis.
This gives a precise obstruction to the proposed minimal-distance method.

## 1. Regular displacement has no first-order obstruction

Let `G=<S|R>` be finitely presented, with `H^1(G,H)=0` for every unitary
Hilbert representation. Kazhdan groups have this property, as recalled in
[Bader--Sauer, Introduction](https://arxiv.org/html/2308.06517v3).
Let `rho_j:G->U(d_j)` be genuine representations and `U_j` generator
tuples. Suppose

```text
eta_j=max_s ||U_j(s)-rho_j(s)||_2 -> 0,   eta_j>0,
delta_j=max_r ||U_j(r)-I||_2=o(eta_j).
```

Assume the normalized generator displacements

```text
A_(j,s)=(U_j(s)rho_j(s)^*-I)/eta_j
```

are uniformly square-integrable. Then, after a subsequence, there are
unitaries `C_j` with `||C_j-I||_2=O(eta_j)` such that

```text
max_s ||U_j(s)-C_j rho_j(s) C_j^*||_2=o(eta_j).          (DCA1)
```

Here is a proof. Work in the regular subspace of the normalized matrix
Hilbert ultraproduct. The exact adjoint actions of `rho_j` give a genuine
unitary representation on that subspace. Extend each `U_j` to words.
Normalized displacements for fixed words are regular by finite word
telescoping. Two words representing the same group element have evaluated
distance `O(delta_j)`, with a constant depending on those fixed words.
After division by `eta_j`, their displacements therefore have the same
ultraproduct class.

Let `a(g)` denote this class. Unitarity makes it skew-Hermitian: the
Hermitian part is a regular normalized displacement multiplied by an
operator-bounded displacement tending to zero in 2-norm. The same product
estimate applied to word multiplication gives

```text
a(gh)=a(g)+Ad(rho(g))a(h).
```

Thus it is a genuine 1-cocycle in the regular Hilbert module. Vanishing
of `H^1`, followed by projection to the real skew-Hermitian subspace,
gives a regular skew-Hermitian vector `b` such that

```text
a(g)=b-Ad(rho(g))b.
```

Choose regular skew-Hermitian representatives `b_j` and set
`C_j=exp(eta_j b_j)`. The regular exponential estimate and the regular
product estimate give

```text
(C_j rho_j(s) C_j^*rho_j(s)^*-I)/eta_j
 = b_j-Ad(rho_j(s))b_j+o(1)
```

in normalized 2-norm along the ultrafilter. This agrees with `A_(j,s)`
there, proving `(DCA1)` and the displacement bound. A subsequence yields
ordinary sequence statements.

In particular, if `rho_j` is an asymptotically nearest same-dimensional
exact representation, meaning its distance `eta_j` is within a factor
`1+o(1)` of the infimum, these hypotheses are contradictory. More
generally a fixed positive lower bound on the ratio of that infimum to
`eta_j` suffices. The same assertion applies after any fixed choice of
padding; it does not by itself decrease a separately charged padding
budget.

## 2. Why nearest-distance normalization need not be regular

Even exact nearest-point choices can have entirely singular normalized
displacements. For `C_2=<s|s^2=1>`, fix `0<theta<pi/2`, let `P_j` have
rank fraction `p_j->0`, and put

```text
U_j(s)=I+(exp(i theta)-1)P_j,
rho_j(s)=I.
```

The identity is a nearest unitary involution: in minimizing the squared
distance, the real part of `U_j(s)` is positive definite, so choosing
every involution eigenvalue `+1` maximizes the trace pairing. Its distance
is `eta_j=|exp(i theta)-1|sqrt(p_j)`. The normalized displacement is
a scalar of modulus one times `P_j/sqrt(p_j)`. It has 2-norm one and
1-norm `sqrt(p_j)->0`, so its regular projection is zero and it is not
uniformly square-integrable.

This particular example has defect comparable to distance; it is not
a counterexample to `(DCA1)` or to stability. It demonstrates that
approaching the exact variety and minimizing distance do not supply
regular tangent vectors.

The next construction also enforces `delta=o(eta)` whenever a genuine
flexible stability obstruction exists. It does not presume that such an
obstruction has been proved for the arithmetic group.

## 3. Dilution preserves a relative obstruction

Fix a Kazhdan constant `kappa` in the convention used by
`moving-subgroup-schreier-correction-has-no-index-loss`, and write
`C=1+10/kappa`. Suppose tuples `U_j:S->U(d_j)` have defining defect
`delta_j->0`, but, for fixed `epsilon,gamma>0`, no genuine padded
representation with relative added dimension at most `gamma` has
generator distance less than `epsilon` from `U_j` with identity padding.

Choose integers `N_j>=d_j` with `p_j=d_j/N_j->0`, and set

```text
Uhat_j(s)=U_j(s) direct_sum I_(N_j-d_j).
```

Let `eta_j` be the distance from this tuple to the exact representation
variety in dimension `N_j`. This infimum is attained: the exact generator
tuples form a closed subset of the compact space `U(N_j)^S`. Then

```text
c sqrt(p_j) <= eta_j <= 2 sqrt(p_j),
c=min(epsilon/C, (kappa/2)sqrt(gamma))>0.               (DCA2)
```

The upper bound compares with the trivial representation. For the lower
bound, let `sigma_j` be any genuine representation on `C^(N_j)` at
generator distance `e_j` from `Uhat_j`. Let `W_j:C^(d_j)->C^(N_j)`
include the original summand. Then

```text
max_s ||sigma_j(s)W_j-W_j U_j(s)||_HS/sqrt(d_j)
 <= e_j/sqrt(p_j)=:beta_j.
```

Apply the original-rank invariant-corner argument from the moving
Schreier proof directly to this supplied genuine representation and
isometry. Induction was only the mechanism for supplying those data;
the subsequent Kazhdan projection, rank estimate, and polar correction
depend solely on the displayed intertwining error. They give a genuine
representation correcting `U_j` with

```text
relative added dimension <=4 beta_j^2/kappa^2,
generator error <=C beta_j.
```

Thus `e_j<c sqrt(p_j)` contradicts the assumed obstruction. Taking its
infimum proves `(DCA2)`.

Defining relator evaluation respects the direct sum, so the new defect
is exactly `deltahat_j=sqrt(p_j)delta_j`. Consequently

```text
eta_j -> 0,
deltahat_j/eta_j <= delta_j/c -> 0.                    (DCA3)
```

For **every** sequence of nearest same-dimensional exact representations
of these diluted tuples, `(DCA1)` and `(DCA3)` show that the normalized
generator displacements cannot be uniformly square-integrable. Otherwise
conjugation would reduce the actual minimum distance by a factor tending
to zero, a contradiction.

This is a conditional structural theorem: an assumed flexible obstruction
can always be realized near the exact variety at a scale where its
nearest tangent falls outside the regular Hilbert subspace. It does not
construct an obstruction or refute flexible stability of any group.

## 4. Consequence for curvature concentration and flexible removal

Section 6 of the arithmetic artifact removes the regular component of
the normalized *relator* errors at the defect scale. The distance method
above requires control of normalized *generator displacements* at a
possibly much larger distance scale. Neither conclusion supplies the
other. In the diluted setting, replacing the entire original block by
an exact block has relative ambient rank cost `p_j` and distance cost
of order `sqrt(p_j)`, which is exactly the nearest-distance scale in
`(DCA2)`. An estimate of that order gives no strict relative improvement.

Discarding this block is harmless for qualitative approximation of the
diluted tuple, which was already close to an exact representation. But it
discards the entire original input. To recover correction of that input,
one needs distance `o(sqrt(p_j))` and relative rank loss `o(p_j)` before
undoing the dilution. The corner calculation above makes those scaling
requirements explicit. Small ambient rank alone cannot replace them.

Thus a nearest-representation or minimum-distance proof has a concrete
remaining requirement: either rule out singular nearest tangents when
defect is smaller than distance, or repair their concentrated sector with
strict improvement at the distance scale. Cohomological vanishing on the
regular subspace and the current curvature concentration theorem establish
neither. The new result here is `(DCA1)` together with the rigorous
dilution obstruction `(DCA2)`--`(DCA3)`, not a claim of full stability.

All derivations were checked analytically. No code, build, or computation
was run, and this artifact is not a proof-kernel verification.
