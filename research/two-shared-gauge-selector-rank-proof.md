---
rg: 2
id: two-shared-gauge-selector-rank-proof
kind: route
title: Count the two sign sectors and compare spectral projections
target: two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
requires: []
artifacts:
  - research/artifacts/non-mf-without-property-t.md
  - experiments/verify_binary_selector_sharp_gap.py
---

Let `G_+=(1+V)/2` and `G_-=(1-V)/2`.  On `H tensor G_+`, the negative
projection of `C_q tensor V` is `F_q tensor G_+`.  On
`H tensor G_-`, multiplication by the negative sign swaps the two spectral
projections, so the negative projection is `(1-F_q) tensor G_-`.  Dividing

```text
q n rank(G_+)+(1-q)n rank(G_-)
```

by `nm` proves `(TSG1)`.  Unitary conjugacy preserves the rank of the
negative spectral projection, proving `(TSG2)`.  Substitution gives

```text
1/2=3/4-theta/2,        hence theta=1/2,
1/4=7/8-3theta/4,       hence theta=5/6.
```

For the robust form, if `P=(1-R_i)/2` and
`Q=(1-T_i)/2`, then

```text
||W_i P W_i^*-Q||_2
  =(1/2)||W_i R_i W_i^*-T_i||_2.
```

Cauchy--Schwarz for the normalized trace gives
`|tau(P)-tau(Q)|<=||W_iPW_i^*-Q||_2`.  Since
`tau(Q)=Phi_(q_i)(theta)`, this is `(TSG3)`.

For `(r_1,q_1)=(1/2,1/4)`, `(TSG3)` rearranges to
`delta_1>=|theta-1/2|`.  For `(r_2,q_2)=(1/4,1/8)`, it rearranges to
`delta_2>=(3/2)|theta-5/6|`.  The weighted triangle inequality gives

```text
delta_1+delta_2
 >= |theta-1/2|+|theta-5/6| >=1/3.
```

For the squared bound, the minimum of

```text
x^2+(9/4)(1/3-x)^2
```

occurs at `x=3/13` and equals `13/169=1/13`.

For the general sharp constants, `(TSG3)` reads

```text
delta_i >= c_i |theta-theta_i^*|.
```

On the interval between the two target values, minimizing the sum places
`theta` at the endpoint carrying the larger weight and gives
`min(c_1,c_2) Delta`.  Minimizing the square sum

```text
c_1^2 x^2+c_2^2(Delta-x)^2
```

puts `x=c_2^2 Delta/(c_1^2+c_2^2)` and gives `(TSG4b)`.
Minimizing the maximum balances the two terms,

```text
c_1 x=c_2(Delta-x),
```

and gives `(TSG4c)`.  In the binary case `c_1=1`, `c_2=3/2` and
`Delta=1/3`, so the balanced value is `1/5`.  Each minimum is attained by
the corresponding scalar optimization problem, so no larger constants follow
from the two inequalities `delta_i>=c_i|theta-theta_i^*|` alone.  This proves
`(TSG4)--(TSG5)`.

For the approximate-gauge form, the positive spectral projections satisfy

```text
|theta_1-theta_2|
 <= (1/2)||V_2-SV_1S^*||_2=epsilon_g/2.
```

Use the first row to move from `theta_1` to `1/2`, the gauge comparison to
move from `theta_1` to `theta_2`, and the second row to move from `theta_2`
to `5/6`.  The triangle inequality gives `(TSG6)`.  With

```text
x=|theta_1-1/2|,       y=|theta_2-5/6|,
```

one has `x+y >= (1/3-epsilon_g/2)_+`,
`delta_1>=x`, and `delta_2>=(3/2)y`.  Minimizing

```text
x^2+(9/4)y^2
```

at fixed `x+y` gives the factor `9/13`, proving `(TSG7)`.


## Proof of the sharp projection-level refinement


The improvement over the inspected Cairn node is to use the squared Hilbert–Schmidt distance between projections, rather than just Cauchy–Schwarz for their trace difference. This section is an unconditional matrix theorem. Its application to \(\Delta\) is conditional on the unproved attachment of actual group-word occurrences to these matrices.

### 6.1. Projection rank mismatch

**Lemma.** For orthogonal projections \(P,Q\in M_d(\mathbb C)\),

\[
|\operatorname{tr}_d(P)-\operatorname{tr}_d(Q)|
\le\|P-Q\|_{2,d}^2.
\tag{6.1}
\]

If their ranks differ, \(\|P-Q\|=1\).

**Proof.** Write \(p=\operatorname{tr}_d(P)\), \(q=\operatorname{tr}_d(Q)\). Since
\(0\le PQP\le P\) and \(0\le QPQ\le Q\), cyclicity gives

\[
0\le\operatorname{tr}_d(PQ)\le\min(p,q).
\]

Therefore

\[
\|P-Q\|_2^2=p+q-2\operatorname{tr}_d(PQ)\ge|p-q|.
\]

If \(\operatorname{rank}P>\operatorname{rank}Q\), the restriction of \(Q\) to \(\operatorname{Ran}P\) has nonzero kernel. For a unit vector \(v\) there, \((P-Q)v=v\). This proves \(\|P-Q\|\ge1\); the reverse inequality follows from \(-I\le P-Q\le I\). Interchange \(P,Q\) for the other rank ordering. ∎

For reflections \(R=I-2P\), \(T=I-2Q\), this gives

\[
\|R-T\|_2^2\ge4|p-q|,
\tag{6.2}
\]

and unequal negative ranks imply \(\|R-T\|=2\).

### 6.2. The common-gauge setup

Let \(H\) and \(M\) be nonzero complex Hilbert spaces of finite dimensions \(n,m\). Let \(V=V^*=V^{-1}\) act on \(M\), and put

\[
\theta=\frac{\operatorname{rank}((I+V)/2)}m.
\]

Let \(F_i\) be projections on \(H\) of normalized ranks \(q_i\), and set

\[
C_i=I-2F_i,\qquad T_i=C_i\otimes V.
\]

Let \(E_i\) be projections on \(H\otimes M\) of normalized ranks \(r_i\), and set \(R_i=I-2E_i\). For arbitrary unitaries \(W_i\) on \(H\otimes M\), define

\[
\delta_i=\|W_iR_iW_i^*-T_i\|_{2,nm}.
\]

The negative spectral fraction of \(T_i\) equals

\[
\Phi_{q_i}(\theta)
=q_i\theta+(1-q_i)(1-\theta)
=1-q_i+(2q_i-1)\theta.
\tag{6.3}
\]

Indeed, on the positive eigenspace of \(V\), the negative eigenspace is \(F_iH\); on the negative eigenspace of \(V\), it is \((I-F_i)H\).

Applying (6.2) to the negative projections gives the stronger inequality

\[
\boxed{\ \delta_i^2\ge4|r_i-\Phi_{q_i}(\theta)|.\ }
\tag{6.4}
\]

Conjugate gauges in place of the identical \(V\) give the same result, since only the positive spectral fraction is used.

### 6.3. The binary rows

Take

\[
(r_1,q_1)=\left(\frac12,\frac14\right),
\qquad
(r_2,q_2)=\left(\frac14,\frac18\right).
\]

Equation (6.4) becomes

\[
\delta_1^2\ge2\left|\theta-\frac12\right|,
\qquad
\delta_2^2\ge3\left|\theta-\frac56\right|.
\tag{6.5}
\]

It follows that

\[
\boxed{\delta_1^2+\delta_2^2\ge\frac23.}
\tag{6.6}
\]

For

\[
2\left|\theta-\frac12\right|
+3\left|\theta-\frac56\right|
\ge2\left(\left|\theta-\frac12\right|
+\left|\theta-\frac56\right|\right)
\ge\frac23.
\]

Also,

\[
\boxed{\delta_1+\delta_2\ge\sqrt{\frac23},}
\tag{6.7}
\]

because \((\delta_1+\delta_2)^2\ge\delta_1^2+\delta_2^2\).

For the maximum, if \(D=\max(\delta_1^2,\delta_2^2)\), then (6.5) implies

\[
\frac13
\le\left|\theta-\frac12\right|+\left|\theta-\frac56\right|
\le\frac D2+\frac D3=\frac{5D}{6}.
\]

Consequently,

\[
\boxed{\max(\delta_1,\delta_2)\ge\sqrt{\frac25}.}
\tag{6.8}
\]

The corresponding figures in the inspected source node were \(1/13\) for the sum of squares, \(1/3\) for the sum, and \(1/5\) for the maximum. Those were correctly described as optimal consequences of its weaker scalar inequalities. Equations (6.6)–(6.8) use additional projection geometry.

### 6.4. Sharpness by explicit diagonal matrices

The stronger constants are optimal for the matrix hypotheses in §6.2, without any further relation between the two source projections.

Choose \(n=8\), let \(F_1\) project onto the first two standard basis vectors of \(H\), and let \(F_2\) project onto the first one. Choose a diagonal \(V\), and write \(Q_i\) for the negative projection of \(T_i\).

**Sharp sum and squared-sum bounds.** Take \(m=6\) and
\(V=\operatorname{diag}(1,1,1,1,1,-1)\). Thus \(\theta=5/6\), and the total dimension is 48. Formula (6.3) gives

\[
\operatorname{rank}Q_1=16,\qquad
\operatorname{rank}Q_2=12.
\]

Choose a diagonal rank-24 projection \(E_1\ge Q_1\), choose \(E_2=Q_2\), and take \(W_1=W_2=I\). Exactly eight diagonal entries differ between the first pair of projections, and none between the second. Therefore

\[
\delta_1^2=4\cdot\frac8{48}=\frac23,
\qquad\delta_2=0.
\]

This attains both (6.6) and (6.7).

**Sharp maximum bound.** Take \(m=10\), with seven positive and three negative entries in \(V\). Then \(\theta=7/10\), total dimension 80, and

\[
\operatorname{rank}Q_1=32,\qquad
\operatorname{rank}Q_2=28.
\]

Choose diagonal projections \(E_1\ge Q_1\) of rank 40 and \(E_2\le Q_2\) of rank 20, again with \(W_i=I\). Each projection pair differs in eight entries, so

\[
\delta_1^2=\delta_2^2=4\cdot\frac8{80}=\frac25.
\]

This attains (6.8). These finite matrices verify sharpness of the standalone matrix theorem; they are not models of the complete Leavitt group presentation.

### 6.5. The maximal operator-norm gap

Put \(\varepsilon_i=\|W_iR_iW_i^*-T_i\|\). If \(\varepsilon_i<2\), the projection rank lemma forces

\[
r_i=\Phi_{q_i}(\theta).
\]

For row one this forces \(\theta=1/2\); for row two it forces \(\theta=5/6\). Both cannot hold. At least one pair of reflections therefore has unequal negative ranks, and for that pair the norm is exactly 2. Thus

\[
\boxed{\max(\varepsilon_1,\varepsilon_2)=2.}
\tag{6.9}
\]

This is the largest possible distance between two unitaries. It applies on any nonzero common carrier, regardless of that carrier's ambient density.

The conclusion does not imply that an actual group relator has defect 2. The row differences in this theorem must first be connected to the actual group-word defects, on the specified common carrier. That is the missing implication.

### 6.6. Approximately shared gauges

Suppose instead the two rows use involutions \(V_1,V_2\) on the same multiplicity space, and there is a unitary \(S\) such that

\[
\epsilon_g=\|V_2-SV_1S^*\|_{2,m}.
\]

Write \(\theta_i=\operatorname{tr}_m((I+V_i)/2)\). Equation (6.1), applied to the positive projections, gives

\[
|\theta_1-\theta_2|\le\frac{\epsilon_g^2}{4}.
\tag{6.10}
\]

The two row inequalities now give

\[
\boxed{
\frac{\delta_1^2}{2}+\frac{\delta_2^2}{3}
+\frac{\epsilon_g^2}{4}\ge\frac13.
}
\tag{6.11}
\]

Indeed, use the triangle inequality along
\(1/2,\theta_1,\theta_2,5/6\), then apply the bounds just proved. Consequently,

\[
\delta_1^2+\delta_2^2
\ge2\left(\frac13-\frac{\epsilon_g^2}{4}\right)_+,
\tag{6.12}
\]

and

\[
\max(\delta_1,\delta_2)^2
\ge\frac65\left(\frac13-\frac{\epsilon_g^2}{4}\right)_+.
\tag{6.13}
\]

Here \(x_+=\max(x,0)\). If gauge comparison is instead in operator norm and
\(\|V_2-SV_1S^*\|<2\), their positive ranks agree exactly. The operator-norm conclusion (6.9) then still holds.

If the common carrier has ambient normalized trace \(\beta\), squared Hilbert–Schmidt norms of operators supported on it scale by \(\beta\). Thus the ambient squared row energy is at least \(2\beta/3-o(1)\) when the gauge discrepancy tends to zero. This inference requires the **same** carrier for the rows and the gauge comparison. A density estimate for some other projection does not supply it.

### 6.7. Reproducible exact arithmetic checks

The following self-contained Python code constructs the diagonal sign lists in §6.4 and checks ranks and squared defects with exact rational arithmetic. The proof is the preceding argument; the calculation is an independent check of the two equality examples.

```python
from fractions import Fraction as F

def targets(m, positive):
    gauge = [1] * positive + [-1] * (m - positive)
    label1 = [-1] * 2 + [1] * 6
    label2 = [-1] + [1] * 7
    return [[a * b for a in label for b in gauge]
            for label in (label1, label2)]

def source(target, negative_rank):
    negative = [i for i, x in enumerate(target) if x == -1]
    positive = [i for i, x in enumerate(target) if x == 1]
    if negative_rank <= len(negative):
        chosen = negative[:negative_rank]
    else:
        chosen = negative + positive[:negative_rank - len(negative)]
    chosen = set(chosen)
    return [-1 if i in chosen else 1 for i in range(len(target))]

def audit(m, positive):
    t1, t2 = targets(m, positive)
    d = 8 * m
    r1, r2 = source(t1, d // 2), source(t2, d // 4)
    energy = [F(sum((a-b)**2 for a, b in zip(r, t)), d)
              for r, t in ((r1, t1), (r2, t2))]
    opnorm = [max(abs(a-b) for a, b in zip(r, t))
              for r, t in ((r1, t1), (r2, t2))]
    ranks = [sum(x == -1 for x in t) for t in (t1, t2)]
    return d, ranks, energy, opnorm

assert audit(6, 5) == (48, [16, 12], [F(2, 3), F(0)], [2, 0])
assert audit(10, 7) == (80, [32, 28], [F(2, 5), F(2, 5)], [2, 2])

# Binary atomic bound: s_i=1, t_i=2/3.
inverse = abs(F(2, 3) - 1)
complete = abs(2 * F(2, 3) - 1)
assert inverse == complete == F(1, 3)
assert 2 * inverse + complete == 1

print(audit(6, 5))
print(audit(10, 7))
print('All exact arithmetic checks passed.')
```
