---
rg: 2
id: one-small-higman-generator-collapses-the-four-cycle-proof
kind: route
title: Combine spectral cubic torsion with fixed-power propagation around Higman
target: one-small-higman-generator-collapses-the-four-cycle
requires: [unitary-square-covariance-forces-cubic-spectrum]
---

Write `r=||U_j-1||`.  Choose `z` in the spectrum of `U_j` with
`|z-1|=r`.  Since `r<=sqrt(2)`, the point `z` lies in the closed right
semicircle and

```text
|z+1|=sqrt(4-|z-1|^2)>=sqrt(2).
```

Therefore

```text
||U_j^2-1||
 >= |z^2-1|
 = |z-1||z+1|
 >= sqrt(2)r.                                         (1)
```

The preceding Higman relation and unitary invariance give

```text
||U_j^2-1||
 <= ||U_(j-1)U_jU_(j-1)^*-U_j^2||
    +||U_(j-1)U_jU_(j-1)^*-1||
 <= delta+r.                                          (2)
```

Combining `(1)` and `(2)` yields

```text
r <= delta/(sqrt(2)-1)=(sqrt(2)+1)delta.              (3)
```

For arbitrary unitaries `A,V`,

```text
||AVA^*-V|| <= 2||A-1||,
||V-V^2||   = ||V-1||.                                (4)
```

Apply `(4)` to the next Higman relation.  If
`r_k=||U_(j+k)-1||`, then

```text
r_(k+1) <= delta+2r_k.                                (5)
```

Starting from `(3)`, three iterations give respectively

```text
r_1 <= (1+2c)delta,
r_2 <= (3+4c)delta,
r_3 <= (7+8c)delta,          c=sqrt(2)+1.
```

The last coefficient is `7+8(sqrt(2)+1)=15+8sqrt(2)`, proving `(HAC3)`.


## Stronger basin: full quantitative proof

The following sections prove the stronger assertions in the target. The
prerequisite supplies equation (14.5), namely the cubic spectral estimate.
Section and equation numbers follow the cumulative research record.

### 14.4. Approximate cubic torsion collapses the four-cycle quantitatively

Let \(U_0,U_1,U_2,U_3\) be unitaries and put

\[
\delta=\max_i\|U_iU_{i+1}U_i^*-U_{i+1}^2\|,
\qquad \eta=\|U_0^3-I\|,
\]

with indices modulo four. Put \(N=2^{127}-1\), an odd integer.
Then

\[
\|U_0-I\|\le(N+17)\eta+(3N+564)\delta,
\tag{14.6}
\]

and

\[
\max_i\|U_i-I\|
\le8(N+17)\eta+(24N+4519)\delta.
\tag{14.7}
\]

**Proof.** If \(\|AWA^*-W^2\|\le\delta\), repeated conjugation and
telescoping powers of unitaries give, for every fixed positive integer \(m\),

\[
\|A^mWA^{-m}-W^{2^m}\|\le(2^m-1)\delta.
\]

The induction step adds at most \(2^m\delta\), since
\(\|X^k-Y^k\|\le k\|X-Y\|\) for unitaries. Also,
\(\|A^mWA^{-m}-W\|\le2\|A^m-I\|\). Hence

\[
\|W^{2^m-1}-I\|
\le(2^m-1)\delta+2\|A^m-I\|.
\tag{14.8}
\]

Use (14.8) successively with \((A,W,m)=(U_0,U_1,3)\),
\((U_1,U_2,7)\), and \((U_2,U_3,127)\). This yields

\[
\begin{aligned}
\|U_1^7-I\|&\le7\delta+2\eta,\\
\|U_2^{127}-I\|&\le141\delta+4\eta,\\
\|U_3^N-I\|&\le(N+282)\delta+8\eta.
\end{aligned}
\tag{14.9}
\]

The last cyclic relation and the cubic error imply

\[
\|U_3U_0U_3^*-U_0^{-1}\|\le\delta+\eta,
\]

because \(\|U_0^2-U_0^{-1}\|=\eta\). Conjugation commutes with
inversion, and inversion preserves distances between unitaries. Induction
therefore gives

\[
\|U_3^kU_0U_3^{-k}-U_0^{(-1)^k}\|\le k(\delta+\eta).
\]

Since \(N\) is odd, comparison with \(U_0\) using (14.9) shows

\[
\|U_0-U_0^{-1}\|
\le N(\delta+\eta)+2((N+282)\delta+8\eta).
\]

Finally,
\(\|U_0-I\|\le\|U_0^3-I\|+\|U_0^2-I\|
=\eta+\|U_0-U_0^{-1}\|\), proving (14.6).

If \(r_i=\|U_i-I\|\), the ordinary cyclic relation also gives
\(r_{i+1}\le2r_i+\delta\). Three iterations give
\(\max_i r_i\le8r_0+7\delta\), which proves (14.7). ∎

The very large constant is explicit and independent of dimension. This is
an all-dimensional estimate, not an asymptotic argument involving
dimension-dependent powers: the integers \(3,7,127,N\) are fixed once and
for all.

### 14.5. The improved Higman obstruction, and its limit

Combining the prerequisite estimate (14.5) and (14.7), if one generator satisfies
\(\|U_j-I\|\le c_a\) and the four-relation defect is below \(\delta_a\),
then

\[
\max_i\|U_i-I\|\le K\delta,
\qquad
K=(24+12\pi)N+204\pi+4519.
\tag{14.10}
\]

Here we used \(2\arcsin(\delta/2)\le\pi\delta/2\), which follows from
convexity of arcsine and its chord between 0 and 1. Cyclic relabelling
handles any \(j\).

Let \(H\) denote Higman's group with these four cyclic relations. If
\(\rho:H\to U(\mathcal Q_{\mathbf d})\) is nontrivial, then

\[
\boxed{\|\rho(g_j)-1\|\ge2\sin(2\pi/5)
\quad\text{for each }j.}
\tag{14.11}
\]

For if one quotient norm were strictly smaller, choose \(a<2/5\), with
\(a\ge1/3\), such that \(c_a\) is larger than that norm. Unitary coordinate
lifts eventually satisfy the required radius bound, their four relator
defects tend to zero, and (14.10) kills every generator in the quotient.
This contradicts nontriviality.

Equivalently, along any coordinate subsequence on which
\(\max_i\|U_{i,n}-I\|\) is bounded away from zero and the relator defects
tend to zero, the lower limit of every generator distance is at least
\(2\sin(2\pi/5)\). Specifying the subsequence matters: arbitrary insertion
of trivial coordinates does not destroy a limsup-separated corona model.

**This still does not prove that \(H\) is non-MF.** The four generators may
all stay at or above this threshold. In particular, the existing clock
constructions with maximal spectral distance are not excluded. Nor does the
fifth-root example close a full Higman cycle. The proved result is the
larger spectral basin and its uniform estimate, not unconditional collapse.
