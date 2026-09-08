# Dilute Iwahori defects require concentrated corrections

2026-09-08. This gives a necessary shape of a correction for an explicit
family of exact modular vertex representations. It also refutes a uniform
sixth-moment-flat quadratic step in the explicit admissible modular
parameterization. It does not refute Hilbert--Schmidt stability: the family
has an exact same-dimensional repair of linear Hilbert--Schmidt cost.

## 1. An incompatible block with the central relation already exact

Use the modular presentation

```text
SL_2(Z)=<s,b | s^2=b^3, s^4=1>,
s=[[0,-1],[1,0]], b=[[0,-1],[1,1]], t=s^(-1)b.
```

There is a one-dimensional character `chi(s)=-1`, `chi(b)=1`.
Both sides of `s^2=b^3` are one, so `chi(-I)=1`, and `chi(t)=-1`.
In dimension `n`, take the pair of exact vertex representations

```text
pi_1=1_n,              pi_2=chi (+) 1_(n-1).                 (1)
```

For the Iwahori generators `t`, `l_2=[[1,0],[2,1]]`, and `-I`, the
commensurator map in
`iwahori-local-global-defect-question` sends `t` to `t^2`, `l_2` to
`l_1=[[1,0],[1,1]]`, and fixes `-I`. Since

```text
l_1=s t^(-1) s^(-1)=s b^(-1),       l_2=(s b^(-1))^2,
```

only the lower-unipotent compatibility equation fails in (1). Its
matrix difference is `2` on the first coordinate and zero elsewhere.
Consequently the local defect is exactly

```text
e_n=def(pi)=2/sqrt(n).                                      (2)
```

Write the four generator matrices as `U=(S_1,B_1,S_2,B_2)`. The fixed
word

```text
w(U)=(S_1 B_1^*)^2 (S_2 B_2^*)^*
```

has length six. It is the lower-unipotent mismatch written as a
unitary relator, and `||w(U)-I||_op=2`.

## 2. Superlinear defect reduction forces operator-norm movement

Adjoin arbitrary exact vertex representations on `r_n` coordinates,
with `N_n=n+r_n<=C_0 n` for a fixed `C_0`. Denote the resulting four
matrices by `U^0`. The original space is reducing before correction,
so `||w(U^0)-I||_op=2`, regardless of the added blocks' defects.

Let `V` be any pair of exact vertex representations in dimension `N_n`
whose local defect satisfies

```text
def(V) <= A e_n^(1+beta),        beta>0.                     (3)
```

This includes exact compatible outputs. Norm comparison and (2) give

```text
||w(V)-I||_op <= sqrt(N_n) def(V)
              <= A sqrt(C_0) 2^(1+beta) n^(-beta/2)=o(1).
```

Telescoping a length-six word in unitaries therefore implies

```text
M_inf := max_g ||V_g-U^0_g||_op >= (2-o(1))/6.              (4)
```

For normalized Schatten norms, `||X||_p>=N_n^(-1/p)||X||_op`.
Thus, with `M_p=max_g ||V_g-U^0_g||_(p,N_n)`,

```text
M_p >= ((2-o(1))/6) N_n^(-1/p).                             (5)
```

If a proposed correction also has `M_2<=C e_n^alpha`, then

```text
M_p/M_2 >= c n^(alpha/2-1/p),                              (6)
```

for a positive constant `c` independent of `n`. In particular a
dimension-independent ratio `M_p<=kappa M_2` is impossible whenever
`alpha p>2`. For square-root movement and the sixth moment, the
necessary ratio grows at least as `n^(1/12)`.

The exponent in (6) is an obstruction threshold, not a sufficiency
claim at or below `alpha p=2`. The argument also does not cover
unbounded relative padding. Such padding is independently incompatible
with vanishing distance in the generalized metric.

## 3. The explicit flat-parameter quadratic proposal fails

Apply the parameterization of
`modular-vertex-charts-have-uniform-schatten-control` at `U^0`, taking
the product of its charts for the two vertices. It satisfies

```text
max_g ||Psi(H)_g-U^0_g||_op <= 4 ||H||_op.                  (7)
```

Here each parameter-tuple norm is the maximum of its six matrix-entry
norms. Suppose `H=xi+eta` obeys the proposed uniform budgets

```text
||xi||_2 <= C sqrt(e_n),       ||eta||_2 <= C e_n,
||xi||_6 <= kappa ||xi||_2,    ||eta||_6 <= kappa ||eta||_2,
r_n <= B e_n n.                                            (8)
```

The padding is `O(sqrt(n))`, so `N_n/n` tends to one. By the triangle
inequality, without any relative-flatness assumption on `xi+eta`,

```text
||H||_op <= N_n^(1/6)(||xi||_6+||eta||_6)
          <= kappa C N_n^(1/6)(sqrt(e_n)+e_n)
          = O(n^(-1/12)).                                  (9)
```

Equations (7) and (9) contradict (4) if the output has defect
`O(e_n^(3/2))`. This rules out the universal step (8) in these natural
charts, even if neutrality, right-inverse, and projected-Hessian
conditions could otherwise be arranged. The obstruction precedes
those more complicated questions.

This does not refute the entire claim
`iwahori-admits-neutral-quadratic-directions`, which permits an
arbitrary dimension-dependent map `Psi` and assumes only specified
residual-derivative and HS-movement estimates. An arbitrary such map
has not been shown to satisfy (7). For that broader formulation a
proof must either establish a concentrated-error mechanism explicitly
or explain how its parameterization avoids this operator-norm test.
The mere existence of the natural chart cannot transfer unknown
directions from another parameterization into it.

## 4. What remains true, and the required repair shape

Replace the single character `chi` in (1) by the trivial character.
The two vertices then agree exactly in the original dimension, and
the maximum generator displacement is `2/sqrt(n)=e_n`. Thus the
family is linearly repairable in normalized HS norm. Its correction
has a fixed operator norm on one coordinate; its sixth/second
moment ratio is `n^(1/3)`.

The previously proved clock-shift example
`commuting-repair-forces-half-dimension-rank` supplies the complementary
test: general normalized-HS repair cannot be confined to low-rank
changes either. Together these show why a uniform method must handle
both concentrated changes of fixed size and changes spread across
many dimensions. They do not assert that every individual input
needs both, or that a method handling both is sufficient.

The elementary decomposition behind that distinction is exact. For
any two unitaries `U,V` in the same dimension, write `VU^*=exp(K)`
using an anti-Hermitian principal logarithm with spectrum in
`i[-pi,pi]`. For `0<theta<=pi`, split `K=K_lo+K_hi` by the spectral
cut `|K|<=theta`. Then the two pieces commute and

```text
V=exp(K_hi) exp(K_lo) U,
||K_lo||_op<=theta,
||K||_2 <= (pi/2)||V-U||_2,
rank(K_hi)/n <= (pi^2/(4 theta^2))||V-U||_2^2.              (10)
```

These follow from `|a|<=pi|exp(ia)-1|/2` on `[-pi,pi]` and the
spectral counting inequality. Decomposing a known correction is not
a procedure for constructing one. In particular, applying (10) to
the separate generators need not preserve the exact vertex relations
at an intermediate tuple. That additional geometric requirement is
the reason to use exact admissible parameterizations where possible.
