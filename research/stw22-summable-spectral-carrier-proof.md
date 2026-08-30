---
rg: 2
id: stw22-summable-spectral-carrier-proof
kind: route
title: Capture an L2-continuous loop by summably many orthogonal norm-continuous carriers
target: stw22-diffuse-stiefel-uniform-loop-fillings
requires: []
artifacts:
  - research/artifacts/stw22-diffuse-spectral-capture-audit-2026-08-30.md
---

We first prove `(SC)` and then derive `(DSF)`. All norms without a subscript
are operator norms.

## 1. The norm-continuous carrier lemma

We use the following lemma inside a possibly moving corner. Let `r_z` be an
operator-norm-continuous projection loop of constant trace in a `II_1`
factor, and let

```text
c:S^1 -> N,       c(z)=c(z)r_z,
```

be operator-norm continuous with `sup_z||c(z)||_2<=D`. If

```text
s=8D^2/alpha^2 < tau(r_z),                             (SC1)
```

then there is an operator-norm-continuous projection loop `p_z<=r_z` with

```text
tau(p_z)=s,       ||c(z)(r_z-p_z)||<alpha.              (SC2)
```

Here is the patching proof. Trivialize the norm-continuous corner locally by
the canonical direct rotation for nearby projections. On a sufficiently
fine doubled cyclic cover, the transported operators differ from the centre
operator by less than `alpha/4`. At each centre take the spectral projection
of the absolute value for `(alpha/2,infinity)`. Its trace is at most
`4D^2/alpha^2=s/2`. Enlarge it, in the diffuse corner, to a projection of
trace exactly `s/2`, and transport this projection over its doubled arc. It
is a local carrier with residual norm less than `3alpha/4`.

On a core arc enlarge the local trace-`s/2` carrier to trace `s`. At a
transition point, the join of the two adjacent trace-`s/2` carriers has
trace at most `s`, so enlarge that one fixed join to trace `s`. Connect the
core carrier to this transition carrier through trace-`s` projections which
contain the first local carrier, and connect onward through trace-`s`
projections containing the second. These path spaces are Grassmannians in a
diffuse finite corner and are path connected. Every point of each half-path
therefore retains one of the two valid local carriers. Repeating cyclically
gives `(SC2)`. Importantly, the proof never asserts that a moving join or a
hard spectral projection is continuous.

The same proof applies after a norm-continuous change of corner, which is
why the moving `r_z` formulation was stated.

## 2. Decompose the L2 loop into norm-continuous increments

If `delta=0`, take `e=0`. Otherwise choose operator-norm-continuous loops

```text
y_j:S^1 -> Nq,       sup_z||x(z)-y_j(z)||_2<delta 4^(-j)
                                                            (j>=1). (SC3)
```

They exist by taking a sufficiently fine cyclic partition in the `2`-norm
and linearly interpolating the sampled values. Put

```text
d_1=y_1,       d_j=y_j-y_(j-1)                         (j>=2),
alpha_j=kappa 2^(-j).
```

Then

```text
sup||d_1||_2 <=5delta/4=:D_1,
sup||d_j||_2 <=5delta 4^(-j)=:D_j                    (j>=2). (SC4)
```

Allocate the carrier traces

```text
s_j=8D_j^2/alpha_j^2.
```

A direct summation gives

```text
sum_j s_j
 <=8(25/4+25 sum_(j>=2)4^(-j)) delta^2/kappa^2
 =200/3 delta^2/kappa^2
 <67 delta^2/kappa^2.                                  (SC5)
```

If this sum is at least `tau(q)`, take `e=q` and `(SC)` is immediate.
Assume it is smaller.

## 3. Add the carriers orthogonally

Construct operator-norm-continuous projections inductively. Set `e_0=0`.
Once `e_(j-1)` is given, put

```text
r_j=q-e_(j-1),       c_j=d_jr_j.
```

The maps `r_j,c_j` are operator-norm continuous and
`sup||c_j||_2<=D_j`. Moreover

```text
tau(r_j)=tau(q)-sum_(i<j)s_i > s_j
```

because the full sum in `(SC5)` is less than `tau(q)`. Apply the lemma from
Step 1 to obtain `p_j<=r_j`, of trace `s_j`, with

```text
||d_j(q-e_(j-1)-p_j)||<alpha_j.
```

Set `e_j=e_(j-1)+p_j`. Thus the new carriers are orthogonal, every `e_j` is
operator-norm continuous, and

```text
||d_j(q-e_j)||<alpha_j.                                (SC6)
```

The increasing projections `e_j(z)` converge in `2`-norm, uniformly in
`z`, to a projection `e(z)`: the squared norm of the tail is exactly
`sum_(i>j)s_i`. This uniform convergence makes `e:S^1->N` `2`-norm
continuous, and `(SC5)` gives its constant trace.

Since `e>=e_j`, equation `(SC6)` gives

```text
||d_j(q-e)||<=alpha_j.
```

Therefore `sum_j d_j(q-e)` converges in operator norm, with norm at most
`sum_j alpha_j=kappa`. Its partial sums are `y_j(q-e)`, which also converge
in `2`-norm to `x(q-e)` by `(SC3)`. The operator-norm limit and the
`2`-norm limit coincide. Hence `||x(q-e)||<=kappa`, completing `(SC)`.

## 4. Localize and fill a diffuse Stiefel loop

Normalize the centre of the loop by a left unitary, so it is enough to
consider

```text
v:S^1 -> St_N(q),       sup_z||v(z)-q||_2<delta.
```

Apply `(SC)` to `x=v-q`. If it returns `e=q`, the whole Stiefel space has
diameter at most `2sqrt(tau(q))<=2sqrt(67)delta/kappa`; the nonquantitative
filling used below suffices. Otherwise put `f_z=q-e_z`. The partial
isometries `v(z)f_z` and `f_z` have common initial projection and are within
`kappa` in operator norm. The controlled direct rotation from
`stw22-matrix-stiefel-defect-localization-proof` is expressed by uniformly
bounded multiplication, inversion away from zero, and functional calculus;
hence its formula is `2`-norm continuous for the present `2`-continuous
inputs. It homotopes `v` within `delta+10kappa` of `q` to

```text
v'(z)=q-e_z+w_z,
w_z^*w_z=e_z,       w_zw_z^* orthogonal to q-e_z.      (SC7)
```

It remains only to fill the loop `(e_z,w_z)` while keeping the trace of
`e_z` fixed. Choose a base pair `(e_0,w_0)` and put `f_0=q-e_0`. The
one-dimensional continuous-comparison theorem for `II_1` factors supplies
continuous unitary loops

```text
a_z in U(qNq),       c_z in U((1-f_0)N(1-f_0))
```

such that, with `a_z` extended by `1-q`,

```text
e_z=a_ze_0a_z^*,       w_z=a_z c_z w_0a_z^*.           (SC8)
```

One first selects `a_z`; after conjugating by it, one selects `c_z` between
two frames with fixed initial projection. This is exactly the dimension-one
unitary selection theorem of Farah--Vaccaro.

For a factor with separable predual, Jekel's strong-topology contraction of
the unitary group contracts both loops `a_z` and `c_z`. Substitution in
`(SC8)` fills `(e_z,w_z)` through pairs satisfying `(SC7)`. Every resulting
frame differs from `q` only on a right support of trace `tau(e_0)`, so the
entire filling has radius at most

```text
2sqrt(tau(e_0)) <=2sqrt(67) delta/kappa.               (SC9)
```

Finally take `epsilon_0=min(epsilon,1)`,

```text
kappa=epsilon_0/40,       delta=epsilon_0^2/2560.
```

Then `delta+10kappa<epsilon` and the right side of `(SC9)` is less than
`epsilon`. This proves `(DSF)`.

The external topological inputs used only after localization are A. Farah
and A. Vaccaro, *Continuous Selection of Unitaries in II_1 Factors*,
arXiv:2501.01272, and D. Jekel, *The unitary group of a II_1 factor is
SOT-contractible*, arXiv:2508.05834. Their contractions need no quantitative
control here because `(SC9)` controls the whole localized configuration
space by its fixed source trace.
