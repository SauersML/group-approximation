---
rg: 2
id: hilbert-embeddable-length-hyperlinearity-proof
kind: route
title: Schoenberg transform of an invariant length, realized by a genuine character
target: hilbert-embeddable-length-hyperlinearity
requires: []
artifacts:
  - notes/NOTEPAD.md
  - GroupApproximation/Sofic/Hyperlinear.lean
---

## Direct proof

**1. Character criterion.**  Let `c:K->C` satisfy `sum_a c_a=0`.  For an
irreducible `pi_i` with character `chi_i`,

```text
sum_(a,b) conj(c_a) c_b chi_i(a^(-1)b)
  = || sum_b c_b pi_i(b) ||_HS^2 >= 0,
```

since `chi_i(a^(-1)b)=<pi_i(b),pi_i(a)>_HS`.  Writing `ell=sum_i b_i chi_i`,
the quadratic form of the kernel is `sum_i b_i ||sum_b c_b pi_i(b)||^2`.  The
constraint `sum_a c_a=0` annihilates exactly the trivial summand, and by
Wedderburn the Fourier map `c |-> (sum_b c_b pi_i(b))_i` is onto
`directSum_i End(V_i)` and stays onto the nontrivial summands after imposing
that one linear constraint.  So the form is nonpositive on all such `c` if
and only if `b_i<=0` for every nontrivial `i`.

Equivalently and more directly: `M[a,b]=ell(a^(-1)b)` is the matrix of
convolution by the class function `ell`, hence central in the group algebra,
hence preserves the constants and `1^perp={c: sum_a c_a=0}`, and acts on the
`chi_i`-isotypic block of the regular representation by the scalar
`|K| b_i/d_i` with multiplicity `d_i^2`.  Conditional negativity is exactly
`M|_(1^perp)<=0`, so exactly `b_i<=0` for nontrivial `i`.  Two by-products:
`b_i` is real because `ell` is real and symmetric, and `ell>=0` is automatic
(test `c=delta_a-delta_1`, giving `-2 ell(a)<=0`), so nonnegativity of `ell`
need not be assumed.  Checked mechanically against the kernel test on `S_3`,
`S_4` and `A_4` (complex characters), 500 random invariant lengths each, no
disagreements.

**2. Realization.**  Assume `ell` Hilbert embeddable.  By Schoenberg's
theorem `phi_t=exp(-t ell)` is positive definite for every `t>0`; it is a
real normalized class function, so `phi_t=sum_i lambda_i chi_i/d_i` with
`lambda_i>=0` and `sum_i lambda_i=1`.  Choose integers `m_i` with
`m_i d_i/D -> lambda_i`, where `D=sum_i m_i d_i`, and put
`rho = directSum_i pi_i^(directSum m_i)`.  Then

```text
tr rho(k) = sum_i (m_i d_i/D)(chi_i(k)/d_i),
```

and `|chi_i/d_i|<=1` gives `|tr rho(k)-phi_t(k)| <= sum_i |m_i d_i/D - lambda_i|`,
which is below any prescribed `epsilon`.  Since
`||u-v||_(2,norm)^2 = 2-2Re tr(v^*u)` for unitaries, the displayed distance
formula follows.  For `0<=s<=1` and `t=1`, concavity of `f(s)=2(1-e^(-s))`
with `f(0)=0` gives `f(1) s <= f(s) <= f'(0) s`, i.e.

```text
2(1-e^(-1)) s <= 2(1-e^(-s)) <= 2 s.
```

Both constants are absolute: they do not depend on `K`, on `ell`, or on the
place in the witness family.  The number of irreducibles used in the
rational approximation does depend on `K`, but `epsilon` is chosen after `K`
is given, so this costs nothing either.

**3. Criterion.**  Let `G` be countable and weakly sofic with Hilbert
embeddable witnesses: for every finite `F <= G` and `delta>0` there are a
finite `K`, a Hilbert embeddable invariant `ell` with `ell<=1`, and
`sigma:G->K` with

```text
ell(sigma(g)sigma(h)sigma(gh)^(-1)) < delta   (g,h in F),
ell(sigma(g)) >= c_g > 0                      (g in F\{1}),
```

the constants `c_g` not depending on `delta`.  This is the usual definition
of weak soficity with "bi-invariant metric" replaced by "Hilbert embeddable
invariant length"; in the form recorded at
`glebsky-weak-soficity-is-metric-free` the separation constant is a fixed
`1/2`, which is a special case of a `c_g` independent of the defect.  (The
numbered reference lives on that node; it was read there and is not
re-asserted here.)  The bound `ell<=1` is
the diameter normalization already built into metric ultraproducts of finite
groups, and it is load bearing — with unbounded diameters, rescaling to
diameter one would send the separation to zero.

Fix `t=1`, apply 2 with `epsilon<delta`, and set `sigma'=rho o sigma:G->U(D)`.  Then

```text
||sigma'(g)sigma'(h)-sigma'(gh)||_2^2 <= 2 ell(...) + 2epsilon < 4 delta,
||sigma'(g)-1||_2^2 >= 2e^(-1) c_g - 2epsilon,
```

using bi-invariance of the normalized-Hilbert--Schmidt metric for the first
line.  Letting `delta->0` along an exhaustion of `G` and taking the metric
ultraproduct gives an injective homomorphism `G -> U(prod_U M_(D_n))`, and
`M_D` embeds trace preservingly in `R`, so `G <= U(R^U)`.  Hence `G` is
hyperlinear.  Note that only conjugation invariance, symmetry and the
conditional negativity of `ell` are used; the triangle inequality for `ell`
is not needed.

**3a. Pairwise separation.**  Injectivity in the ultraproduct — and the
separation field of `Sofic/Hyperlinear.HyperlinearModel` — needs
`sigma'(g)` far from `sigma'(h)` for all distinct `g,h in F`, not only from
`1`.  `ell` itself is not subadditive, but `sqrt(ell)` is a bi-invariant
metric: conditional negativity together with `ell(1)=0` says exactly that
`sqrt(ell)` embeds in Hilbert space.  Run the witness on `F union F F^(-1)`
and factor
`sigma(gh^(-1)) = [sigma(gh^(-1))sigma(h)sigma(g)^(-1)] sigma(g)sigma(h)^(-1)`
to get

```text
sqrt(ell(sigma(g)sigma(h)^(-1))) >= sqrt(c_(gh^(-1))) - sqrt(delta),
```

so `ell(sigma(g)sigma(h)^(-1)) >= c/2` once `delta <= c/4`, where
`c=min_(g != h in F) c_(gh^(-1))`.

**3b. Upgrade to maximal separation.**  The repo's `HyperlinearModel`
demands `2-epsilon <= hsDistSq`, not a constant.  For unitary models this is
not a free convention: `Sofic/HyperlinearAmplification.tensorPow_phase_collapse`
kills tensor amplification, and the conjugate-double repair
`exists_conjDouble_separation` needs `|tau(A B^*)|^2 <= 1-delta`, which fails
precisely on scalars.  The Schoenberg realization supplies that hypothesis
for free, because its traces are approximately the **real positive** numbers
`e^(-ell)`:

```text
|tau(sigma'(g)sigma'(h)^*)| = |tr rho(sigma(g)sigma(h)^(-1))|
                          <= e^(-ell(sigma(g)sigma(h)^(-1))) + epsilon
                          <= e^(-c/2) + epsilon < 1 .
```

So `normSq(tau) <= 1-delta_0` with `delta_0` depending only on `c`, hence
only on `F`.  `exists_conjDouble_separation` then yields a number of tensor
copies `k=k(delta_0,epsilon)` — again independent of the group — after which
the separation is at least `2-epsilon`.  The defect survives amplification:
`hsDistSq(A,B)<=eta` gives `Re tau(A B^*)>=1-eta/2`, hence
`|tau(A B^*)|^(2k) >= (1-eta/2)^(2k) >= 1-k eta`, so the amplified defect is
at most `2 k eta`.  Choose `k` from `F` and the target accuracy first and
`delta` afterwards; every constant is uniform along the sequence.

**4. Calibration.**  On `Sym(n)`, `d_H(sigma,1)=1-chi_perm(sigma)/n` and
`chi_perm = 1 + chi_std`, so `d_H = (1-1/n)*1 - chi_std/n`: the only
nontrivial coefficient is `-1/n<=0`.  This is the same fact as the metric
identity `||P_sigma-P_tau||_(HS,norm)^2 = 2 d_H(sigma,tau)` behind the
formalized `isHyperlinear_of_isSofic`, which is therefore the special case
`ell=d_H` of 3.  The discrete length `1_(k!=1)` is `(1-1/|K|)*1` minus
`chi_i(k)d_i/|K|` summed over nontrivial `i`, all coefficients nonpositive,
and is realized by the regular representation.

For the negative calibration, take `K=GL_2(F_2)=S_3` and
`ell(g)=rank_(F_2)(g-I)`, so `ell=(0,1,1,1,2,2)` on the identity, the three
transpositions and the two three-cycles.  Its coefficient on the sign
character is `(-3+4)/6=1/6>0`, so `ell` is not Hilbert embeddable.  This is
the computation recorded in `notes/NOTEPAD.md` under "Normalized rank has no
Schoenberg bridge to Hilbert--Schmidt geometry", where the same conclusion is
reached by exhibiting `c=sgn` as a violating vector; criterion 1 explains it
and makes the test mechanical for any proposed length.

This single-group computation is **not** evidence that the hypothesis is
hard to satisfy, and must not be quoted as such: the snowflakes of the same
length pass.  On `S_3`,

```text
b_sgn(rank^s) = (2*2^s-3)/6 <= 0   iff   s <= log_2(3/2)=0.58496...,
```

while `b_std(rank^s)=-2^s/3<0` always, so `rank^s` is Hilbert embeddable for
every `s<=log_2(3/2)` and for no larger `s`.  Conditional negativity is also
not stable under the opposite reparametrization: normalized Hamming on `S_4`
is Hilbert embeddable but `d_H^2` is not (kernel test returns `+0.75`).  The
asymptotic content is supplied by 5 below, not by any one group.

**5. Character-gap corollary (what makes the hypothesis restrictive).**
Suppose a family of finite groups satisfies a uniform character ratio bound
`|chi(x)|/chi(1)<=c<1` for every nontrivial irreducible `chi` and every
`x != 1` — Gluck's theorem for the finite Lie type families.  Let `ell<=1` be
Hilbert embeddable on such a `K` and write `e^(-ell)=sum_i lambda_i chi_i/d_i`
with `lambda_i>=0`, `sum_i lambda_i=1`.  Then for every `x`

```text
1-e^(-ell(x)) = sum_(i != 1) lambda_i (1 - Re chi_i(x)/d_i),
```

which is at most `2(1-lambda_1)` always and at least `(1-c)(1-lambda_1)` for
`x != 1`.  With `e^(-1) ell <= 1-e^(-ell) <= ell` on `[0,1]` this gives

```text
max_x ell(x) <= (2e/(1-c)) min_(x != 1) ell(x).
```

So on such a family every Hilbert embeddable invariant length is uniformly
bi-Lipschitz to the discrete length, and a Hilbert embeddable witness
running through those groups is a LEF witness up to absolute constants.
This is the asymptotic obstruction the rank example only gestures at, and it
subsumes the `notes/NOTEPAD.md` no-go "Uniform character gaps forbid
hyperlinearizing finite-field rank models by exact representations".

**5. Normalized-character form.**  For unitaries,
`||u-v||_(2,norm)^2 = 2-2Re tr(v^*u)`, and `tr` is the *normalized* trace, so
with `phi=tr rho` the displayed identity of item 5 is immediate from
`(1/2)||rho(h)-1||_F^2 = dim(rho) - Re tr_un rho(h)` on dividing by
`dim(rho)`.  The cone statement is cairn-bernoulli's and is not reproved
here; what is used is only that a normalized class function `phi` with
`phi(1)=1` is positive definite exactly when its expansion
`phi=sum_i lambda_i chi_i/d_i` has `lambda_i>=0`, which is item 2's
decomposition read backwards.  Given such a `phi`, set `ell=1-Re phi`: it is
conditionally negative definite, and running 3 on it recovers `rho` itself up
to the approximation in 2.  Conversely item 2 applied to a Hilbert
embeddable `ell` produces `phi=exp(-t ell)`.  So the two designs are the same
design.

For the one-line collapse: `|chi_i(x)|/d_i <= c < 1` for all nontrivial `i`
and all `x != 1` gives
`Re phi(x) <= lambda_triv + c(1-lambda_triv) = 1-(1-c)(1-lambda_triv)`, so
`phi(x) >= 1-eta` forces `1-lambda_triv <= eta/(1-c)`, and then
`Re phi(y) >= 1 - 2(1-lambda_triv) >= 1 - 2eta/(1-c)` for every `y`, which is
no separation.

**6. Calibration.**  On `S_3` the transposition class generates, and the word
metric is `0` at the identity, `1` on the three transpositions and `2` on the
two three-cycles, since a three-cycle is a product of two transpositions and
is not itself one.  That is the same table as `rank_(F_2)(g-I)` under
`GL_2(F_2) = S_3`, whose sign coefficient is computed in 4.

On `(Z/2)^A` the characters are `epsilon_S(a)=(-1)^(sum_(alpha in S) a_alpha)`,
and `1_(a_alpha != 0) = (1-epsilon_({alpha})(a))/2`, so the Hamming weight is
`sum_alpha (1-epsilon_({alpha}))/2`: a nonnegative combination of
`1 - character`, hence in the cone of 5.

## Scope

This is a **sufficient** condition only.  Nothing here says that a
hyperlinear group has Hilbert embeddable weak-soficity witnesses, or is
weakly sofic at all: hyperlinear approximations live in `U(n)`, not in
finite groups.  So a negative answer to
`hilbert-embeddable-witness-for-kun-thom-wreath` would not make `W`
non-hyperlinear, and this route is not a characterization.

It also says nothing about which groups are weakly sofic.  Note what the
criterion does *not* ask: it does not ask that a given witnessing length be
Hilbert embeddable, only that the witness can be run with some Hilbert
embeddable length.  On a single finite group that is a weak demand — any two
invariant lengths are comparable there, with constants depending on the
group — so the content is entirely asymptotic: the defect must still tend to
zero and the separations must stay bounded below **uniformly along the
sequence** after the replacement.  Concretely, the usable form of the
hypothesis is: there is one increasing `f` with `f(0)=0`, continuous at `0`
and **independent of the group in the sequence**, with `f o d_n`
conditionally negative definite and bounded by `1`; defect and separation
transport through any such `f`.  Since `d_H` is conditionally negative
definite while `d_H^2` is not, and `rank^s` is for `s<=log_2(3/2)` while
`rank` is not, the choice of `f` is a real degree of freedom and the
question must name it.

The rank calibration is a statement about one parametrization of one length,
not a proof that no comparable Hilbert embeddable replacement exists at
bounded distortion — and on `GL_2(F_2)` such a replacement does exist.  The
only proved obstruction of the required uniform kind is the character-gap
corollary 5, which applies to families with a uniform character ratio bound;
whether the groups produced by Glebsky's permanence theorem have one has not
been inspected.
