# A first-order threshold for the Deligne perturbation route

Date: 2026-09-08.

The exact triple-cover radical has not been proved. The new result here is
an exact criterion for the opposite, all-MF branch and a quantitative
necessary condition on any genuine gap. It distinguishes a second-order
projective construction from the vacuous first-order construction already
available in dimension one.

## Definitions and quantifiers

Let `Gamma=Sp_4(Z)` and fix a normalized integral cocycle `b` for the
actual universal-cover extension. Put
`c_t(g,h)=exp(2 pi i t b(g,h))`. The matrix dimensions below are arbitrary
positive integers. Norm means operator norm. There is no trace or group
separation condition on the projective tuples.

The proposed perturbative input is one sequence of maps
`U_n:Gamma->U(d_n)` and nonzero real `t_n->0` satisfying

```text
U_n(e)=I,
delta_n(g,h)/|t_n| -> 0   for each fixed (g,h),
delta_n(g,h)=||U_n(g)U_n(h)-c_(t_n)(g,h)U_n(gh)||.
```

This requires control on all fixed multiplication pairs along the same
sequence. It is equivalent to using exhausting finite windows with errors
`o(|t_n|)` on each fixed window. It is not a claim about just one selected
matrix size, and not a numerical local-minimum certificate.

## Tensor amplification proves the all-MF branch

Conjugating a tuple reverses the sign of the cocycle parameter and leaves
its defect unchanged. We can consequently suppose `t_n>0`.

Fix `theta in (0,1)`, and let `k_n=floor(theta/t_n)`. On a tail this is
positive. Define

```text
V_n(g)=U_n(g) tensor ... tensor U_n(g)   (k_n factors).
```

For unitaries `A,B` the telescoping identity gives
`||A^(tensor k)-B^(tensor k)||<=k||A-B||`. For every fixed pair this
implies

```text
||V_n(g)V_n(h)-c_(k_n t_n)(g,h)V_n(gh)||
  <= k_n delta_n(g,h)
  <= theta delta_n(g,h)/t_n -> 0.
```

Moreover `0<=theta-k_n t_n<t_n`, so the scalar multipliers converge to
`c_theta` on each fixed pair. We have therefore constructed point-norm
models at every `theta`. Zero is supplied by the trivial representation.

Conversely, if every parameter has point-norm models, choose `t_n=1/n`
for `n>=2`. At parameter `t_n`, take one sufficiently accurate member of
its model sequence, with defect below `t_n^2` on the first `n` pairs of
a fixed enumeration of `Gamma^2`. This produces the required single
perturbative sequence with defect divided by `t_n` tending to zero on
every fixed pair.

By the finite-cover classification already in the repository, this
perturbative input is consequently equivalent to all finite Deligne
covers being MF. The dimensions of the amplified models are
`d_n^(k_n)`; their potentially enormous growth is allowed by the MF
definition and has not been suppressed in the argument.

The same conclusion follows from an `O(t_n^2)` defect estimate with a
constant depending on the fixed pair. It does not follow from a uniform
`O(|t_n|)` estimate on each fixed finite window: the choice `U_n(g)=1`
already satisfies

```text
delta_n(g,h)=|1-c_(t_n)(g,h)|
           <=2 pi |b(g,h)| |t_n|.
```

Tensoring this trivial construction a reciprocal number of times leaves
an error of constant order. Thus ordinary vanishing error at moving
parameters is insufficient; the division by `|t_n|` is essential.

## A fixed gap propagates to a linear lower bound at zero

For a nonempty finite multiplication window `W`, let `f_W(t)` be the
infimum, over all matrix sizes and tuples indexed by the group elements
used in `W`, of

```text
max_((g,h) in W) ||U_g U_h-c_t(g,h)U_(gh)||.
```

Set `B=max_W|b(g,h)|` and `L=2 pi B`. Tensor products and conjugation
prove

```text
f_W(x+y)<=f_W(x)+f_W(y),   f_W(-x)=f_W(x).
```

Comparing scalar phases on one fixed tuple and taking infima in both
directions proves

```text
|f_W(x)-f_W(y)|<=L dist(x,y).
```

Suppose `f_W(a)>=epsilon>0` for `0<a<=1/2`. Necessarily `L>0`.
For `0<t<=min(a,epsilon/(2L))`, put `k=floor(a/t)`. Then

```text
k f_W(t)>=f_W(kt)>=f_W(a)-L(a-kt)>=epsilon-Lt>=epsilon/2.
```

Since `1<=k<=a/t`, this yields

```text
f_W(t)>=epsilon t/(2a).
```

Conjugation gives the corresponding estimate for `-t`. In particular, a
verified window gap `f_W(1/3)>=epsilon` forces

```text
f_W(t)>=(3 epsilon/2)|t|
```

for all `0<|t|<=min(1/3,epsilon/(2L))`. The identity tuple supplies the
upper bound `f_W(t)<=L|t|`. A genuine triple-cover exclusion therefore
forces first-order, rather than second-order, optimal small-parameter
error on one fixed window.

The entire argument uses tuples on the same fixed window; multiplying
tensor powers does not require an additional closure condition on `W`.
The shared labels `g`, `h`, and `gh` remain shared after tensoring.

## Primary-source audit and the remaining mathematical task

[Bachner--Dogon--Lubotzky, *On L1-approximation of groups*,
arXiv:2508.17392v3](https://arxiv.org/html/2508.17392v3), dated
29 April 2026, explicitly leaves the existence of non-MF groups open.
Its Proposition 1.6 establishes norm-to-trace approximation for a finite
normal kernel over a hyperlinear quotient. It does not provide the
dimension-uniform operator gap for the Deligne triple cover.

[Dadarlat--Glebe, *Central Extensions and Almost Representations*,
Theorem 6.4](https://www.math.purdue.edu/~mdd/Webpapers/Central-extensions.pdf)
uses nonzero MF quotients at a sequence of small twists to obstruct
matricial stability. The criterion above makes explicit what is required
when one has only a single imperfect tuple at each small twist: the
projective error must be little-o of the twist parameter. No novelty
claim relative to all literature is made.

The finite-cover classification and scalar-corner arguments inspected in
`deligne-sep7-all-cover-mf-radical-classification-proof` remain sound.
They do not decide the branch. A proof must now supply either a genuine
finite-window gap at one-third, or a matrix construction with the specified
sublinear parameter error (which would refute the desired radical claim
by proving every finite cover MF). Neither is supplied by this artifact.

No executable code, build, numerical optimization, or local test was run
for this symbolic proof. The proof uses tensor telescoping, scalar phase
continuity, and the established finite-cover classification only.
