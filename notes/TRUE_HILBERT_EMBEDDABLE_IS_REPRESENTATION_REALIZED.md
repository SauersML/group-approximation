# A Hilbert embeddable length is exactly the HS metric of a representation

Date: 2026-08-14

## 0. Statement

Let `H` be a finite group and `ell` a real conjugation-invariant function with
`ell(1)=0` and `ell >= 0`.  Write `Irr(H)` for the irreducible characters,
`d_i = chi_i(1)`, and

```text
psi_i(h) = d_i - Re chi_i(h) = (1/2) ||pi_i(h) - 1||_F^2,             (HR1)
```

`||.||_F` the unnormalized Frobenius norm.

**Theorem.**  The following are equivalent.

1. `ell` is **Hilbert embeddable**: the kernel `(a,b) -> ell(a^(-1)b)` is
   conditionally negative definite.
2. `ell = sum_(i != triv) a_i psi_i` with all `a_i >= 0`.
3. `ell(h) = (1/2)||rho(h)-1||_F^2` for a finite-dimensional unitary
   representation `rho` of `H` with no trivial subrepresentation — exactly when
   the `a_i` of (2) are nonnegative integers, and up to an arbitrarily small
   uniform error and a positive scalar in general.

Consequently, normalizing by `dim rho = m`,

```text
ell(a^(-1)b) proportional to ||rho(a) - rho(b)||_(2,norm)^2.           (HR2)
```

**The content: a Hilbert embeddable invariant length on a finite group is not
merely convertible into unitary microstates — it *is*, up to a positive scalar,
the squared normalized Hilbert--Schmidt metric of an honest unitary
representation.**  The scalar is `2/dim rho` with `dim rho = mean_H(ell)`, so
it is uniformly controlled along a family; see §2, and note that the
`exp(-t ell)` step of `hilbert-embeddable-length-hyperlinearity` item 2 is
*not* thereby dispensable — it is what supplies scalar-freeness, which this
identity does not.

## 1. Proof

**(2) implies (1).**  `psi_i(a^(-1)b) = (1/2)||pi_i(a^(-1)b) - 1||_F^2
= (1/2)||pi_i(b) - pi_i(a)||_F^2` by unitary invariance of `||.||_F`.  That is
the squared distance between two points of the Hilbert space
`(M_(d_i)(C), ||.||_F)`, hence a conditionally negative definite kernel.
Nonnegative combinations of conditionally negative definite kernels are
conditionally negative definite.

**(1) implies (2).**  Expand the class function in characters,
`ell = sum_i b_i chi_i`.  The character criterion for an invariant length
(`hilbert-embeddable-length-hyperlinearity`, item 1) gives `b_i <= 0` for every
nontrivial `chi_i`.  From `ell(1) = 0` we get `sum_i b_i d_i = 0`, so
`b_triv = - sum_(i != triv) b_i d_i`, and therefore

```text
ell(h) = b_triv + sum_(i != triv) b_i chi_i(h)
       = sum_(i != triv) (-b_i)(d_i - chi_i(h)),
```

which is `(2)` with `a_i = -b_i >= 0` (taking real parts, which is harmless
because `ell` is real and conjugate characters are paired).

**(2) implies (3).**  For nonnegative integers `a_i` put
`rho = ⊕_i pi_i^(⊕ a_i)`; then `(1/2)||rho(h)-1||_F^2 = sum_i a_i psi_i(h)`
because the Frobenius norm is additive over direct sums.  For general
nonnegative reals, approximate the `a_i` by rationals and clear denominators;
the resulting `rho` realizes a positive scalar multiple of `ell` up to uniform
error `< delta` for any prescribed `delta`.

**(3) implies (2)** is the direct-sum decomposition of `rho`.  End proof.

## 2. Consequence A: the identity is exact, but it does NOT remove the
## normalization exposure — corrected

This section has been corrected twice.  The first version claimed the theorem
removes the uniformity-of-constants exposure in
`hilbert-embeddable-length-hyperlinearity` item 2, "because there is now one
scalar per witness and it is explicit, `s = 1/(2m)` with `m = dim rho`",
giving no reason why the scalar is controlled.  The correction that replaced
it asserted the opposite — that the scalar is *unbounded*, that
`dim rho_n -> inf` along a family, and that an exact realization therefore
delivers normalized separation `2c/dim(rho_n) -> 0`.

**That failure mode cannot occur** (`cairn-verify`, audit 2026-08-14).  The
normalization identity is right,

```text
||rho(a)-rho(b)||_(2,norm)^2 = 2 psi_rho(a^(-1)b) / dim(rho),         (HR5)
```

but `dim rho` is not a free parameter.  Since `sum_h chi_i(h)=0` for
nontrivial `i`, the mean of each generator is `mean_H(psi_i)=d_i`, so in the
trivial-free decomposition

```text
dim rho = sum_(i != triv) a_i d_i = mean_H(ell).                      (HR5a)
```

The dimension of the realizing representation *is* the average of the length.
And `psi_i <= 2 d_i` pointwise gives, for every Hilbert embeddable `ell`,

```text
max_h ell(h) <= 2 mean_H(ell).                                        (HR5b)
```

So a witness normalized to `ell <= 1` with separation `c` has
`mean_H(ell)` pinned into `[c/2, 1]`: by `(HR5)` the normalized-HS defect is
at most `4 delta/c` and the normalized-HS separation at least `2c`, both
uniform along any family.  Far from diverging, `dim rho <= 1` whenever
`ell <= 1` — which is precisely why exact *integral* realization of a
normalized length essentially never exists, and why statement 3 of the
theorem says "up to a positive scalar".

The discrete length does not calibrate the other way.  The regular
representation realizes `|K| * ell_discrete`, not `ell_discrete`, and
`mean(|K| * ell_discrete) = |K| - 1 = dim(lambda - triv)`, in agreement with
`(HR5a)`.  There is no representation at all with `psi_rho = ell_discrete`,
since that would need `dim rho = (|K|-1)/|K| < 1`.

The correct dimension-free formulation is via the **normalized character**.
Put `phi = chi_rho / dim rho`; then

```text
(1/2)||rho(a) - rho(b)||_(2,norm)^2 = 1 - Re phi(a^(-1)b),            (HR6)
```

and in cone coordinates, with `lambda_i = a_i d_i / dim rho` (so that
`sum_i lambda_i = 1`, a point of the simplex),

```text
1 - Re phi(h) = sum_i lambda_i ( 1 - Re chi_i(h)/d_i ).               (HR7)
```

So the right generators are the **normalized** functions
`g_i = 1 - Re chi_i / d_i`, indexed over irreducibles, with weights on the
simplex — not the unnormalized `psi_i = d_i - Re chi_i` with unconstrained
weights.  This is exactly what item 2 of the criterion produces through the
trace.  Note that the simplex constraint is not an alternative to `(HR5a)`
but the same fact restated: `mean_H(g_i)=1` for nontrivial `i`, so
`sum_i lambda_i = 1` and `dim rho = mean_H(ell)` say the same thing.  Both
close the exposure; neither leaves it open.

**What actually forbids substituting the identity for item 2 is
scalar-freeness, not normalization.**  `(HR5)` controls only
`Re tau(rho(h)) = 1 - ell(h)/dim rho` and leaves `|tau|` free, while
`|tau| = 1` holds exactly on scalars — where the upgrade to maximal
separation (`Sofic/HyperlinearAmplification.exists_conjDouble_separation`,
and equally plain tensor powers) is unavailable at any number of copies.  The
obstruction is realized.  On `Z/N` put

```text
ell(h) = (1/2)(1 - cos(2 pi h / N)).                                  (HR5c)
```

This is a Hilbert embeddable invariant length — the kernel test returns
conditionally negative definite, and it vanishes only at `h=0` — and its
exact realizer is the one-dimensional character `chi_1`, so **every** `rho(h)`
is a scalar and `|tau(rho(h))| = 1` for all `h != 0`.  On the same data the
Schoenberg trace `exp(-ell)` is real, positive and bounded away from `1`
(`0.708`, `0.828`, `0.935` for `N = 5, 7, 12`).  The identity and item 2
therefore compose; the identity does not replace it.

What survives from the theorem, and is still worth having, is the *cone
description itself*: the Hilbert embeddable invariant lengths are precisely the
nonnegative combinations of the `psi_i`, equivalently of the `g_i`.  Since
`psi_i = d_i g_i` and `d_i > 0`, the two generating sets span the same cone, so
every statement below phrased as a ratio or as a feasibility question over the
cone is unaffected by the choice.

## 3. Consequence B: the design question becomes a representation question

Combining with the extraction of Glebsky's data
(`glebsky-manufactured-invariant-length`,
`hilbert-embeddable-length-lp-feasibility`): a weak-soficity witness is a
finite group `H`, a map `phi : Phi -> H` with defect set
`X = {phi(g)phi(h)phi(gh)^(-1)}`, and a target set `T = phi(Phi ∖ {1})`
`n`-separated from `X`.  Asking for a Hilbert embeddable witnessing length is,
by the theorem, asking for a finite-dimensional unitary representation `rho` of
`H` with

```text
||rho(x) - 1||_(2,norm) small for x in X,
||rho(y) - 1||_(2,norm) >= c for y in T.                              (HR3)
```

and then `rho ∘ phi : Phi -> U(m)` **is** the hyperlinear microstate: it is
`(Phi, epsilon)`-multiplicative and `(Phi, c)`-separating by construction,
because `rho` is a genuine homomorphism and all defects of `rho ∘ phi` are
`rho(X)`.

So the following are equivalent for a countable group `K`:

* `K` is weakly sofic with Hilbert embeddable witnessing lengths;
* `K` admits hyperlinear microstates that **factor through a finite group** —
  `Phi -> H -> U(m)` with the second arrow a homomorphism;
* `K` is approximable by **finite subgroups of unitary groups**, in the
  normalized Hilbert--Schmidt metric.

Call that class `C_FU`.  Then

```text
sofic  ⊆  C_FU  ⊆  hyperlinear,                                       (HR4)
```

the first inclusion because permutation matrices give
`||sigma - 1||_(2,norm)^2 = 2 d_Hamming(sigma, 1)`, so the normalized Hamming
length is `psi` of the standard permutation representation minus its trivial
summand.

## 4. What this does and does not settle for the Kun--Thom wreath

It converts `hilbert-embeddable-witness-for-kun-thom-wreath` from a metric
design problem into the membership question **`W ∈ C_FU`?**, with no length to
design: one has to produce finite subgroups of `U(m)` approximating `W`, or
show none exist.  Three consequences for how to attack it.

* The two constraints recorded there survive unchanged and are now
  representation-theoretic.  "No dilution of a single lamp" says
  `||rho(a_o) - 1||_(2,norm)` must stay bounded below, i.e. the multiplicity
  vector of `rho` must keep mass on characters that separate a single lamp.
  "No finite-quotient witness" says `rho ∘ phi` cannot be a genuine partial
  homomorphism, i.e. `rho` cannot kill the normal subgroup generated by the
  defect set.
* The linear program of `hilbert-embeddable-length-lp-feasibility` is now a
  program in the **multiplicity vector** `(a_i)_(i in Irr(H))`, with the
  constraints `(HR3)` read off the character table.  Its dual certificate,
  if infeasible, is a positive combination of characters — a genuinely
  computable obstruction.
* `C_FU` is a class strictly between the two settled facts about `W`: `W` is
  weakly sofic and `W` is not sofic.  Whether `C_FU = hyperlinear` is itself
  open and is not needed: only `W ∈ C_FU` is at issue, and it suffices.

## 5. Scope

Proved here: the Theorem of §0 and the equivalences of §3.  Item 1 of
`hilbert-embeddable-length-hyperlinearity` (the character criterion) is used
for the direction (1) implies (2) and is not reproved; every other step is
self-contained.

Not proved: that `W ∈ C_FU` or that `W ∉ C_FU`; that `C_FU` equals the class of
hyperlinear groups; anything about whether Glebsky's construction can be
steered into `C_FU`.
