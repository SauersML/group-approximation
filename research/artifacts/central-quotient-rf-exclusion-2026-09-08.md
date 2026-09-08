# Central quotients of residually finite groups: an exclusion

2026-09-08.  Ingestion record for a fourth forwarded dossier
("central-quotients-rf-exclusion").  Every step was re-derived here before
any node was written.  The dossier makes no novelty claim and neither do
the nodes.

## The statement

`Lambda` countable residually finite, `Z <= Z(Lambda)`, `G = Lambda/Z`.
Then every nonidentity `g in G` has an operator-norm asymptotic
representation separating it in normalized Hilbert--Schmidt norm; `G` is
MF; and, consuming the Kazhdan transport collapse, `D_G(L) = 1` for every
property-(T) subgroup `L <= G`.  No finite generation, torsion or
finite-rank hypothesis on `Z`.

## What was re-derived

**Central character approximation.**  `C = Z(Lambda)`, `chi` a character of
`C`.  Fix `b_1,...,b_m in C` and `eps`, pick `N` with `2m/N < eps^2`, put
`mu_i` uniform on `{b_i^k : k < N}` and `mu = mu_1 * ... * mu_m` on the
abelian `B = <b_1,...,b_m>`.  Shifting `mu_i` cancels all but its two
endpoint terms, and convolution by a probability measure is an
`l^1`-contraction, so `||b_i mu - mu||_1 <= 2/N`.

With `F = supp mu`, residual finiteness gives a finite quotient `q` that is
injective on `F union b_1F union ... union b_mF` (separate each of the
finitely many nonidentity quotients of distinct pairs, then take the
product of those finite quotients).  Set
`xi(q(x)) = conj(chi(x)) sqrt(mu(x))` on `F` and `0` elsewhere, a unit
vector in `l^2(Q)`, well defined by the injectivity.  Checked here:

```text
(lambda_Q(q(b_i))xi)(q(x)) = xi(q(b_i^-1 x)),
conj(chi(b_i^-1 x)) = chi(b_i) conj(chi(x)),
```
so the two vectors differ pointwise only through the square roots and

```text
||lambda_Q(q(b_i))xi - chi(b_i)xi||^2
  <= sum_x |mu(b_i^-1 x) - mu(x)| <= 2/N,
```
using `(sqrt a - sqrt b)^2 <= |a - b|`.

`q(C)` is a finite central abelian subgroup of `Q`, so `l^2(Q)` splits into
joint eigenspaces `E_psi`, each invariant under all of `Q` by centrality.
Writing `xi = sum xi_psi` and using orthogonality,

```text
sum_psi ||xi_psi||^2 sum_i |psi(q(b_i)) - chi(b_i)|^2 <= 2m/N < eps^2,
```
and the weights sum to one, so some nonzero `E_psi` has
`|psi(q(b_i)) - chi(b_i)| < eps` for all `i`.  On `E_psi` the whole of `C`
acts by the scalar character `psi . q` -- not merely the chosen `b_i`,
because `E_psi` is a joint eigenspace for all of `q(C)`.  Exhaust `C` by
finite sets with `eps = 1/n`.

**Separation inside `C/Z`.**  For `g = cZ != 1` take a character of `C/Z`
nontrivial at `cZ` (T is divisible, so characters of a subgroup of a
countable abelian group extend) and pull it back to `chi` with
`chi|_Z = 1`, `chi(c) != 1`.  With a section `s`, `V_n = rho_n . s` has
`s(x)s(y)s(xy)^-1 in Z` central, so
`||V_n(x)V_n(y) - V_n(xy)|| = |chi_n(z_(x,y)) - 1| -> 0`, and
`||V_n(g) - I||_2 = |chi_n(s(g)) - 1| -> |chi(c) - 1| > 0` because
`s(g) in cZ` and `chi|_Z = 1`.  Both statements are dimension-free.

**Separation outside `C/Z`.**  For `gamma not in C` pick `h` with
`[gamma,h] != 1` and a finite quotient `q` keeping it nontrivial; then
`q(gamma)` is not central while `q(Z)` is, so `Lambda -> Q -> Q/Z(Q)`
kills `Z` and detects `g`.  Its left regular representation is exact with
`||V(g) - I||_2^2 = 2`.

**Assembly.**  The per-element sequences combine into one MF model by block
sums over an exhaustion; the operator norm of a block diagonal matrix is
the maximum of the block norms, and `||A||_2 <= ||A||_op`, so the
normalized-HS separations survive as operator-norm separations.  No
ultrafilter and no comparison of dimensions is needed.

**The defect conclusion.**  If `1 != d in D_G(L)` with `L` Kazhdan, keep the
individual sequence for `d` rather than the block sum.  Kazhdan transport
makes every `V_n(c)`, `c in C_G(L)`, an asymptotic commutant of the image
of `L` and carries that property through the compressor, so every
generator `[u c u^-1, l]` of `D_G(L)` has `||V_n(.) - I||_2 -> 0`,
contradicting the retained separation.

## Consistency checks against the graph

* **No conflict with the MF groups that keep a central defect.**
  `mf-group-with-finite-central-compression-defect` and
  `finite-order-central-compression-defect-survives-mf` both have `L`
  **infinite cyclic**, not Kazhdan.  The theorem here only kills `D_G(L)`
  for property-(T) `L`, so those witnesses stand, and they are exactly why
  the (T) hypothesis cannot be dropped from the third assertion.
* **It sharpens the Abels--Prüfer calibration rather than contradicting
  it.**  `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center` gives
  `Gamma_p = A_p / z(Z)` with `A_p <= GL_4(Z[1/p])` residually finite, and a
  central `c_p` killed by every **exact** finite-dimensional representation
  while visible in permutation microstates.  The theorem here applies to
  that same `Gamma_p` and adds that it is MF with `c_p` visible in an
  operator-norm asymptotic representation.  Exact invisibility and
  approximate visibility coexist; that gap is the content of the
  calibration, and this is an independent second route to its positive
  half.
* **It does not touch the non-MF constructions in the graph.**  The
  elementary groups of Leavitt and Jacobson rings, the dyadic
  finite-perturbation group and the perfect-lamp wreath products are not
  central quotients of residually finite groups, so nothing established is
  weakened.  In particular
  `kazhdan-self-embedding-has-sofic-perfect-lamp-non-mf-family` builds a
  wreath product, not a central quotient, and is untouched.

## Why the exclusion is worth recording

`defect-forces-proper-self-embedding` says a nontrivial compression defect
forces the core to embed in itself properly, and observes that co-Hopfian
cores are useless.  That makes non-Hopfian Kazhdan groups the obvious place
to look for a source, and Cornulier's finitely presented non-Hopfian
Kazhdan groups are the standard supply.  This theorem removes them: they
are `Gamma/Z` with `Gamma <= GL_r(Z[1/p])`, hence residually finite by
reduction modulo a prime other than `p` that misses the numerator of a
nonzero entry of `A - I`.

Reference checked: Yves de Cornulier, *Finitely presentable, non-Hopfian
groups with Kazhdan's Property (T) and infinite outer automorphism group*,
Proc. Amer. Math. Soc. **135** (2007) 951--959 -- Definition 2.4 specifies
the groups, Proposition 2.7 gives property (T) and non-Hopficity, Theorem
1.3 gives finite presentability; arXiv:math/0502140 carries the corrected
version with the 2011 erratum on Theorem 3.1.  Only the structural
identification is imported.

## Not asserted

This settles nothing about the locally finite normal-subgroup question
(`locally-finite-defect-subgroup-dies-in-every-corona` stays open), repairs
nothing, and produces no non-MF group.  It is an exclusion of a candidate
source.  The only non-elementary input is the Kazhdan transport collapse,
used only for the defect assertion; the MF half is elementary.  No Lean
certification is asserted.
