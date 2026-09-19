# An explicit cocycle for the finite split-clock Schur class

Date: 2026-08-11

## 1. Outcome

The growing Schur class in
`FALSE_SPLIT_SQUARE_ZERO_H2_AMPLIFIER.md` has a closed cocycle formula.  It
is not necessary to compute a resolution or a Schur cover in order to
evaluate the class on presentation relators.

Fix an odd prime `p` and `k>=1`, and put

`q=1+p`, `M=p^k`, `n=p^(k+1)`.

Let

`B_k=<h,c | h^n=c^M=1, c h c^-1=h^q>`               `(SCC1)`

and let

`J_k=Aug_(Z/n)(C_M)`.                                 `(SCC2)`

Write `e_0,...,e_(M-1)` for the cyclic permutation basis and let `c` act
by `S e_j=e_(j+1)`, while `h` acts trivially.  Put

`G_k=J_k semidirect B_k`.                             `(SCC3)`

Define

`lambda_k:J_k->Z/n`,

`lambda_k(x)=sum_(j=0)^(M-1) x_j q^(-j) mod n`.       `(SCC4)`

Then `lambda_k(Sx)=q^(-1)lambda_k(x)`.  There is a
`1`-cocycle

`alpha_k:B_k->J_k^*=Hom(J_k,Z/n)`                    `(SCC5)`

determined by

`alpha_k(h)=lambda_k`, `alpha_k(c)=0`.                `(SCC6)`

For `(x,g),(y,t) in G_k`, the formula

`omega_k((x,g),(y,t))=alpha_k(g)(g.y) in Z/n`         `(SCC7)`

is a normalized `2`-cocycle.  Its cohomology class has exact order `p^k`
and is dual to the finite clock summand in `H_2(G_k;Z)`.

Thus `(SCC7)` is a proof-producing projective model: the finite central
extension is `Z/n times_(omega_k) G_k`, and every word phase is obtained by
straight evaluation of one modular formula.

## 2. The clock functional

The inverse `q^(-1)` exists modulo `n`.  Since `q` has order `M` modulo
`n`, the coefficients in `(SCC4)` are cyclic.  Direct reindexing gives

`lambda_k(Sx)=q^(-1)lambda_k(x)`.                     `(SCC8)`

On the distinguished augmentation vector,

`lambda_k(e_0-e_1)=1-q^(-1) mod n`.                  `(SCC9)`

The right side has `p`-adic valuation exactly one.  Its additive order in
`Z/p^(k+1)` is therefore exactly `p^k`.

Every difference `q^(-i)-q^(-j)` is divisible by `p`, so the image of
`lambda_k` lies in `p(Z/n)`.  Equation `(SCC9)` shows that the image is
exactly that subgroup.  Hence `lambda_k` itself has exact order `p^k` in
the dual group.

## 3. Verification of the one-cocycle

Give `J_k^*` the contragredient left action

`(g.f)(x)=f(g^(-1).x)`.                               `(SCC10)`

The assignment `(SCC6)` respects the presentation `(SCC1)`.  First,

`alpha_k(h^n)=n lambda_k=0`,
`alpha_k(c^M)=0`.                                     `(SCC11)`

Next, `h` acts trivially on `J_k`, while `(SCC8)` gives

`(c.lambda_k)(x)=lambda_k(S^(-1)x)=q lambda_k(x)`.    `(SCC12)`

Therefore

`alpha_k(c h c^(-1))=c.lambda_k=q lambda_k`
`                         =alpha_k(h^q)`.             `(SCC13)`

The universal property of the presentation now gives a well-defined crossed
homomorphism satisfying

`alpha_k(gt)=alpha_k(g)+g.alpha_k(t)`.                `(SCC14)`

## 4. Verification of the two-cocycle

Use the semidirect-product convention

`(x,g)(y,t)=(x+g.y,gt)`.                              `(SCC15)`

For a third element `(z,u)`, the left side of the additive cocycle identity
for `(SCC7)` is

`alpha_k(g)(g.y)+alpha_k(gt)(gt.z)`.                  `(SCC16)`

Using `(SCC14)`, its second term is

`alpha_k(g)(gt.z)+alpha_k(t)(t.z)`.                   `(SCC17)`

The right side is

`alpha_k(t)(t.z)+alpha_k(g)(g.(y+t.z))`,              `(SCC18)`

which is the same expression.  Normalization follows from
`alpha_k(1)=0`.  Hence `(SCC7)` is a normalized `2`-cocycle.

## 5. Exact order and pairing

The finite metacyclic descent identifies the clock homology generator with
the `h`-coordinate represented by `e_0-e_1`.  Its pairing with `(SCC5)` is

`alpha_k(h)(e_0-e_1)=1-q^(-1) mod n`,                `(SCC19)`

which has exact order `p^k` by `(SCC9)`.  Thus the cohomology class of
`alpha_k`, and consequently the mixed class `(SCC7)`, have order at least
`p^k`.  They have order at most `p^k` because every value of `lambda_k`
lies in `p(Z/n)`.  Their order is exactly `p^k`.

Equivalently, pushing out `(SCC7)` by the primitive character

`a |-> exp(2 pi i a/n)`                               `(SCC20)`

produces a projective multiplier whose marked clock pairing is the phase

`exp(2 pi i (1-q^(-1))/n)`,                           `(SCC21)`

of exact order `p^k`.

## 6. Relevance to the folded double

The remaining FALSE task is no longer to locate an abstract element in a
computed Schur multiplier.  It is to globalize the explicit cocycle `(SCC7)`
to a finite quotient of the full Kun--Thom vertex and then evaluate the fixed
vertex relators under that global cocycle.  Those evaluations give the
curvature vector `zeta_k` in
`FALSE_FOLDED_DOUBLE_PROJECTIVE_GAUGE_CRITERION.md`.

The formula also makes failures informative.  Restriction, corestriction,
and double-coset terms can be evaluated on `(SCC7)` without constructing
unitary matrices.  If globalization succeeds, only the final `2d` scalar
gauge variables remain; if it cancels, the exact modular term responsible
for cancellation is visible.

