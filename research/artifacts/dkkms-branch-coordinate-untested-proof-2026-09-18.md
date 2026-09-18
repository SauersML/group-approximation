# Seeds are subspaces of smoothed tuple spaces, so a direction is linkable only when a smoothing keeps it, which costs one factor 1 - 3 beta / 4 per block; the resulting seed weight at an A-vertex is an exact block dynamic program and it concentrates on one hyperplane

*Attempt artifact (2026-09-18, wave `swarm-0917`, lane `e2-w2-ugc-selector-kill`),
written as route `dkkms-branch-coordinate-untested-proof` into
`dkkms-smoothing-leaves-the-branch-coordinate-untested` with
`requires: [dkkms-2to1-instances-satisfy-selector-decoding-hypotheses,
grassmann-restriction-test-is-99-percent-rigid,
orientation-lifts-sandwich-2to1-game-values]`, artifact
`experiments/grassmann-99-rigidity-2026-09-18/seed_spread_dkkms.py`.*

**REFUTED at Corollary 3 by referee lens 2 of the wave's three-lens stage, and
the same step was independently named by lens 1 as "the first step that does not
follow".** Lemma 1 is proved with an existential/single-constraint quantifier
and Corollary 3 then uses it with a universal one. Lemmas 1, 2 and the
block dynamic program are correct and are kept; the universal sentences drawn
from them are not. The refutation is reproduced verbatim in the `## Attempts`
entry of `dkkms-smoothing-leaves-the-branch-coordinate-untested`, and the
surviving narrow statement is recorded there. Do not promote this back to a
`kind: route` node until the gap at Corollary 3 is closed.

**Where it dies, in one paragraph.** By item 1 of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` the constraint is
exactly 2-to-1 and the unfolding `Fun(R_C) -> Fun(L)` is a bijection, so an
A-label is a *linear functional on `L`*. Two constraints at the **same**
A-vertex `(U,L)` with distinct seeds `R1 != R2` are two distinct hyperplanes of
`L`, so `R1 + R2 = L` and together they pin `A(U,L)` at every direction of `L`,
with neither seed required to contain the direction. Lemma 2's factor
`(1 - 3 beta / 4)^k` is the cost of a second seed through a prescribed
direction only under Corollary 3's *different-target* conditioning, which is
the right conditioning for the six-flag gadget (whose auxiliary flags sit at
`N = P + <x,y> != L`) and the wrong one for an agreement argument that is free
to use two queries at one A-vertex. Lens 2 measured the same-A-vertex quantity
with this file's own exact rational dynamic program: at `l = 3`, `beta = 1/2`
it is `0.2925, 0.3128, 0.2400, 0.2224, 0.1524, 0.1138, 0.1348` for `k = 2..8`
against `(1 - 3 beta / 4)^k = 0.3906, 0.2441, 0.1526, 0.0954, 0.0596, 0.0373,
0.0233` — the ratio grows from `0.75` to `5.8` with `k`, so
`(1 - 3 beta / 4)^k` is not the invariant for that conditioning.

All notation is imported verbatim from
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`, which quotes ECCC
TR16-198 Section 4.2. Recall from there:

* `A = {(U,L) : U in cal U, L in Gr(X_U, l), L cap H_U = {0}}`,
  `B = {(V,L') : V in cal V, L' in Gr(X_V, l-1)}`;
* the edge process: `U` uniform; `V` with the `i`-th element the equation `e_i`
  with probability `1 - beta` and a variable of `e_i` (uniform among its three)
  with probability `beta`; then `L' in Gr(X_V, l-1)` uniform and
  `L in Gr(X_U, l)` uniform with `L' <= L`; outputs are restricted to
  `(U,L) in A` and the weights renormalised;
* `G_multi` has one constraint per output `((U,L),(V,L'))`, accepting
  `sigma in Fun(R_C)` and `sigma' in Fun(L')` iff `A(U,L)|_(L') = sigma'`, where
  `A(U,L)` is the unfolding of the class label;
* annotation: each `G_multi` constraint is split into `2^(l-1)` equal-weight
  copies, one per `x in L \ L'`, with seed `(V,L')`, target `U`, direction `x`.

Write `X_U = F_2^(3k)` as `k` **blocks** of three variables, block `i` being the
variables of `e_i`; `H_U = Span(x_(e_1),...,x_(e_k))` where `x_(e_i)` is the
all-ones vector of block `i`.

## Lemma 1

*Statement.* A constraint of `G_multi` with A-endpoint `(U,L)` and seed
`(V'', R)` constrains the value `A(U,L)(x)` only if `x in R`; and then
`x in R <= X_(V'')`.

*Proof.* The constraint reads `A(U,L)|_R = sigma'_R`. Two A-labels that agree on
`R` satisfy it together, so it says nothing about the value at any `x notin R`.
By the definition of `B`, `R in Gr(X_(V''), l-1)`, so `R <= X_(V'')`. QED

Two remarks. First, the same is true of the *annotated copies*: a copy with seed
`(V'',R)` and direction `x_e in L \ R` prescribes the branch through
`g_e(sigma') = A(U,L)(x_e)` (annotation item of the membership node), so it
*reports* the value at `x_e` but the underlying `G_multi` constraint does not
*pin* it. Second, `V'' = U` is always a legal smoothing, and then
`X_(V'') = X_U >= L`, so every hyperplane of `L` is a legal seed; the content is
entirely in the weights.

## Lemma 2

*Statement.* For `x` uniform in `X_U` and `V''` a fresh smoothing of `U`
independent of `x`, `Pr[x in X_(V'')] = (1 - 3 beta / 4)^k`.

*Proof.* `X_(V'')` is the coordinate subspace spanned by the variables `V''`
keeps, and the keeping decisions are independent across blocks, as are the three
coordinates of `x` in each block. Fix a block `i` and let
`s := |supp(x) cap block_i| in {0,1,2,3}`, with probabilities
`1/8, 3/8, 3/8, 1/8`. With probability `1 - beta` the block keeps the equation
and contributes all three coordinates, so the block condition holds. With
probability `beta` it keeps a single uniform variable `v`, and the block
condition is `supp(x) cap block_i subset {v}`: this has conditional probability
`1` if `s = 0`, `1/3` if `s = 1` (the one variable in the support must be the
chosen `v`), and `0` if `s >= 2`. Hence the per-block probability is

```text
(1 - beta) + beta * ( 1/8 * 1 + 3/8 * 1/3 + 3/8 * 0 + 1/8 * 0 )
  = (1 - beta) + beta/4  =  1 - 3 beta / 4,
```

and multiplying over the `k` independent blocks gives the claim. QED

## Corollary 3

*Statement.* Let `x` be a direction drawn from the game's own direction law at a
target `U`, and independently let a second constraint of `G_multi` at the same
target be drawn from the edge law. Then

```text
Pr[ the second constraint's seed R satisfies x in R ]  <=  (1 - 3 beta/4)^k + 2^(l-1-2k).
```

*Proof.* The second constraint's seed is a pair `(V'', R)` with
`R in Gr(X_(V''), l-1)`, so `x in R` implies `x in X_(V'')`, and `V''` is drawn
from the smoothing law independently of `x`. By item 3 of the membership node
the direction `x` is uniform on `X_U \ (L' + H_U)`, whose total variation
distance from uniform on `X_U` is `2^(l-1-2k)`. Apply Lemma 2 and add that
error. QED

*Remark (legality is not the point).* Many smoothings do contain a given `x`,
and `V'' = U` always does, so every hyperplane of `L` is a legal seed. What
Corollary 3 bounds is the total *weight* those seeds carry under the edge law,
and that is what a union bound over uses of the test spends.

**Refuted extension (referee lens 2, 2026-09-18).** The route originally
continued: "Every argument that pins the value of an A-label at `x` needs such
a second constraint." That does not follow, and it is the load-bearing sentence
of the whole node. Corollary 3 conditions on a second constraint drawn at the
same *target* `U`, i.e. at a fresh A-space; the quantifier "every argument"
ranges over all pairs of constraints, including two at the same *A-vertex*
`(U,L)`, where two distinct hyperplane seeds span `L` and pin every direction
at `O(1)` cost. What survives is the narrow statement: the six-flag gadget of
`grassmann-restriction-test-is-99-percent-rigid` places its three
direction-certifying auxiliary flags at `N = P + <x,y> != L`, so for *that*
gadget the different-target conditioning is the right one and its flags do
carry total game weight `<= (1 - 3 beta / 4)^k + 2^(l-1-2k)`. Everything below
this line is stated for that gadget only.

*Consequence for the six-flag gadget.* Step 1 of the rigidity proof bounds the additive defect of the
prediction function by `6 eps`, where `eps` is the rejection rate of a *uniform*
flag. On `G_multi` the six flags are not uniform: the three that certify a
direction sit on seeds of total weight at most `(1 - 3 beta / 4)^k`, so the
bound becomes
`6 eps (1 - 3 beta / 4)^(-k)`. With `beta` a fixed positive constant and `k` as
large as the DKKMS parameter choice takes it (item 7 of the membership node fixes
`k` by `exp(-k/exp(ql)) < p^2/8` with `p = (gamma/2)^3 2^(-l-2)`, so
`k >= exp(ql) * ((2l + 7) log 2 + 6 log(2/gamma))`), that factor is
`exp(Theta(beta k))` and the bound is vacuous. There is no choice of `l` and `k`
admissible for Corollary A of
`high-advantage-selector-witnesses-decode-good-outer-labellings` at which *this
gadget* transfers.

*(Referee lens 2 correction, 2026-09-18: the route previously wrote the
parameter bound as `k >= exp(ql)(3l + O(1)) log 2`, which is not what item 7 of
the membership node gives; the form above is. The conclusion is unaffected,
since both grow like `exp(ql) * Theta(l)`.)*

## The seed weight at an A-vertex

*Statement.* For a hyperplane `R < L` with `R cap H_U = 0`, the conditional
probability `w(R|L)` that an edge with A-space `L` has seed `R` is proportional,
with a constant depending only on `(l,k)`, to

```text
S(R)  =  sum_(V'' : R <= X_(V'')) Pr[V''] / |Gr(X_(V''), l-1)| .
```

*Proof.* Condition on `U`. The process draws `V''`, then `R` uniform in
`Gr(X_(V''), l-1)`, then `L` uniform in `Gr(X_U,l)` with `L > R`, and keeps the
output iff `L cap H_U = 0`. So the unrenormalised weight of the ordered pair
`(R, L)` is `sum_(V'' : R <= X_(V''))  Pr[V''] / |Gr(X_(V''), l-1)|` times
`1 / #{ L'' in Gr(X_U,l) : L'' > R }` times `1{L cap H_U = 0}`. Now
`#{ L'' > R } = (2^(3k) - 2^(l-1)) / (2^l - 2^(l-1))` depends only on `(l,k)`,
and for `R cap H_U = 0` the admissible extensions are
`L = R + <z>` with `z notin R + H_U`, of which there are
`(2^(3k) - 2^(l-1+k)) / 2^(l-1)`, again depending only on `(l,k)`. Every
hyperplane `R` of an admissible `L` has `R cap H_U = 0`. Dividing by the sum over
the hyperplanes of `L` gives the claim. QED

*Computation.* `Pr[V'']` and the condition `R <= X_(V'')` both factorise over
blocks, while `|Gr(X_(V''), l-1)|` depends on `V''` only through the number `j`
of smoothed blocks (`dim X_(V'') = 3k - 2j`). So `S(R)` is a sum over `j` of a
block-product, computed exactly by a dynamic program that tracks `j`. At block
`i` the admissible single variables are those `v` with
`proj_i(R) subset <v>`: all three when `proj_i(R) = 0`, exactly one when
`proj_i(R)` is a line spanned by a variable, none otherwise. The artifact
implements exactly this, in `Fraction` arithmetic.

*Measured values.* See the claim node; with `l = 3` (uniform spread `1/7`) the
mean of `max_R w(R|L)` rises from `0.4776` at `k = 2` to `0.8397` at `k = 8` for
`beta = 1/2`, the dominant hyperplane is the generating seed for `0.90` of the
A-mass at `k = 8`, and the `beta = 0` control returns `1/7` exactly.

*(Referee correction, 2026-09-18: all three lenses re-ran
`seed_spread_dkkms.py` and found that this paragraph previously quoted
"`0.365` at `k = 2` to `0.831` at `k = 8`", which the artifact does not
produce. The claim node quoted it correctly throughout; only this file was
stale. The numbers above are what the script prints.)*

## Proposition 4

*Statement and proof* as in the claim node. Three points deserve the detail.

**(a) The labelling.** Put `tau_(V,R) := 0 in Fun(R)` at every seed. On the
A-side, folding fixes the unfolding: a class label `sigma_C in Fun(R_C)` unfolds
at `(U,L) in C` to `tilde sigma_U|_L`, where `tilde sigma_U` is the linear
functional on `M := R_C + H_U` with `tilde sigma_U|_(R_C) = sigma_C` and
`tilde sigma_U|_(H_U) = h_U` (Definition 4.2 of the paper, quoted in the
membership node). The hypothesis of folding-compatibility is that `sigma_C` can
be chosen with `ker(tilde sigma_U) cap L = D(L)` for most members. Note
`tilde sigma_U != 0` whenever `h_U != 0`, and for `L cap H_U = 0` the restriction
`tilde sigma_U|_L` is unconstrained by `h_U`, so `ker(tilde sigma_U) cap L` is a
hyperplane of `L` for all but a `~2^(-l)` fraction of the members.

**(b) The value.** An edge with A-space `L` and seed `R` is satisfied iff
`tilde sigma_U|_R = tau_R = 0` iff `R <= ker(tilde sigma_U)` iff `R = D(L)` (the
kernel meets `L` in one hyperplane). By hypothesis that has conditional weight
`>= 1 - xi` on a `1 - delta - delta'` fraction of the A-mass.

**(c) The distance.** Agreement with `hon_kappa(lambda)` at a clean copy of
`(U,L)` means `tilde sigma_U|_L = lambda_U|_L`, hence
`lambda_U|_(D(L)) = 0`. The hypothesis takes `D(L) = L'`, the seed that
generated `L`, and `L = L' + <x>` with `L'` uniform in `Gr(X_V, l-1)`, so for a fixed
`lambda_U` this forces `L' <= ker(lambda_U)`, an event of probability
`|Gr(ker(lambda_U) cap X_V, l-1)| / |Gr(X_V, l-1)| <= 2^(1-l)`. Adding the dirt
`d_kappa(lambda)` covers the unclean copies. Since `lambda_U` ranges over one
functional per `k`-tuple, no union bound over `lambda` is needed.

*Unfilled case (referee lens 1, 2026-09-18).* The bound `2^(1-l)` assumes
`lambda_U|_(X_V)` is not identically zero; if it is, every `L'` lies in the
kernel and the ratio is `1`. Proposition 4 is explicitly conditional on
folding-compatibility, which is posted as open, so this does not propagate, but
it has to be filled before the proposition is used. Lens 1 also recorded a
consistency check worth keeping: if folding-compatibility were provable by pure
geometry it would hand `G_multi` a value-`(1-o(1))` labelling on NO instances
too, contradicting DKKMS soundness, so that sub-statement must be
instance-dependent or false.

**(d) The lift.** By item (5) of `orientation-lifts-sandwich-2to1-game-values`
the branch is `o_e(sigma) = sigma(x_e) xor g_e(sigma|_(L'))`. On a satisfied edge
the A-label vanishes on the seed `D(L)` and `x_e in L \ D(L)`, so
`sigma(x_e) = 1`. Taking `g_e := 1` for every `e` and every argument (a constant,
hence polynomial-time, orientation) gives `o_e = 0`, matched by the right bits
`b_(V,L') := 0`. So the lift value equals the `G_multi` value.

## The open sub-statement

Folding-compatibility of the dominant germ `L |-> D(L)` is the whole remaining
content. It is posted as a need; a clean sufficient form is:

> For all but `delta'` of the A-mass there is a class label `sigma_C` with
> `ker(tilde sigma_(U))  cap L = L cap X_(V(L))` for the smoothing `V(L)` of
> maximal seed weight at `L`.

A single class `C` over a window `U` carries `l` free bits and has many members,
so this is an over-determined linear condition; whether it has a solution on most
of the mass is a question about how the classes `L + H_U = R + H_U` cut across
the smoothing spaces `X_V`, and nothing in the graph answers it.
