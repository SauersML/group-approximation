# Compact-summand cancellation for real-rank-zero pure coefficient fields

Date: 5 September 2026. Complete proof; internal mathematical review completed.
This proves cancellation for arbitrary positive section classes and
closure of the first-factor image under removing compact summands.
It does not prove mixed target realization or full LXXVI.

The root reviewer checked ordered projection-frame cancellation,
the local continuity and uniform gap of positive support projections,
the closed cutoff equality core, compact stage lifting and the Cu-limit
comparison passage, and the actual extraction of a compact source
module. No unresolved gap was found. This is internal review, not
external peer review or formal verification.

## The theorem

Let `D` be separable, simple, stably finite, pure, and real rank zero,
and let `X` be compact metrizable. For every projection
`p in C(X,D tensor K)` and positive sections `a,b` in the same
stabilized section algebra,

`[p]+[a] <= [p]+[b]` implies `[a]<=[b]`.              (1)

In particular this holds with `D tensor Z` in place of `D`. No
stable-rank-one hypothesis on the section algebra is assumed.

The proof uses coefficient stable rank one (Lin), cancellation of
a projection summand in the coefficient Cu semigroup
(Rordam--Winter, Proposition 4.2), and the already proved exact
strict relative positive-embedding theorem for these coefficients.
The latter is applied only on finite-dimensional compact bases.

## 1. Ordered cancellation for projection bundles

First let `X` be finite-dimensional compact metrizable, put
`B=D tensor K`, and suppose `p,q,r` are continuous projection
sections with

`[p]+[q] <= [p]+[r]`.                                (2)

Projection comparison supplies an actual isometric embedding
`V:(p direct_sum q)B -> (p direct_sum r)B`, continuous over `X`.
All modules here are projection section modules, not just fiber
classes. Write `Q=p direct_sum r` for the target projection.

The zero locus of `r` is clopen. On it, evaluation of (2) and
finiteness of the coefficient projections force `q=0`: an embedding
of `p(x) direct_sum q(x)` into `p(x)` would otherwise make a finite
projection equivalent to a proper subprojection. Comparison of
`q` with `r` is therefore automatic there.

On the remaining compact clopen set, `r(x)!=0` everywhere. Consider
the two `p`-frames in `QB`: the restriction `V_p` of `V` to its
first summand, and the canonical first-summand inclusion `j_p`.
At every point with `p(x)!=0`,

`[p(x)] < [Q(x)]`.

Indeed `p(x)` is a proper subprojection of the finite projection
`Q(x)`, so the two cannot be Murray--von Neumann equivalent.
Apply the exact strict relative positive-embedding theorem on
`X x [0,1]`, with source projection `p`, target projection `Q`,
and the prescribed endpoint frames `V_p,j_p`. It gives a continuous
path of actual frames `T(x,t)` joining them. The theorem allows
zero source fibers; they require no separate strictness assertion.

Close frames with the same initial projection are carried to each
other by a target unitary given by the polar transport formulas in
the relative-embedding artifact. Uniform continuity on the compact
parameter space permits a finite subdivision in `t`; composing
these continuous close-frame transports gives a unitary section
`U` of the corner with unit `Q`, satisfying

`U V_p=j_p`.

The image under `UV` of the second source summand is orthogonal to
the canonical first summand and hence lies in `rB`. It gives an
actual continuous embedding of `qB` into `rB`. Combining the two
clopen pieces proves `[q]<=[r]`.

This proves ordered projection-bundle cancellation. It does not
infer cancellation from a K0 equality, nor use stable rank one of
`C(X,D)`. The parameter space of the frame homotopy is genuinely
`X x [0,1]`, with the entire two endpoint sections prescribed.

## 2. Continuous compact fiber type forces a uniform support gap

We need a separate support lemma, since compactness in every fiber
alone does not automatically say that a chosen section has a
uniform spectral gap.

**Support lemma.** Let `K` be compact metrizable, let
`h in C(K,B)_+`, and let `r in C(K,B)` be a projection such that

`[h(x)]=[r(x)]` in `Cu(B)` for every `x in K`.

Then `s(x)=supp(h(x))` is a continuous projection section, and
there is `delta>0` such that

`spec(h(x)) subset {0} union [delta,infinity)`

for all `x`. In particular `[h]=[s]` globally.

**Proof.** The zero locus of `r` is clopen, and `h` vanishes there.
Work near a point `x_0` of its complement. The fiber class of
`h(x_0)` is compact. Brown--Ciuperca, Theorem 3.5, applied to the
stable finite coefficient `B`, shows that its actual support
`s_0` belongs to `B` and `h(x_0)` is invertible in `s_0Bs_0`.
Let `e` be that corner inverse, extended by zero outside `s_0`.

Near `x_0`, the element `e h(x)^2 e` is invertible in `s_0Bs_0`.
The formula

`v_x=h(x)e (e h(x)^2 e)^(-1/2)`

defines continuous partial isometries with `v_x*v_x=s_0`,
`v_(x_0)=s_0`, and range projections `s'_x=v_xv_x*` in
`Her(h(x))`. Shrink the neighborhood so that `r(x)` is equivalent
to `r(x_0)`. Then

`[s'_x]=[s_0]=[h(x_0)]=[r(x_0)]=[r(x)]=[h(x)]`.

Every `h(x)` has compact fiber class. Brown--Ciuperca therefore
gives its actual support projection `s_x in B`. We have
`s'_x<=s_x` and equal Cu classes. These are equivalent projections;
finiteness of `s_x` forces `s'_x=s_x`. Thus the actual support is
continuous near `x_0`.

Use the polar unitary for nearby projections to transport `s_x`
back to `s_0`. In this fixed corner the transported `h(x)` varies
continuously and equals the invertible element `h(x_0)` at `x_0`.
It remains bounded below on a smaller neighborhood. Compactness
supplies finitely many such neighborhoods and one positive lower
bound for all nonzero fibers. The clopen zero locus causes no
problem. This proves the lemma. QED.

The continuous projection `r` specifying the fiber type is
essential in this proof. It is not replaced by a bare assertion
that all fiber classes happen to be compact.

## 3. Cancellation for arbitrary positives on finite-dimensional bases

Assume `X` is finite-dimensional compact metrizable and that the
inequality in (1) holds. After harmless positive rescaling assume
`a,b` are contractions. Evaluation and coefficient compact-summand
cancellation give

`[a(x)]<=[b(x)]` for every `x`.

Fix `0<eta<1`, put `c=(a-eta)_+`, and form

`E_eta={x : [c(x)]=[b(x)]!=0}`, `K=closure(E_eta)`.

The following cutoff-core argument includes its spectral details.
At a point of `E_eta`,

`[c(x)]=[a(x)]=[b(x)]`.

Since `[c(x)]<<[a(x)]`, the common class is compact. The actual
support projections of `a(x)` and `c(x)` belong to `B`; the
second is a subprojection of the first with the same Cu class.
Finiteness makes them equal. Consequently

`spec(a(x)) subset {0} union (eta,infinity)`

and `||a(x)||>eta`. By norm and spectral continuity, on `K` we have

`spec(a(x)) subset {0} union [eta,infinity)`,
`||a(x)||>=eta`.

Functional calculus therefore gives a continuous support projection
`r=supp(a|K)` and `[a|K]=[r]`.

The equality of fiber classes persists on `K`. Indeed, for `y in K`
and any `epsilon>0`, choose `x in E_eta` close enough that
`||b(y)-b(x)||<epsilon` and `||r(y)-r(x)||<1`. Positive-element
perturbation and equivalence of close projections give

`[(b(y)-epsilon)_+] <= [b(x)]=[r(x)]=[r(y)]`.

Take the supremum over `epsilon` to get `[b(y)]<=[r(y)]`.
The opposite inequality follows from the already known fiberwise
comparison. Thus `[b(y)]=[r(y)]` on `K`.

The support lemma now gives an actual continuous projection
`s=supp(b|K)` and a uniform spectral gap for `b|K`. In particular
`[b|K]=[s]`. Restrict the original global comparison to `K`:

`[p|K]+[r] <= [p|K]+[s]`.

The compact set `K` is finite-dimensional. Section 1 cancels the
projection summand and gives `[r]<=[s]`. Choose an actual continuous
partial isometry `t` on `K` with `t*t=r` and `tt*<=s`, and put

`z_K=t(c|K)^(1/2)`.

Then `z_K*z_K=c|K`, and its range lies in the hereditary module
of `b|K`. Off `K`, the inequality `[c(x)]<=[b(x)]` is strict
whenever `c(x)!=0`; otherwise `x` would belong to `E_eta`.
The exact strict relative positive-embedding theorem extends `z_K`
to a global `z` with

`z*z=c`, `zz* in Her(b)`.

If `K` is empty, apply the same theorem with empty boundary.
It follows that `(a-eta)_+ precsim b`. Taking all positive cutoffs
proves `a precsim b` and completes (1) in finite dimension.

## 4. Passing compact cancellation through sequential Cu limits

We state the limit step precisely. Suppose `S_i` are a sequential
system of Cu semigroups in which cancellation holds for the compact
elements under consideration. Suppose a compact element `z` in
the limit `S` is the image of a compact stage element `z_i`, whose
later images admit that cancellation. Then

`z+x<=z+y` implies `x<=y`.

Fix `x'<<x`. The usual approximation properties of the Cu limit
give, at some stage, elements

`u_0<<u_1<<u_2`, with `x'<=alpha(u_0)` and `alpha(u_2)<=x`.

This three-cutdown version follows by first approximating a class
strictly between `x'` and `x` by a stage image, and then taking
three cutdowns of its stage representative. Write `y` as an
increasing supremum of stage images `beta(y_j)`. Since `z` is
compact,

`z+alpha(u_1) << z+alpha(u_2) <= z+x <= z+y`.

For some `j` we therefore have
`z+alpha(u_1)<=z+beta(y_j)`. Bring the representatives and `z_i`
to a common stage. The comparison clause for Cu limits, applied
to `z_i+u_0<<z_i+u_1`, gives at a later stage

`z_k+alpha_k(u_0) <= z_k+beta_k(y_j)`.

Stage cancellation gives `alpha_k(u_0)<=beta_k(y_j)`, hence
`x'<=y` in the limit. Taking all `x'<<x` proves the assertion.

Now embed a compact metrizable `X` in the Hilbert cube and let
`X_i` be its first `i` coordinate images. These are finite-dimensional
compact metrizable spaces, their inverse limit is `X`, and

`C(X,D)=lim_i C(X_i,D)`

under the coordinate pullbacks. A projection in the limit is
equivalent to a projection from a stage: approximate it closely
by a self-adjoint stage element, apply the spectral projection
cut at `1/2`, and use equivalence of close projections. Its Cu
class thus has exactly the compact stage lift required above.
Cu continuity and Section 3 prove (1) for every compact metrizable
`X`. This also proves all-base projection-bundle cancellation as
a special case.

For completeness the same statement holds for `C_0(X,D)` when
`X` is second-countable locally compact Hausdorff: embed it as an
ideal of `C(X^+,D)` and use that ideal inclusion reflects Cu order.
The compact-base theorem is the substantive result used here.

## 5. The target coefficient and removal from the first-factor image

Set `E=D tensor Z`. It is again simple, stably finite, and pure,
and has stable rank one. Its Cu semigroup is isomorphic to `Cu(D)`.
The algebraicity of `Cu(D)` therefore transfers to `Cu(E)`;
Coward--Elliott--Ivanescu, Corollary 5, gives real rank zero of `E`.
Thus the theorem applies to both the source and target section
algebras.

Let `S=Cu(C(X,D))`, `T=Cu(C(X,E))`, and `Phi=Cu(phi_X)`.
The previously proved full order reflection and compact V
surjectivity imply the following stronger range property:

**Corollary (removing a compact summand).** If `Phi(x)=k+y`,
where `k` is compact in `T`, then `y` lies in the range of `Phi`.

**Proof.** Lift `k` to a source projection class `[p]`. From
`Phi([p])<=Phi(x)`, order reflection gives `[p]<=x`. Represent
`x` by a positive element `a` in the stabilized source section
algebra. Projection comparison gives an actual projection
`r in Her(a)` equivalent to `p`. The compact projection on the
range module gives the actual orthogonal splitting

`H_a = r A direct_sum (1-r)H_a`.

The complementary module is countably generated, or equivalently
its hereditary compact-operator algebra is sigma-unital, so it
defines a source Cu class `z`. We obtain `x=[p]+z`. Applying
`Phi` gives

`k+Phi(z)=Phi(x)=k+y`.

Cancel the compact summand in the target using the theorem, in
both directions, to get `Phi(z)=y`. QED.

The extraction of the source summand uses actual projection
comparison inside `Her(a)`; it does not assume stable rank one or
identify arbitrary equal Cu classes with chosen isomorphic modules.

## 6. Exact equivalence with the universal two-frame Gram problem

The universal-angle artifact constructs, for any projection
`p in D tensor K`, any target positive contraction
`a in C(X,phi(p)Fphi(p))`, and any fixed `t>0` at most one,

`G_t=[[P,sqrt(P-t a)],[sqrt(P-t a),P]]`, `P=phi(p)`,

with the exact identity `[G_t]=[P]+[a]`. Its two diagonal entries
are identical actual source projections. The compact-removal
corollary now proves

`[G_t] is in range(Phi)` if and only if
`[a] is in range(Phi)`.                              (3)

The reverse implication is addition of the source projection
class; the forward implication is the new compact-removal result.
The source-projection compressions in the universal-angle artifact
exhaust every target positive class by an increasing sequence.
Consequently, under the already established order reflection,
surjectivity of the whole first-factor Cu map is equivalent to
realization of these two-by-two Gram matrices alone. The parameter
`t` may be chosen arbitrarily small and fixed in advance.

This removes the compact-cancellation caveat from the earlier
universal Gram reduction. It does not construct the arbitrary
Gram class, so mixed target realization remains unproved.

## Inputs and scope of review

- The exact strict relative positive-embedding theorem, including
  polar transport of nearby projection frames:
  `stw99-lxxvi-rr0-cutoff-relative-selection-audit-2026-09-05.md`.
- The closed cutoff-core method and the verified Cu-limit
  approximation/comparison conventions:
  `stw99-lxxvi-rr0-full-order-reflection-audit-2026-09-05.md`.
- The all-base V theorem:
  `stw99-lxxvi-all-base-compact-k-stability-audit-2026-09-05.md`.
- The explicit universal Gram identities and increasing source
  projection compressions:
  `stw99-lxxvi-universal-small-angle-obstruction-2026-09-05.md`.
- Rordam--Winter, Proposition 4.2:
  <https://arxiv.org/pdf/0801.2259>.
- Brown--Ciuperca, Theorem 3.5:
  <https://arxiv.org/abs/0811.0958>.
- Coward--Elliott--Ivanescu, Theorem 2 and Corollary 5:
  <https://arxiv.org/pdf/0705.0341>.

The projection cancellation, support-gap argument, arbitrary-positive
cancellation, and image-removal corollary are proved above. No
stable-rank-one theorem for a section algebra is being imported.
No older proof artifact was edited. The reviewed claim and route are
`stw99-lxxvi-rr0-compact-summand-cancellation` and
`stw99-lxxvi-rr0-compact-summand-cancellation-proof`; no commit was
performed by this reviewer.
