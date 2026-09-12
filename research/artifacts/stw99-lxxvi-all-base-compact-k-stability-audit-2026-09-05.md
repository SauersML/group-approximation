# The exact projection-corner obstruction beyond dimension one

## Statement and scope

Let `D` be separable, simple, stably finite, and pure, and put
`E=D tensor Z`. We prove the equivalence stated in
`stw99-lxxvi-all-base-compact-rigidity-k-stability` and its real-rank-zero
corollary. The maps throughout are the actual first-factor maps.

The ingredients already available in the LXXVI lane are:

- `D` and `E` have stable rank one, and the coefficient first-factor map
  induces an isomorphism on Cu, hence on V;
- first-factor inclusion induces an isomorphism on K-theory;
- nonzero projection corners of `D tensor K` are unital simple pure
  stably finite algebras, and the corresponding target corners are
  Z-stable;
- Z-stable algebras are K-stable (Jiang; Hua's new proof).

No stable-rank-one assertion about `C(X,D)` is used. Cu equivalence of
projections is Murray--von Neumann equivalence without such an assertion.

## 1. The specified map on a projection corner

For a nonzero projection `p in D tensor K`, write

```text
B = p(D tensor K)p,
B_Z = (p tensor 1)((D tensor K) tensor Z)(p tensor 1) = B tensor Z.
```

The corner first-factor map fits into the commuting diagram

```text
pi_k U(B)       ---> pi_k U(B_Z)
   |                      |
   v                      v
K_(k+1)(B)     ---> K_(k+1)(B_Z).
```

The bottom and right arrows are isomorphisms. Thus the top arrow is an
isomorphism exactly when the left stabilization arrow is an isomorphism;
the same holds separately for injectivity and surjectivity. This is a
map-level conclusion, not an abstract identification of the groups.

## 2. Projection bundles of a fixed fiber

Over a connected finite CW complex, a continuous projection section
`q in C(X,D tensor K)` has locally constant Murray--von Neumann fiber
class: projections at norm distance less than one are unitarily
equivalent in the unitization. Hence its fiber class is a single
`[p] in V(D)`.

The ranges of `q(x)` form a locally trivial Hilbert D-module bundle with
fiber `p(H_D)`. Its structure group is exactly `U(B)` in the norm
topology. Conversely, every principal `U(B)` bundle over compact `X`
produces such a module bundle and a projection in `C(X,D tensor K)`.
For completeness, take a finite trivializing cover and a subordinate
partition of unity. The usual map whose coordinates are the square roots
of the partition functions times the local trivializations embeds the
bundle isometrically into a finite direct sum of `p(H_D)`. Its range
projection is continuous. It is therefore a projection in the stabilized
section algebra.

An isomorphism of these module bundles is precisely a continuous partial
isometry between the range projections. Thus classification here is by
actual bundle isomorphism, not merely stable isomorphism or K0. Principal
bundle classification identifies these classes with `[X,BU(B)]`.
Extension of scalars acts through the specified map
`BU(B) -> BU(B_Z)`.

## 3. Spheres detect both kernels and cokernels

For `k>=0`, glue trivial `p(H_D)` bundles on the two hemispheres of
`S^(k+1)` using a clutching map into `U(B)` on the equator. For `k>=1`,
the unbased bundle classes are the orbits of `pi_k U(B)` under the
conjugation action of `pi_0 U(B)`. For `k=0`, bundles on `S^1` are the
conjugacy classes in `pi_0 U(B)`; equivalently one normalizes one of the
two equatorial transition values to the identity.

In every degree the orbit of zero is just zero. Therefore a nonzero
element of the kernel of

```text
pi_k U(B) -> pi_k U(B_Z)
```

gives a nontrivial projection bundle which becomes the trivial `p` bundle
after tensoring with Z. The two source projections are not equivalent,
whereas their images are equivalent. In particular injectivity of the
first-factor V map for this sphere forces injectivity on `pi_k U(B)`.

For surjectivity, start with any target clutching element
`beta in pi_k U(B_Z)` and its associated projection bundle. If the
first-factor V map of this sphere is surjective, choose a source
projection bundle lifting it. At one basepoint its fiber has class
mapping to `[p tensor 1]`. Coefficient V injectivity identifies that
source fiber with `p`; connectedness then does so at every point. The
source bundle consequently has some clutching class `alpha` in the
appropriate orbit space.

The component-conjugation action in the target is trivial. Indeed, its
stabilization map is an isomorphism, and conjugation by a fixed unitary
acts trivially on stable unitary homotopy groups. One can see the latter
directly after adding a block: `diag(v,v*)` is path connected to the
identity, so conjugation by `diag(v,1)` has the same action as an inner
conjugation homotopic to the identity on a stabilized family in the first
block. Hence the image of `alpha` is `beta` itself, not just an
uncontrolled target conjugacy class. This proves surjectivity on
`pi_k U(B)`.

Thus sphere V isomorphisms in every dimension force every corner
stabilization map to be an isomorphism. Conversely, any failure of a
corner stabilization map produces a failure of the corresponding sphere
V map, by the same two arguments.

## 4. Corner homotopy rigidity gives every compact base

Assume all the corner stabilization maps are isomorphisms. Section 1
says `U(B) -> U(B_Z)` is a weak homotopy equivalence, including the map
on components. Its classifying-space map is therefore a weak homotopy
equivalence and induces bijections on homotopy classes of maps out of
finite CW complexes. This is the standard principal-bundle obstruction
argument, applied successively over the cells; equivalently use CW
approximations of the classifying spaces.

Section 2 now proves bijectivity of V on every fixed fiber class. The
coefficient V isomorphism matches the fiber classes themselves, so the
whole V map is bijective for every finite CW base (componentwise if
disconnected). It is additive. A bijective monoid homomorphism has an
additive inverse, so it preserves and reflects algebraic order. For
projections that order is the Cu order: `p<=q` is equivalent to
`q ~ p direct-sum r` for another projection `r`.

Every compact metrizable space is an inverse limit of finite polyhedra.
The resulting section algebra is the corresponding C*-inductive limit
after tensoring with D, and similarly with E. V is continuous for
C*-inductive limits: a projection is equivalent to one from a finite
stage, and an equivalence between finite-stage projections occurs at a
later stage, by projection and partial-isometry perturbation. Naturality
of first-factor inclusion therefore passes these V isomorphisms to every
compact metrizable base. No finite-dimensional-base hypothesis is needed.

The implication from all compact metrizable bases to spheres is immediate.
This completes the three-way equivalence.

## 5. A positive class in every base dimension

Suppose in addition that `D` has real rank zero. Every nonzero projection
corner `B` above is simple, non-elementary, real rank zero, and stable
rank one. Non-elementarity follows also from purity: a nonzero elementary
corner would make the simple algebra Morita equivalent to the scalars,
whose Cu semigroup is not almost divisible. Zhang's 1991 Theorem II
(Section 2; summarized explicitly on page 285) makes
these corners K-stable. Section 4 therefore gives the actual V
isomorphism over every compact metrizable X.

Since `C(X,D)` is stably finite, its compact Cu classes are precisely
projection classes, by Brown--Ciuperca. The same holds for E. Hence this
is the entire compact wing, with its order, in arbitrary base dimension.
It does not reflect an inequality with noncompact right-hand side merely
from V, and it does not classify the noncompact wing.

## 6. The relation between the two named problems

Assume STW LXXVI has an affirmative answer. If B is unital separable
simple stably finite pure, Seth--Vilalta's Theorem A says
`C(S^d,M_m(B))` is pure for all d and m. Its Cu first-factor map would
therefore be an isomorphism. Restricting to compact elements gives the
sphere V isomorphisms used above; compact elements lift under a Cu
isomorphism, and stable finiteness makes those lifts projection classes.
Section 3 forces all stabilization maps on every `U(M_m(B))` to be
isomorphisms. Thus B is K-stable. The simple purely infinite case is
already K-stable by the published purely infinite theorem.

Consequently LXXVI entails the stronger K-stability assertion of LVIII
on the unital separable simple class. A counterexample to that assertion
in the finite simple class would automatically yield a pure sphere-field
counterexample to LXXVI. This is stronger than asking for a scalar
unstable class: the earlier scalar-no-go theorem shows that any surviving
kernel must depend on the coefficient algebra.

This implication is not a proof of either open problem. In particular,
the prime dimension-drop maps obtained from almost divisibility do not
commute with arbitrary coefficient-dependent unitary families, so the
scalar nullhomotopy argument cannot prove the required corner maps.

## Primary sources and prior-art boundary

- S. Zhang, *Matricial structure and homotopy type of simple C*-algebras
  with real rank zero*, J. Operator Theory 26 (1991), 283--312:
  https://jot.theta.ro/jot/archive/1991-026-002/1991-026-002-004.pdf .
  Theorem II, Section 2, with its statement summarized on page 285.
  The simple real-rank-zero stable-rank-one K-stability input is published
  prior art, not a new K-stability theorem here.
- X. Jiang, *Non-stable K-theory for Z-stable C*-algebras*:
  https://arxiv.org/abs/math/9707228 ; S. Hua, *K-stability of Z-stable
  C*-algebras*, Theorem 4.2: https://arxiv.org/pdf/2406.11084 .
- A. Seth and E. Vilalta, *Continuous functions over a pure C*-algebra*,
  Theorem A: https://arxiv.org/pdf/2602.14809 . The introduction explicitly
  announces forthcoming work by Evington, Hua, Schafhauser, Seth, and
  White on K-stability for pure coefficients. That announcement is not
  treated as an available theorem.
- C. Schafhauser, A. Tikuisis, S. White, *Nuclear C*-algebras: 99
  problems*, Problems LVIII and LXXVI:
  https://mysite.science.uottawa.ca/atikuisis/STW.pdf .

The contribution here is the exact map-level reduction of the complete
compact wing to projection-corner K-stability, the all-base corollary,
and the explicit implication between the named problems. Principal
bundle classification, sphere clutching, and Zhang's computation are
classical inputs. The general noncompact higher-dimensional Cu problem
remains outside this theorem.
