# Pure coefficients erase scalar unstable homotopy

## Result and correction of the S6 search route

Let `A` be unital, have stable rank one, and have almost divisible
`Cu(A)`. If `alpha in pi_k(U(r))` is zero under stabilization to the
infinite unitary group, then its image under scalar extension into
`pi_k(U(M_r(A)))` is already zero, for every `r>=1` and `k>=1`.

Every unital separable simple pure coefficient satisfies this conclusion.
Thus the scalar rank-two clutching witness over `S^6` previously left
open in this graph is impossible. The missing input was a published
divisibility-to-dimension-drop theorem; the required finite block map
is automatic, not an additional assumption to avoid in the search.

## From Cu almost divisibility to a finite block map

Fix `n>=2`. Almost divisibility applied to the compact class `[1_A]`
gives an element `x in Cu(A)` with

```text
n x <= [1_A] <= (n+1)x.                                  (1)
```

Rørdam--Winter formulate their criterion in the finite-matrix Cuntz
semigroup `W(A)`, so this distinction must be addressed. Every Cu class
is a supremum of an increasing sequence of finite-matrix classes
`x_j in W(A)` lying below it. Since `[1_A]` is compact and
`(n+1)x=sup_j (n+1)x_j`, some `j` satisfies

```text
n x_j <= n x <= [1_A] <= (n+1)x_j.                        (2)
```

The natural inclusion `W(A)->Cu(A)` reflects order, so (2) holds in
`W(A)`. Proposition 5.1 of Rørdam--Winter's arXiv:0801.2259v1 states,
for a unital stable-rank-one algebra, that these inequalities are
equivalent to existence of a unital *-homomorphism

```text
theta_n:Z_(n,n+1) -> A.                                  (3)
```

Here `Z_(n,n+1)` is the finite prime dimension-drop algebra, with
endpoint fibers `M_n` and `M_(n+1)`. We need a unital homomorphism,
not an embedding. Its possible kernel is irrelevant because the
scalar map into `A` still factors through it. Different `n` may use
unrelated maps. No compatibility, centrality, or map from their
inductive limit `Z` is inferred.

## The homotopy-pullback calculation in arbitrary degree

Fix `r>=1`, `k>=1`, and choose `n` so that

```text
k+1 < 2rn.                                               (4)
```

Set `P=U(M_r(Z_(n,n+1)))`. Concretely, this is the space of paths
in `G=U(rn(n+1))` whose endpoints lie in the images of
`G_0=U(rn)` and `G_1=U(r(n+1))`. The two maps into `G` are
the `(n+1)`-fold and `n`-fold tensor amplifications, up to a fixed
permutation conjugacy. Path evaluation is a fibration, so this is
the homotopy pullback and its long exact sequence contains

```text
pi_(k+1)(G_0) direct_sum pi_(k+1)(G_1)
  --d--> pi_(k+1)(G)
  --> pi_k(P)
  --e--> pi_k(G_0) direct_sum pi_k(G_1).                 (5)
```

By the unitary stable range, `pi_j(U(N))->pi_j(U)` is an
isomorphism for `j<2N`. Thus (4) identifies all three left groups
with the same stable group `H=pi_(k+1)(U)`. Under these canonical
identifications, tensor amplification by `m` is multiplication by
`m`, since it is the block sum of `m` copies. Therefore

```text
d(x,y)=(n+1)x-n y.                                      (6)
```

This is surjective: `d(z,z)=z` for every `z in H`. Consequently,
exactness of (5) makes `e` injective. This argument treats both
parities of `k`; one does not need to assume the obstruction group
`pi_(k+1)(G)` vanishes.

Let `alpha in pi_k(U(r))` be stably zero. The scalar-extension map
to `P` evaluates at the two endpoints as the `n`-fold and `(n+1)`-fold
amplifications of `alpha`. Both vanish: their target groups are in
the stable range and their stabilized values are multiples of zero.
Injectivity of `e` now forces the scalar image in `pi_k(P)` to be
zero. Apply `M_r(theta_n)` to prove the claimed vanishing in `A`.

For the original `S^6` witness one can simply take `r=2`, `k=5`,
and `n=2`, since `6<8`. The endpoint groups are `U(4),U(6)` and
the interior group is `U(12)`. The order-two element of `pi_5(U(2))`
is stably zero and therefore dies before tensoring with `Z`.

## Simple pure coefficients, including the infinite case

Lin's theorem says that a simple pure C*-algebra is either purely
infinite or has stable rank one. In the latter case, the argument
above applies directly. In the purely infinite simple case, known
K-stability of its nonzero unital projection corners identifies the
homotopy groups of `U(M_r(A))` with stable K-theory. The scalar
image of a stably zero class must then be zero by naturality.

Thus the conclusion applies to every unital separable simple pure
coefficient, as stated in the original scalar witness. In the
stably finite LXXVI counterexample corridor, only the stable-rank-one
branch is needed.

## Bundle consequence and the remaining mathematical issue

For `d>=2`, complex vector bundles of fixed rank `r` over `S^d`
are classified by clutching maps in `pi_(d-1)(U(r))`. Stable
equivalence means that the difference of the clutching classes is
in the kernel of stabilization. Hence stably equivalent rank-`r`
complex bundles become isomorphic `A`-module bundles after scalar
extension to the coefficients above. Their projection classes
cannot remain distinct until a later `Z` tensoring.

This does not prove K-stability of a general simple pure algebra.
The vanishing theorem applies to classes induced by scalar unitary
maps. A coefficient-dependent class

```text
gamma in ker(pi_k(U(p(A tensor K)p)) -> K_(k+1)(A))
```

need not factor through the scalar subgroup. The dimension-drop
map in (3) need not commute with the image of `gamma`, so tensoring
the null-homotopy construction with that image inside `A` is not
licensed. This is the precise distinction between the eliminated
scalar route and the remaining corner-unitary route.

## Prior art and sources

The implication from divisibility and stable rank one to a finite
dimension-drop map is a published theorem, not new here. The use
of it to remove the scalar witness corrects the prior search
boundary. The arbitrary-degree calculation is an explicit
application of the standard homotopy-pullback sequence and unitary
stable range.

- Rørdam--Winter,
  [The Jiang--Su algebra revisited](https://arxiv.org/abs/0801.2259),
  Proposition 5.1 in arXiv v1, for the exact finite-block criterion.
- Lin,
  [Strict comparison and stable rank one](https://arxiv.org/abs/2301.09250),
  for the simple-pure dichotomy.
- Seth--Vaidyanathan,
  [K-stability of continuous C(X)-algebras](https://arxiv.org/abs/1906.00033),
  Remark 1.5, recording K-stability of nonzero projection corners
  of purely infinite simple algebras.
- Jiang,
  [Nonstable K-theory for Z-stable C*-algebras](https://arxiv.org/abs/math/9707228),
  and Hua,
  [K-stability of Z-stable C*-algebras](https://arxiv.org/abs/2406.11084),
  Theorem 4.2, for the distinct target K-stability statement.
