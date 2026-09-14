---
rg: 2
id: ce-stabilizer-criterion-proof
kind: route
title: Tensor the representation with the regular one to make it canonical, and use the stable letter for the converse
target: ce-stabilizer-criterion-needs-no-trace
requires: [commutation-stabilizers-are-relatively-embeddable, binary-free-and-ordinary-coset-wreaths-share-hyperlinearity]
---

**`2 => 1`.** Put `P = L(G) tensor-bar M`. It is Connes embeddable because
`L(G)` is (hyperlinearity of `G`) and `M` is, and tensor products of
Connes-embeddable finite algebras are Connes embeddable. Define
`u_g = lambda_g tensor sigma(g)`, a unitary representation of `G` in `P`. For
the product trace,

```text
tau_P(u_g) = tau(lambda_g) tau(sigma(g)) = delta_(g,e),
```

so `lambda_g -> u_g` extends to a trace-preserving normal embedding
`L(G) -> P`: a canonical copy of `L(G)`, whatever `tau o sigma` was.

For each `i` take the spectral projections of `Re x_i` and `Im x_i` on the
intervals with rational endpoints. This is a countable family `(q_j)` of
projections in `M`. A unitary commutes with a normal element if and only if it
commutes with all of its spectral projections, and it commutes with `x_i` if and
only if it commutes with `Re x_i` and `Im x_i`. So

```text
{g : [u_g, 1 tensor q_j] = 0 for all j} = {g : [sigma(g), x_i] = 0 for all i} = Lambda
```

by `(CST1)`. The countable-family clause of
`commutation-stabilizers-are-relatively-embeddable` makes `L(Lambda) <= L(G)`
relatively embeddable over the scalars.

**`1 => 2`.** By `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`
(item 6 implies item 5), the centralizer HNN group
`H = G *_Lambda (Lambda x <v>)` is hyperlinear, so `M = L(H)` is Connes
embeddable. Let `sigma` be the inclusion `G <= H` followed by
`g -> lambda_g`, and put `x = lambda_v`. For `g in G`, `[lambda_g, lambda_v] = 0`
if and only if `g v g^(-1) v^(-1) = 1` in `H`. If `g in Lambda` this holds by the
defining relation. If `g notin Lambda`, the only candidate pinch in
`g v g^(-1) v^(-1)` is `v g^(-1) v^(-1)`, which needs `g^(-1) in Lambda`. So the
word is reduced and contains stable letters, and by Britton's lemma it is not
trivial. Hence the stabilizer is exactly `Lambda`.

**Transport of walls.** If `sigma : G -> U(M)` has a relative wall, i.e.
`y in M` commuting with `sigma(t Lambda t^(-1))` but not with `sigma(Lambda)`,
then `1 tensor y` is a wall for the canonical model `u` in `P`, since
`[u_g, 1 tensor y] = lambda_g tensor [sigma(g), y]`. So normalization questions
such as `kt-centralizer-normalization-hs` can be tested on non-canonical models.
