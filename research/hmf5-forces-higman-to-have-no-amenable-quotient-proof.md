---
rg: 2
id: hmf5-forces-higman-to-have-no-amenable-quotient-proof
kind: route
title: Corona classes of a non-collapsing tuple are an exact MF representation, and amenable or locally-MF quotients lift back to non-collapsing tuples
target: hmf5-forces-higman-to-have-no-amenable-quotient
requires:
  - amenable-implies-operator-mf
  - nontrivial-higman-quotients-keep-all-four-bs-subgroups
  - nontrivial-higman-quotients-are-not-locally-elementary-amenable
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

Notation:
- `Hig` is the group with generators `g_0,...,g_3` and relations
  `g_i g_(i+1) g_i^(-1) = g_(i+1)^2` for `i in Z/4`.
- The relator defect of a tuple `U` in `U(k)^4` is
  `def(U) = max_i ||U_i U_(i+1) U_i^* - U_(i+1)^2||`.
- For a sequence of sizes `k_n >= 1`, the unitary corona is
  `C = prod_n U(k_n) / Null`, where `Null = {(u_n) : ||u_n - 1|| -> 0}`.
- "MF" means that the group embeds into some `C`. This is the repository's
  `IsOperatorMF`, where `C` is the group `NormMatrixCoronaUnitary`.

## Step 0. Every generator survives in every nontrivial quotient

Let `N` be a proper normal subgroup. Suppose `g_0 in N`. Then in `Hig/N` the
relation for `i = 0` reads `g_1 = g_1^2`, so `g_1 in N`. Repeating the
argument puts `g_2` and then `g_3` in `N`, so `N = Hig`, a contradiction. The
cyclic symmetry gives the same for every `g_i`. So every generator has
nontrivial image in every nontrivial quotient. (Infinite order is the stronger
[[nontrivial-higman-quotients-keep-all-four-bs-subgroups]], item 1, once
`g_i = x_i^(-1)` is used to match presentations. It is used only in Step 5.)

## Step 1. (a) implies (b)

Let `rho : Hig -> C` be a homomorphism. Choose unitary lifts `U_(i,n)` of
`rho(g_i)`. The class of `U_i U_(i+1) U_i^* U_(i+1)^(-2)` is `1`, so

```text
||U_(i,n) U_(i+1,n) U_(i,n)^* - U_(i+1,n)^2||
  = ||U_(i,n) U_(i+1,n) U_(i,n)^* U_(i+1,n)^(-2) - 1|| -> 0.
```

The equality holds because right multiplication by a unitary is an isometry.
So `def(U_n) -> 0`, and `(HMF5)` gives `max_i ||U_(i,n) - 1|| -> 0`. Hence
`rho(g_i) = 1` for every `i`, and `rho` is trivial.

## Step 2. (b) implies (a)

Suppose `(HMF5)` fails. Then there are `epsilon > 0` and tuples `U_n` in
`U(k_n)^4` with `def(U_n) <= 1/n` and `max_i ||U_(i,n) - 1|| >= epsilon`.
Pass to a subsequence along which a single index `i_0` attains the maximum.
The classes `[U_i]` in `C` satisfy the four relations exactly, by the display
in Step 1 read backwards. So they define a homomorphism `rho : Hig -> C`. It
has `rho(g_(i_0)) != 1`, because `||U_(i_0,n) - 1|| >= epsilon` for every `n`.
This contradicts (b).

## Step 3. (b) is equivalent to (c)

- **(b) implies (c).** Let `Q = Hig/N` be nontrivial and MF, with an injective
  `sigma : Q -> C`. Then `sigma` composed with the quotient map is a
  homomorphism `Hig -> C`. By Step 0, `g_0` does not lie in `N`, so this
  homomorphism sends `g_0` to something nontrivial. That contradicts (b).
- **(c) implies (b).** A nontrivial `rho : Hig -> C` has image
  `rho(Hig) <= C`. The inclusion is an injective homomorphism into `C`, so the
  image is MF. It is a nontrivial quotient of `Hig`, contradicting (c).

## Step 4. (c) is equivalent to (d), using finite presentation

MF groups are trivially locally embeddable into MF groups, so (d) implies (c).
For the converse, let `Q` be a nontrivial quotient that is locally embeddable
into MF groups, and write `q_i` for the images of the generators. Put

```text
F = {1} ∪ {q_i, q_(i+1)^2, q_i q_(i+1), q_(i+1)^2 q_i : i in Z/4}.
```

Take `phi : F -> G` injective, with `G` MF, such that
`phi(xy) = phi(x) phi(y)` whenever `x, y, xy` all lie in `F`.

- `1 * 1 = 1` gives `phi(1) = 1`.
- Put `h_i = phi(q_i)`. Then `phi(q_(i+1)^2) = h_(i+1)^2`.
- In `Q`, `q_i q_(i+1) = q_(i+1)^2 q_i`. Applying `phi` to both sides gives
  `h_i h_(i+1) = h_(i+1)^2 h_i`.

So `g_i -> h_i` is a homomorphism `Hig -> G`. It sends `g_0` to
`h_0 = phi(q_0)`, which is not `phi(1) = 1` by injectivity and Step 0. Compose
with a faithful `G -> C`. The result is a nontrivial homomorphism `Hig -> C`,
which contradicts (b) and hence (c).

## Step 5. Item 2 (the collapse implies NAQ)

Let `Q` be a nontrivial quotient of `Hig`. Each case below yields a nontrivial
homomorphism `Hig -> C`, which contradicts (b).

- **`Q` amenable.** `Q` is countable, so it is MF by
  [[amenable-implies-operator-mf]]. This contradicts (c).
- **`Q` residually amenable.** Some amenable quotient of `Q` keeps `q_0`
  nontrivial. It is a nontrivial amenable quotient of `Hig`, and the previous
  case applies.
- **`Q` locally embeddable into amenable groups.** Amenable groups are MF, so
  `Q` is locally embeddable into MF groups. This contradicts (d).
- **`Q <= U(A)` with `A` an MF C*-algebra.** Here `A` embeds in
  `prod M_(k_n) / (+) M_(k_n)`, possibly non-unitally with `1_A -> p`. Then
  `u -> iota(u) + (1 - p)` is an injective homomorphism from `U(A)` into the
  unitary group of the C*-corona. By `normMatrixCoronaUnitaryEquiv`, that
  unitary group is the group `C`. So `Q` is MF, contradicting (c).

## Step 6. Item 3 (NAQ concerns simple groups)

Let `Q` be a nontrivial amenable quotient. `Q` is finitely generated, so Zorn's
lemma gives a maximal proper normal subgroup `M`. The union of a chain of
proper normal subgroups is proper, because otherwise a single member would
contain all four generators. Then:

- `S = Q/M` is simple, nontrivial and amenable.
- `S` is infinite, because `Hig` has no nontrivial finite quotient.
  (Finite groups lie in class `D` of
  [[nontrivial-higman-quotients-are-not-locally-elementary-amenable]].)
- The converse is trivial.

The remaining properties of `S` are items 1–2 of
[[nontrivial-higman-quotients-keep-all-four-bs-subgroups]] and item 2 of
[[nontrivial-higman-quotients-are-not-locally-elementary-amenable]], applied to
the proper normal subgroup `ker(Hig -> S)`.

## Step 7. Items 4 and 5

- **Item 4** is the contrapositive of Step 5, made explicit by the lifts in
  Step 3.
- **Item 5.** Steps 1–3 never use the relations beyond Step 0. For a general
  group `G`, the statement "`Rad_MF(G) = G` if and only if no nontrivial
  quotient is MF" is Step 3 with Step 0 dropped. This works because a
  nontrivial quotient `G/N` embedded in `C` gives a homomorphism whose kernel
  is `N`, which is not all of `G`.
- **Item 5, amenable case.** Combine item 5 with
  [[amenable-implies-operator-mf]].
