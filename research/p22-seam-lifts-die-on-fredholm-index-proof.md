---
rg: 2
id: p22-seam-lifts-die-on-fredholm-index-proof
kind: route
title: Read the head as the cokernel of the S-root on the range of x_13(1) and compare Fredholm indices at the two ends of a seam
target: p22-seam-lifts-die-on-fredholm-index
requires: []
---

Notation as in the target. All operators are linear maps between vector
spaces. "Fredholm" means finite-dimensional kernel and cokernel, and
`ind = dim ker - dim coker`. No topology is used.

## Step 1. Root calculus

**Additivity.** For `i != j`, `(1 + A e_ij)(1 + B e_ij) = 1 + (A + B) e_ij`.
So multiplicativity of `pi` on `x_ij(a) x_ij(b) = x_ij(a + b)` gives
`phi_ij(a + b) = phi_ij(a) + phi_ij(b)` for coefficients in `B_0`.

**Commutators.** For distinct `i, j, k`,

```text
[1 + A e_ij, 1 + B e_jk] = 1 + A B e_ik        ([g,h] = g h g^(-1) h^(-1)).
```

So each relation `[x_ij(a), x_jk(b)] = x_ik(ab)` in `B_0` gives
`phi_ik(ab) = phi_ij(a) phi_jk(b)`. All four triples used below have their
three roots in `P_{2,2}`.

```text
(1,2,3):  phi_13(ab) = phi_12(a) phi_23(b)
(2,1,3):  phi_23(b)  = phi_21(1) phi_13(b)
(1,3,4):  phi_14(b)  = phi_13(b) phi_34(1)
(1,4,3):  phi_13(ba) = phi_14(b) phi_43(a)
```

**Left and right S-roots.** Put `R(a) = phi_34(1) phi_43(a) : V_3 -> V_3`.
Composing the first two lines, and then the last two, gives for `a, b` in
the coefficient set:

```text
phi_13(a b) = L(a) phi_13(b),        phi_13(b a) = phi_13(b) R(a).              (1)
```

With `b = 1`:

```text
phi_13(a) = L(a) m = m R(a)          for a in {1, s, t}.                        (2)
```

Applying (1) twice, with `ts = 1` in `R`:

```text
m = phi_13(t s) = L(t) phi_13(s) = L(t) L(s) m,                                  (3)
phi_13(s t)     = L(s) phi_13(t) = L(s) L(t) m.                                  (4)
```

**The head.** By additivity, `phi_13(q) = phi_13(1) - phi_13(st)`, so by (4)

```text
phi_13(q) = m - L(s) L(t) m.                                                    (5)
```

Every relation used lies in `B_0`: commutators have length 4, coefficient
products lie in `{±1, ±s, ±t, ±st}`, and `x_13(1) x_13(-st) = x_13(q)` has
length 2.

## Step 2. Part 1: the head is a cokernel

**Stability.** Let `a in {s, t}`. By (2), `L(a) m = m R(a)`, so
`L(a) Y = range(m R(a)) ⊂ range(m) = Y`. This uses the right Levi roots
`x_34(1)` and `x_43(a)`.

**Left inverse.** For `y = m v in Y`, (3) gives `L(t) L(s) y = m v = y`. So
`L(t) L(s)|_Y = id_Y`. In particular `L(s)|_Y : Y -> Y` is injective, and
`L(t)|_Y` is surjective.

**Equivalence.** Since `pi` is root-preserving, `pi(x_13(q)) = 1` exactly
when `phi_13(q) = 0`. By (5), that holds exactly when `L(s) L(t) = id` on `Y`.
- If `L(s) Y = Y`, then `L(s)|_Y` is bijective, so its left inverse
  `L(t)|_Y` is its inverse and `L(s) L(t)|_Y = id`.
- Conversely, `L(s) L(t)|_Y = id` makes `L(s)|_Y` surjective.

So `pi(x_13(q)) != 1` if and only if `Y / L(s) Y != 0`.

In fact the head is this cokernel. For `y = m v`, write
`phi_13(q) v = y - L(s) L(t) y`. The map `y -> y - L(s) L(t) y` is the
projection of `Y` onto a complement of `L(s) Y`: it kills `L(s) Y`, because
`L(s)L(t)L(s) = L(s)` on `Y`, and it is idempotent. So
`range(phi_13(q)) ≅ Y / L(s) Y`.

## Step 3. Part 2: the index bound

**Two standard facts.** Both are purely algebraic.

- **(F1) Additivity.** Let `X ⊂ V` be a subspace with `A X ⊂ X`, and let `A`
  induce `A_X` on `X` and `A'` on `V/X`. If two of `A_X, A, A'` are Fredholm,
  so is the third, and `ind A = ind A_X + ind A'`. This is the snake lemma
  applied to `0 -> X -> V -> V/X -> 0`: the six-term exact sequence of kernels
  and cokernels has alternating dimension sum 0.
- **(F2) Finite rank.** If `A` is Fredholm and `f` has finite rank, then
  `A + f` is Fredholm with the same index. Both maps agree on
  `U = ker f`, which has finite codimension, and restricting to `U` changes
  the index by `-codim U` for each, by composing with the inclusion
  `U -> V`, whose index is `-codim U`.

**Proof of part 2.** Take `X = Y` in (F1).
- `V_1 / Y` is finite-dimensional, so the induced map `A'` has index 0.
- Hence `L(s)|_Y` is Fredholm and `ind L(s) = ind L(s)|_Y`.
- By Step 2, `L(s)|_Y` is injective, so
  `ind L(s)|_Y = -dim Y / L(s) Y <= 0`.
- If the head survives, `dim Y / L(s) Y >= 1`, so the index is `<= -1`.

## Step 4. Part 3: finite dimensions

If `Y` is finite-dimensional, the injective map `L(s)|_Y : Y -> Y` is
surjective. So the head dies by Step 2. Nothing about `V_1` or the other
blocks is needed.

## Step 5. Part 4: sink ends

Let `V_1 = V_3 = K^((k <= M))`, with `m - 1` of finite rank, and suppose `L(s)`
agrees with the shift `D : e_k -> e_(k+1)` (read `e_(M+1) = 0`) on all basis
vectors except finitely many.

- `m = 1 + (m - 1)` is Fredholm of index 0 by (F2). So its cokernel
  `V_1 / Y` is finite-dimensional.
- `D` is surjective, and `ker D = K e_M`, so `ind D = +1`.
- `L(s) - D` vanishes on all but finitely many basis vectors, so it has
  finite rank, and by (F2) `ind L(s) = +1`.

This contradicts part 2, which needs `ind L(s) <= 0`. So no root-preserving
partial model with such a `V_1` exists. The obstruction does not use `q`,
and so it holds whether or not the head survives.

The same argument rules out every far end where `L(s)` is Fredholm of
positive index and `m` is Fredholm. Only far ends of index `<= 0` survive,
and at index 0 the head dies there. The head can survive only at an end
where `L(s)` has negative index.

## Step 6. Seam consequence

Suppose a construction glues, as in `binary-jacobson-el2-is-lef`, a near
end (the faithful action on `V_+ = F^((N))`) to a far end
`x_ij(a) -> 1 + (lambda_ij a)_- e_ij` on the half-line
`V_-^M = F^((k <= M))` of some ring `J'`.
- **What the gluing needs.** Middle agreement requires the far symbols to
  match, `sigma' o lambda_ij = sigma`. Multiplicativity on the ball requires
  the far end to be a partial model.
- **Why part 4 applies.** Assume each far operator `(lambda_ij a)_-` has
  band width `r` and equals the Laurent operator of its symbol on all
  columns `k <= M - c`. This is (N2) of `binary-jacobson-el2-lef-proof` for
  `J' = F<S',T' | S'T' = 1>`, and it is the shape middle agreement needs for
  any `J'`.
  - `m = (lambda_13 1)_-` differs from `1` in finitely many columns.
  - `L(S) = (lambda_12 S)_- (lambda_21 1)_-` equals the Laurent operator of
    `z * 1 = z`, which is `D`, on all columns `k <= M - c - r`. So it differs
    from `D` in finitely many columns.
- **Conclusion.** Part 4 applies, so no such far end exists, for any `J'`
  and any family `lambda_ij`, and not only for ring-hom-induced ones.

**Near end check.** At the near end, `m = 1` and `L(S) = S_+`, so `Y = V_+`
and `Y / S V_+ = F e_0`. Part 1 gives that the head survives, and part 2 gives
`ind = -1`, which is consistent.

**Why EL_2 and the one-sided parabolic escape.**
- **EL_2(J).** It has no root `x_13`, so no `m` and no `Y` exist.
- **One-sided parabolic `J^2 x| EL_2(J)`.** There is no root `x_43`, so (2)
  loses `m R(a)` and `Y` need not be `L(S)`-stable. The mirror end, with
  index `+1`, is then harmless.

**What survives.** The theorem constrains only root-preserving block models.
- **Unconstrained models:**
  - models where `pi(x_13(a))` is not supported in the block `(1,3)`, for
    instance a far end that mixes the four blocks by a non-block-diagonal
    change of basis away from the seam;
  - models that are not linear on the unipotent radical.
- **Consistent seams:** a seam whose far end has `L(S)` of index `<= -1`,
  that is a second source end. This forces a total index `<= -2` on an
  infinite space and so cannot close up into a finite-dimensional model by
  itself.
