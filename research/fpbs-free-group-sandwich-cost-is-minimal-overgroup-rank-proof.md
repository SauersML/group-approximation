---
rg: 2
id: fpbs-free-group-sandwich-cost-is-minimal-overgroup-rank-proof
kind: route
title: Squeeze the sandwich cost between the Fox rank bound and a subgroup treeing, and identify the Fox rank with the least overgroup rank through Jaikin-Zapirain's formula
target: fpbs-free-group-sandwich-cost-is-minimal-overgroup-rank
requires:
  - fpbs-sandwich-cost-fox-rank-lower-bound
  - free-group-minimal-overgroup-rank-is-fox-rank
  - jaikin-zapirain-minimal-overgroup-rank-formula
  - linnell-dimension-equals-skew-field-rank
  - lueck-dimension-additivity-cofinality-and-induction
  - gaboriau-treeable-free-action-realizes-min-cost
---

Notation as in the target. Fix a basis `f_1, …, f_q` of `F`, write
`S = {h_1, …, h_p}`, and let `A ∈ M_{p×q}(ZF)` be the Fox matrix
`A_{jk} = ∂h_j/∂f_k`. Put `r = π̄(H ≤ F)`. The minimum defining `r` is over
natural numbers and `H ≤ F` has finite rank, so `r` is attained by some
finitely generated `L`. If `S ⊆ {1}`, then `H = 1` and `r = 0`. The identity
relation is a sandwich, and it has cost 0. So assume `H ≠ 1`.

## 1. Upper bound: p^F_S(a) ≤ r

Let `H ≤ L ≤ F` with `rk L = r`, and let `l_1, …, l_r` be a basis of `L`.
The graphing `{x ↦ l_i x}` generates `E_{a|L}`. It is a treeing: a nontrivial
cycle would give a nontrivial reduced word `w` in the `l_i` with `w x = x` on
a non-null set, and `a` is free. By
`gaboriau-treeable-free-action-realizes-min-cost` (1), `C(E_{a|L}) = r`.
Since `E_{a|H} ⊆ E_{a|L} ⊆ E_a`, the relation `E_{a|L}` is a sandwich, so
`p^F_S(a) ≤ r`.

## 2. Lower bound: p^F_S(a) ≥ rk_{N(F)}(A)

This is `fpbs-sandwich-cost-fox-rank-lower-bound` (1), applied to
`h_1, …, h_p`. That part allows any finite family, not only a basis.

## 3. The module presented by A

Let `M_H = I_{Q[F]} / ^F I_{Q[H]}` as in
`jaikin-zapirain-minimal-overgroup-rank-formula`. Let
`ι : Q[F]^{1×q} → I_{Q[F]}` send `(c_k)` to `Σ_k c_k (f_k − 1)`. It is an
isomorphism of left `Q[F]`-modules, since `I_{Q[F]}` is free on the
`f_k − 1`. This is the same fact used in step 3 of §3 of
`fpbs-sandwich-cost-fox-rank-lower-bound-proof`.

**Claim.** `ι(Q[F]^{1×p} A) = ^F I_{Q[H]}`.

*Proof.* By the Fox fundamental formula (§1 of the Fox proof),
`ι(row_j A) = h_j − 1`. So the left side is `Σ_j Q[F](h_j − 1)`, which lies
in `^F I_{Q[H]}`.

For the converse, let `J = Σ_j Q[H](h_j − 1)`. For `g, h ∈ H`:
- `gh − 1 = g(h − 1) + (g − 1)`;
- `h^{-1} − 1 = −h^{-1}(h − 1)`.

Induction on word length in the `h_j^{±1}` then puts every `g − 1`, for
`g ∈ H`, into `J`. These elements span `I_{Q[H]}` over `Q`, so
`I_{Q[H]} = J`. Hence
`^F I_{Q[H]} = Q[F] I_{Q[H]} ⊆ Σ_j Q[F](h_j − 1)`. ∎

So `M_H ≅ Q_Q := Q[F]^{1×q} / Q[F]^{1×p} A`.

Now let `Q_C = C[F]^{1×q} / C[F]^{1×p} A`. Right exactness of `C ⊗_Q −` gives
`Q_C ≅ C[F] ⊗_{Q[F]} Q_Q ≅ C[F] ⊗_{Q[F]} M_H`.

## 4. Its dimension over the Linnell skew field

Let `D_Q` be the division closure of `Q[F]` in `U(F)`. This is the `D(F)` of
`jaikin-zapirain-minimal-overgroup-rank-formula`. Let `D_C` be the skew field
of `linnell-dimension-equals-skew-field-rank`. That node says `D_C` contains
`D_Q`. Then

```text
D_C ⊗_{C[F]} Q_C ≅ D_C ⊗_{Q[F]} M_H ≅ D_C ⊗_{D_Q} ( D_Q ⊗_{Q[F]} M_H ).
```

The Jaikin-Zapirain formula, with `rk F = q`, says the inner space has
`D_Q`-dimension `q − r`. The inner space is finite-dimensional, because
`M_H` is a quotient of `Q[F]^q`. Base change along the skew-field inclusion
`D_Q ⊆ D_C` sends `D_Q^{q−r}` to `D_C^{q−r}`. So

```text
dim_{D_C} ( D_C ⊗_{C[F]} Q_C ) = q − r.
```

By `linnell-dimension-equals-skew-field-rank`, with `N = N(F)`,

```text
dim_N ( N ⊗_{C[F]} Q_C ) = q − r.
```

## 5. rk_{N(F)}(A) = r

Let `θ : N^{1×p} → N^{1×q}`, `v ↦ vA`. Steps 1, 2 and 5 of §3 of
`fpbs-sandwich-cost-fox-rank-lower-bound-proof` do not use compressedness.
They give:
- `dim_N ker θ = p − rk A`;
- `coker θ = N ⊗_{C[F]} Q_C`, by right exactness;
- additivity (`lueck-dimension-additivity-cofinality-and-induction`) on
  `0 → ker θ → N^p → N^q → coker θ → 0`.

Additivity gives

```text
(p − rk A) − p + q − (q − r) = 0,   so   rk A = r.
```

**Conventions.** The identification of the Jaikin-Zapirain `D(F)` with a
skew field inside the `U(F)` containing `N(F)` is the one already made in
step 3 of §3 of the Fox proof. If the two sources embed `Q[F]` by left
versus right convolution, the anti-automorphism `g ↦ g^{-1}` exchanges them.
It carries `A` to the adjoint `A^*`, and `rk A^* = rk A` by §0 of the Fox
proof: `LP(A^*) = RP(A)`, which is equivalent to `LP(A)`. On the algebraic
side, the left span of the rows is exchanged with the right span of the
columns of `A^*`. Over a skew field these have the same dimension. So the
value `q − r` is convention-free.

## 6. Conclusion

§1, §2 and §5 give

```text
r ≥ p^F_S(a) ≥ rk_{N(F)}(A) = r.
```

So `p^F_S(a) = π̄(H ≤ F)`, attained by `E_{a|L}` for any `L ⊇ H` of rank
`r`. By `jaikin-zapirain-minimal-overgroup-rank-formula`, the `L²`-closure is
such an `L`. Nothing depended on the free action `a`. ∎

**Remarks.**
- **The easy half needs no L2 input.** The inequality `rk A ≤ r` follows from
  §1 and §2 alone: `rk A ≤ C(E_{a|L}) = rk L` for every `L ⊇ H`. The
  Jaikin-Zapirain theorem, through the existence of the `L²`-closure, is used
  only for `rk A ≥ r`.
- **This extends the compressed case.** For compressed `H` with basis `S`,
  `r = rk H = p`. This recovers part (2) of the Fox node.

## 7. Direct route through the imported Fox-rank identity

Alternatively, choose a free basis of `H` (the empty basis when `H = 1`).
By `free-group-minimal-overgroup-rank-is-fox-rank`, its Fox matrix has
rank `r = π̄(H ≤ F)`. The sandwich Fox-rank bound immediately gives
`C(E) ≥ r` for every intermediate relation. The subgroup treeing in §1
attains `r`; when `r = 0`, the diagonal relation attains cost 0.
This is the shorter route using the translated form of Jaikin-Zapirain's
Theorem 3.12. The calculation in §§3–5 gives the module translation for
an arbitrary finite generating family as well.

The value is independent of `a`, so in particular it equals the value
on the Bernoulli shift. For positive rank the free group is infinite and
the Bernoulli shift is free; for rank zero the group and every orbit
relation are trivial. Thus the relative Bernoulli sandwich bound holds
throughout the stated scope.
