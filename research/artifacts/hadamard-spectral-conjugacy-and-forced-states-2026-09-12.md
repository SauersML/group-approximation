# The Hadamard spectral half is the swap idempotent, and states are forced on the signed Thompson group

Lane `w4-hadamard-f3`, 2026-09-12. Supports:
- `hadamard-spectral-half-is-constant-conjugate-to-swap-idempotent` (Section 1), with route
  `hadamard-spectral-half-constant-conjugacy-proof`;
- the route `f9-hadamard-fullness-from-swap-corner-fullness` into `f9-hadamard-spectral-idempotent-is-full`
  (Corollary 1.4);
- `anti-central-k0-states-equal-lifted-trace-on-signed-thompson` (Section 2), with route
  `anti-central-k0-states-lifted-trace-proof`.

Directive: decide `f9-hadamard-spectral-idempotent-is-full` (w3-corner-cohn-b, e5b4731bcd), either by a
design `c f_+ b = 1_-` or by a state that sees `h`. Outcome: the target is the swap corner itself,
conjugated by a constant `F_9` unit (Section 1). The state side is rigid on every finite subgroup of the
signed Thompson group, and the only place a state can see `h` is one block split (Section 2).

## 0. Notation

- `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `S_- = eps_- F_3[G]` with `eps_- = 2(1 - [z])` and unit `1_- = eps_-`,
  `S_-^(9) = F_9 (x) S_-`, `i^2 = -1` in `F_9`. In characteristic three `2 = -1` and `4 = 1`.
- `M : R -> M_2(R)`, `x -> (t_i x s_j)`, is an algebra isomorphism. A matrix `a` in `GL_2(F_3)` names the
  constant unit `sum_ij s_i a_ij t_j` of `G`, and `a -> sum s_i a_ij t_j` is an injective homomorphism.
- `w = [[0,1],[1,0]]`, `d = [[1,0],[0,-1]]`, `h = [[1,1],[1,-1]]`, `u = [[1,0],[1,-1]]`.
- `e_- = 2 eps_- (1 + [w])` (the swap idempotent) and `f_+ = 2(1_- + i[h])`, `f_- = 1_- - f_+`
  (`f9-hadamard-spectral-idempotents-are-half-idempotents`).
- `Q = span_(F_3){1_-, [w], [d], [wd]}`, a unital copy of `M_2(F_3)` (Lemma 1.2 of
  `ternary-anti-central-cohn-reformulation-2026-09-12.md`). Evaluation `pi` is injective on `Q`.
- `H = E x| V`, the signed Thompson group, with `F_3[H] eps_- = C(M_-, F_3) x| V`
  (`signed-thompson-algebra-is-odd-measure-crossed-product`), `lambda` the Haar measure on `M_-`.

## 1. The spectral half is a constant conjugate of the swap idempotent

**Lemma 1.1.** Put `c = [[-1,0],[1,1]] = -s0 t0 + s1 t0 + s1 t1`, a constant unit of `G`. Then

```text
c^2 = 1,     c d c = u,     c (wd) c = h,     c w c = hu = [[-1,-1],[0,1]].
```

*Proof.* Matrix arithmetic over `F_3`.
- `c^2 = [[1,0],[-1+1,1]] = I`.
- `c d = [[-1,0],[1,-1]]`, and `(c d) c = [[1,0],[-2,-1]] = [[1,0],[1,-1]] = u`.
- `wd = [[0,-1],[1,0]]`, `c (wd) = [[0,1],[1,-1]]`, and `(c wd) c = [[1,1],[-2,-1]] = [[1,1],[1,-1]] = h`.
- `c w c = c (wd) d c = (c wd c)(c d c) = h u`, and `h u = [[2,-1],[0,1]] = [[-1,-1],[0,1]]`. QED

**Lemma 1.2.** `Q' = [c] Q [c]^(-1) = span_(F_3){1_-, [h], [u], [hu]}` is a unital subalgebra of `S_-`
isomorphic to `M_2(F_3)`, evaluation is injective on it, and `Q'_9 = F_9 (x) Q'` is a unital copy of `M_2(F_9)`
inside `S_-^(9)`. It contains `f_+`, `f_-` and `E'_11 = [c] e_- [c]^(-1) = 2 eps_- (1 + [hu])`.

*Proof.* Conjugation by the group element `[c]` is an algebra automorphism of `S_-` fixing `1_-`, and it carries
`[w], [d], [wd]` to `[hu], [u], [h]` by Lemma 1.1. `pi([c] x [c]^(-1)) = c pi(x) c^(-1)`, so injectivity of `pi` on
`Q` passes to `Q'`, and `pi(Q') = M_2(F_3)` by dimension. Tensor with `F_9`. QED

**Theorem 1.3.** Put `p = f_+`, `q = E'_11`, and

```text
v  = p q + (1_- - p)(1_- - q),        v' = q p + (1_- - q)(1_- - p).
```

Then `v` is a unit of `Q'_9` with `v^(-1) = -v'`, and

```text
f_+ = W e_- W^(-1),      W = v [c].
```

*Proof.*
- *Intertwining.* For idempotents in any ring, `v q = p q = p v`, and
  `v v' = v' v = 1 - (p - q)^2`, and `(p - q)^2` commutes with `p` and `q`. (Expand:
  `(1-p)(1-q)(1-p) = 1 - p - q + pq + qp - pqp`, add `pqp`, and compare with `(p-q)^2 = p + q - pq - qp`.)
- *The matrices.* Under `pi`, `q = 2(I + hu) = 2 [[0,-1],[0,2]] = [[0,1],[0,1]]` and
  `p = 2(I + i h) = [[-1-i, -i],[-i, -1+i]]`. Both are idempotents of rank one; `p^2 = p` because
  `(-1-i)^2 + (-i)^2 = 2i - 1 = -1 - i` and `(-1-i)(-i) + (-i)(-1+i) = 2i = -i`.
- *The square.* `p - q = [[-1-i, -1-i],[-i, 1+i]]` and `(p - q)^2 = -I`: the diagonal entries are
  `(-1-i)^2 + (-1-i)(-i) = 2i + (i - 1) = -1` and `(-i)(-1-i) + (1+i)^2 = (i - 1) + 2i = -1`, and the
  off-diagonal entries are `2i - 2i = 0` and `(i - 1) + (-i + 1) = 0`.
- *Transfer.* `pi` is injective on `Q'_9` (Lemma 1.2), so `(p - q)^2 = -1_-` in `Q'_9`, and
  `v v' = v' v = 2 . 1_- = -1_-`. Hence `v^(-1) = -v'`, and `v q v^(-1) = p v v^(-1) = p`.
- *Conclusion.* `f_+ = v [c] e_- [c]^(-1) v^(-1)`. QED

**Corollary 1.4.** For `b, c'` in `S_-^(9)`, `c' f_+ b = 1_-` iff `(c' W) e_- (W^(-1) b) = 1_-`. Hence
`f9-hadamard-spectral-idempotent-is-full` holds iff `ternary-anti-invariant-swap-corner-is-full` holds.

*Proof.*
- *If.* A solution `c e_- b = 1_-` in `S_-` lies in `S_-^(9)`, and `(c W^(-1)) f_+ (W b) = c e_- b = 1_-`.
  This is route `f9-hadamard-fullness-from-swap-corner-fullness`.
- *Only if.* This direction is already on main as a chain: `hadamard-spectral-fullness-gives-f9-cohn-family`,
  `f9-cohn-family-descends-to-anti-central-summand`, `anti-central-cohn-family-gives-swap-corner-fullness`.
  Corollary 1.4 gives a one-step version over `F_9`: conjugate by `W`, then descend with Theorem 1.1 of
  `f9-hadamard-spectral-cohn-attempt-2026-09-12.md` and Theorem 2.1 of the Cohn reformulation. QED

**Remark 1.5 (supports).** `v` and `v'` are `F_9`-combinations of `eps_- [g]` with `g` in the dihedral group
`<h, u>` of order eight, so `supp W` lies in `<h, u> c`. A design for `f_+` with supports `S_b`, `S_c` is a
design for `e_-` with supports `c^(-1) <h,u> S_b` and `S_c <h,u> c`, and conversely.

**Remark 1.6 (what this does to the F_9 line).**
- Section 3.4 of the F_9 artifact kept one surviving idea: `h` in the support escapes the signed Thompson
  crossed product. The swap corner already has that escape: `q_[0] = [h] e_- [h]^(-1)` lies in
  `C(M_-, F_3) x| V` (`hadamard-unit-conjugates-swap-idempotent-to-cylinder`), and every swap design is a
  `q_[0]` design with supports translated by `h`. So the F_9 Hadamard target is not a separate problem, and no
  room is gained or lost by passing to it.
- The filters coincide. Part 5 of the half-idempotent claim (a rank model moving `z` on a subgroup containing
  `h`, `u` and the supports) is the swap corner's filter `anti-central-rank-models-kill-ternary-corner-witnesses`
  transported by `[c]`, with `(h, u) = [c](wd, d)[c]^(-1)`.
- w3-corner-crossed (4647e9e53f) shows that every Sylvester rank function on `C(M_-, F_3) x| V` kills
  `eps_- <~ q_[0]`. So any `f_+` design makes `eps_-` properly infinite in `S_-`, and it must defeat every rank
  function on every subalgebra containing its supports together with `H`.
