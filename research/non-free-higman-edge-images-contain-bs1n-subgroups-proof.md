---
rg: 2
id: non-free-higman-edge-images-contain-bs1n-subgroups-proof
kind: route
title: Pushing a power of b through a relation of the edge pair in the discrete quotient, then Horner's rule against orbit growth
target: non-free-higman-edge-images-contain-bs1n-subgroups
requires:
  - higman-power-pair-collapse-is-base-uniform-up-to-torsion
  - subexponential-schreier-growth-excludes-sl3z-and-bs1k
  - nontrivial-higman-quotients-have-tower-distorted-generators
artifacts:
  - experiments/higman-diagonal-pro2-2026-09-18/b_pair_free.g
  - experiments/higman-diagonal-pro2-2026-09-18/b_pair_free-output.txt
---

Conventions: `x^y = y^-1 x y`. `H4(n)`, `A`, `B`, `A_M`, `B_M` are as in the target.
- **[U]** is `higman-power-pair-collapse-is-base-uniform-up-to-torsion`. We use its item 1 (for every
  quotient and every `M`, `A_M` is free on `a^M, c^M` or `A_M/A_M'` is finite) and its Lemma 3.1
  (`a^E = 1` implies `b^(n^E - 1) = 1`).
- **[S]** is `subexponential-schreier-growth-excludes-sl3z-and-bs1k`. We use its item 1 (orbit
  pigeonhole), its item 4 (orbit growth of `[[X, T]]` for `Z^d`-actions) and its definition of orbit
  growth.
- **[T]** is `nontrivial-higman-quotients-have-tower-distorted-generators`, item 1: in a nontrivial
  quotient of `H4 = H4(2)` every generator has infinite order.

## Step 0: symmetries and push rules

**Cyclic symmetry.** `σ : a -> b -> c -> d -> a` maps each defining relation of `H4(n)` to the next
one, so `σ` is an automorphism. If `π : H4(n) -> Q` is a quotient map, so is `π ∘ σ`. Under `π ∘ σ` the
letters `a, b, c, d` go to `b, c, d, a` in `Q`. Any statement proved for `(A; b, d)` in all quotients
therefore holds for `(B; c, a)`, and, using `σ^2`, for `(A; d, b)` with the roles of `a` and `c`
exchanged.

**Torsion around the cycle.** [U, Lemma 3.1]: `a^-E b a^E = b^(n^E)`, so `a^E = 1` gives
`b^(n^E - 1) = 1`. Applying `σ`, torsion of `b` gives torsion of `c`, then `d`, then `a`. So either
all four generators of `Q` have finite order or all four have infinite order.

**Push rules.** From `a^-1 b a = b^n` and `b^-1 c b = c^n`, for all integers `K` and all `j >= 0`:
- (P1) `b^K a = a b^(Kn)`;
- (P2) `b^(Kn) a^-1 = a^-1 b^K`;
- (P3) `b^-j c^ν = c^(ν n^j) b^-j`.

(P1) is `a^-1 b^K a = b^(Kn)`. (P2) follows from (P1) by multiplying by `a^-1` on both sides. (P3)
comes from `b^-1 c^ν b = c^(νn)`, that is `b^-1 c^ν = c^(νn) b^-1`, by induction on `j`.

## Step 1: discrete absorption (item 1)

Write `w = x_1 x_2 ... x_l` with letters `x_i ∈ {a, a^-1, c, c^-1}`. A block `a^(±M)` or `c^(±M)` is
split into `M` letters, and at the end the resulting pieces are regrouped. Put
`E_i = N + e_a(x_1 ... x_i)`, so `E_0 = N`. The hypothesis on `N` says `E_(i-1) >= 1` whenever
`x_i = a^-1`. Since `E` only drops at such letters, and then by one, `E_i >= 0` for all `i`.

*Claim.* For each `i`, `b^(-n^N) x_1 ... x_i = x_1' ... x_i' b^(-n^(E_i))`, where
`x_j' = x_j` if `x_j = a^(±1)` and `x_j' = c^(±n^(n^(E_(j-1))))` if `x_j = c^(±1)`.

*Proof by induction on `i`.* For `i = 0` there is nothing to prove. Move `b^(-n^E)` with
`E = E_(i-1) >= 0` past `x_i`:
- if `x_i = a`, (P1) with `K = -n^E` gives `b^(-n^E) a = a b^(-n^(E+1))`;
- if `x_i = a^-1`, then `E >= 1`, and (P2) with `K = -n^(E-1)` gives
  `b^(-n^E) a^-1 = a^-1 b^(-n^(E-1))`;
- if `x_i = c^(±1)`, (P3) with `j = n^E` gives `b^(-n^E) c^(±1) = c^(±n^(n^E)) b^(-n^E)`.

This proves the claim.

Take `i = l`. Then `E_l = N + Y`, and `w' := x_1' ... x_l'` lies in `A`. If `w` is a word in
`a^M, c^M`, then the `a`-letters regroup into blocks `a^(±M)` and every `c`-letter of a block
`c^(±M)` becomes a power `c^(±M n^(...))`, so `w'` lies in `A_M`. Since `w = 1` in `Q`,
`b^(-n^N) = w' b^(-n^(N+Y))`, hence

`w' = b^(n^(N+Y) - n^N)`.

- For `Y > 0` this is `b^(n^N (n^Y - 1))`.
- For `Y < 0` it is the inverse of `b^(n^(N+Y) (n^|Y| - 1))`, where `N + Y = E_l >= 0`.

Both are nonzero powers of `b`, and they lie in `A` (in `A_M`). Such an `N` always exists, for
example `N = 1 + max(0, max_u (-e_a(u)))` over all prefixes `u`.

For `(c, d)`, apply the same argument to the quotient `π ∘ σ^2`, which exchanges `a <-> c` and
`b <-> d`. It uses `c^-1 d c = d^n` and `d^-1 a d = a^n`. For `B` absorbing `c` and `a`, apply it to
`π ∘ σ` and `π ∘ σ^3`. No finiteness of `Q` is used anywhere.

## Step 2: non-free edge images absorb b and d (item 2)

Suppose `A` is not free on `a, c`. By [U, item 1] with `M = 1`, `A/A'` is finite. Let `Y >= 1` be the
order of `a A'` in `A/A'`. Then `a^Y` is a product `p` of commutators of words in `a, c`. The word
`w = a^Y p^-1` equals `1` in `Q`, and `e_a(w) = Y`, since each commutator has exponent sum zero.
Step 1 gives `m = n^N (n^Y - 1) >= 1` with `b^m ∈ A`. In the same way `e_c` gives `m' >= 1` with
`d^m' ∈ A`.

The four elements `a, b^m, c, d^m'` lie in `A` and generate it, since `a` and `c` are among them.
They satisfy:
- `(b^m)^a = b^(nm) = (b^m)^n`;
- `c^(b^m) = c^(n^m)`, iterating `c^b = c^n` `m` times;
- `(d^m')^c = (d^m')^n`;
- `a^(d^m') = a^(n^m')`.

So `A` is a quotient of `H(n, n^m, n, n^m')` in which the images of the first and third generators
generate.

## Step 3: two copies of BS(1,n) (item 3)

Assume `b` has infinite order. Then so does `b^m`. Let `ρ : BS(1,n) = < x, t | t^-1 x t = x^n > -> A`
be given by `x -> b^m` and `t -> a`. It is well defined, because `a^-1 b^m a = b^(nm)`. We show that
`ρ` is injective.

Recall `BS(1,n) ≅ Z[1/n] ⋊ Z`, where `x = (1, 0)` and `t` acts on `N = Z[1/n]` by multiplication by
`n` or `1/n`. Let `K = ker ρ`.

1. **`K ∩ N = 1`.** A nonzero element of `N` is `u = k / n^j` with `k != 0` an integer and `j >= 0`.
   Since `t^-1 x t = x^n`, conjugation `v -> t^-1 v t` multiplies `N` by `n`, so `t^-j u t^j = k`,
   that is `x^k`. `K` is normal. If `u ∈ K`, then `x^k ∈ K`, so
   `b^(mk) = 1`. That contradicts the infinite order of `b`.
2. **`K` centralizes `N`.** Both `K` and `N` are normal, so `[K, N] ⊂ K ∩ N = 1`.
3. **`K ⊂ N`.** An element `(u, s)` with `s != 0` acts on `N` by multiplication by `n^(±s) != 1`, so it
   does not centralize `N`.

Hence `K ⊂ K ∩ N = 1`, and `<a, b^m> ≅ BS(1,n)`. The same argument, with `c^-1 d^m' c = d^(nm')`, gives
`<c, d^m'> ≅ BS(1,n)`. Both subgroups lie in `A`.

The last sentence of item 3 is the torsion-around-the-cycle remark of Step 0.

## Step 4: host obstruction (item 4)

**Horner bound.** In `BS(1,n)` with generators `x, t`, write `M >= 1` as `M = ε_0 + n M_1` with
`0 <= ε_0 < n`. Then `x^M = x^(ε_0) t^-1 x^(M_1) t`. By induction on the number `J + 1` of base-`n`
digits of `M`, `|x^M| <= (n + 1)(J + 1)`. So `|x^j| <= (n + 1)(log_n M + 1)` for all `0 <= j <= M`.

**Pigeonhole.** Let `A` act faithfully on a set `X`, and let `S = {a, b^m}`. The element `g = b^m`
has infinite order.
- Suppose every `<g>`-orbit had at most `M` points. Then `g^(M!)` would fix `X` pointwise. That
  contradicts faithfulness.
- So some orbit `<g>x` has more than `M` points. The points `g^j x`, `0 <= j <= M`, are then
  distinct.
- They lie in `B_S(x, R)` with `R = (n + 1)(log_n M + 1)`. This is [S, item 1].

So `γ_S(R) >= M + 1`. Hence `(1/R) log γ_S(R) >= log(M + 1) / ((n + 1)(log_n M + 1))`, and as
`M -> ∞` this tends to `(log n)/(n + 1) > 0`. So the orbit growth of `A` is not subexponential for
this `S`. Equivalently, [S, item 3] (no `BS(1,k)` in a group with a faithful action of
subexponential orbit growth) applied to the subgroup `<a, b^m>`. Restricting a faithful action of a
host to a subgroup keeps it faithful.

**The listed hosts have subexponential orbit growth.** Take any finite `S` in the host.
- **Group of subexponential word growth `Γ`.** Use the left-regular action on `Γ`. Then
  `B_S(x, R) = B_S(1, R) x`, so orbit growth equals word growth.
- **`[[X, T]]` for `Z^d`.** The orbit growth is at most `(2 K_S R + 1)^d` by [S, item 4].
- **Piecewise translations of an interval (`IET` included).** Let `λ_1, ..., λ_q` be the finitely many
  translation lengths used by the elements of `S`. The elements of `S^-1` use their negatives. One
  step moves a point by some `±λ_i`, so `B_S(x, R) ⊂ x + { Σ ν_i λ_i : ν_i ∈ Z, Σ |ν_i| <= R }`. That
  set has at most `(2R + 1)^q` points, so the orbit growth is polynomial. The action on the
  interval is faithful.
- **Wobbling group `W(Γ)`** (permutations of the vertex set moving each vertex a bounded distance)
  of a connected bounded-degree graph. If every `s ∈ S` moves points at most `K` apart, then
  `B_S(x, R)` lies in the graph ball of radius `KR` about `x`. So the orbit growth is at most the
  growth of `Γ`, which is subexponential by assumption.

Subgroups of these hosts inherit the faithful actions. This proves item 4.

## Step 5: whole-group version (item 5)

Let `phi : H4(n) -> G`, where `G` acts faithfully with subexponential orbit growth.
1. `<phi(a), phi(b)>` is the image of `BS(1,n)` under `x -> phi(b)` and `t -> phi(a)`.
2. If `phi(b)` had infinite order, Step 3 (with `m = 1`, the same argument) would make this map
   injective. Then `G` would contain `BS(1,n)`, contradicting Step 4 (or [S, item 3]).
3. So `phi(b)` has finite order, and by Step 0 all four images do.
4. For `n = 2`, `phi(H4)` is a quotient of `H4` with a torsion generator, so it is trivial by [T].

This settles the topological-full-group orbit-count spark. The gap in its first form was that finite
orbits alone do not force finite order. That gap is closed by the pigeonhole step: faithfulness plus
infinite order give arbitrarily long orbits.

## Step 6: amenable edge images (item 6)

Let `A` be amenable with `b` of infinite order. A free group of rank two is not amenable, so `A` is
not free, and Step 2 gives `m, m'`. With `L = lcm(m, m')`, `b^L` and `d^L` lie in `A`, so
`B_L ⊂ A ∩ B`, and `B_L` is amenable.

So `B_L` is not free on `b^L, d^L`. By [U, item 1] applied to `π ∘ σ` with `M = L`, `B_L / B_L'` is
finite. Let `Y >= 1` be the order of `b^L B_L'` in it. As in Step 2 there is a word `w` in
`b^(±L), d^(±L)` with `w = 1` and `b`-exponent sum `LY != 0`.

Step 1, applied to `π ∘ σ`, pushes `c^(-n^N)` through `w`. It uses `b^-1 c b = c^n` in place of (P1)
and (P2), and `c^-1 d c = d^n` in place of (P3). It gives `c^k ∈ B_L` with
`k = n^N (n^(LY) - 1) >= 1`. In that push the `b`-letters regroup into blocks `b^(±L)`, and each
`d`-letter block `d^(±L)` becomes a power `d^(±L n^(...))`, so the result lies in `B_L`. The order
`Y'` of `d^L B_L'` gives, in the same way via `π ∘ σ^3`, `a^k' ∈ B_L` with `k' >= 1`.

Hence `C := <a^k', b^L, c^k, d^L>` equals `B_L`: it contains `b^L, d^L`, and its other two generators
lie in `B_L`. It satisfies:
- `(b^L)^(a^k') = (b^L)^(n^k')`;
- `(c^k)^(b^L) = (c^k)^(n^L)`;
- `(d^L)^(c^k) = (d^L)^(n^k)`;
- `(a^k')^(d^L) = (a^k')^(n^L)`.

So `C` is a quotient of `H(n^k', n^L, n^k, n^L)`, generated by the images of its second and fourth
generators. All four generators have infinite order by Step 0, and `C` is amenable as a subgroup of
`A`.

The converse, that such a `C` yields a quotient of `H4(n)`, is not claimed.

## Calibration

- `D_oo x D_oo` (odd `n`): `b^2 = 1`, so Steps 3–6 do not apply, as they should not, since this
  `A = D_oo` acts on `Z` with linear orbit growth.
- `(Z/(n-1))^4`: torsion, consistent.
- `b_pair_free.g` (`H4(3)/<<[a,c]^2>>`, pro-2 classes 1 to 8): the closure of `B` is not free
  pro-2 from class 7 on, and `B_k^ab = (Z/64)^2` at classes 6 to 8. `A_k ∩ B_k = 1` through class 8,
  which is consistent with Step 1 because `b^64 = 1` at those classes. This is evidence, not proof:
  all `G_k` are finite, and a non-free pro-2 closure does not make the discrete `B` non-free.
