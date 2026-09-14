---
rg: 2
id: uniform-wp-bound-excludes-bh-targets-proof
kind: route
title: Diagonalize past the bound, realize it as a group, and transfer along the embedding
target: uniform-wp-bound-excludes-bh-universal-targets
requires: [kms-arbitrarily-hard-fp-rf-groups]
artifacts:
  - research/artifacts/boone-higman-complexity-wall-2026-09-11.md
---

Fix a recursive non-decreasing `g` and let `F(g)` be as in `(UWB1)`.

## Step 1: a recursive problem outside F(g)

Enumerate the deterministic Turing machines `M_1, M_2, ...` and reserve, for
each pair `(i,c)` of positive integers, a distinct input string `x_(i,c)`,
computably encoded and decoded. Define a decision problem `X`:

* on an input `x` that is not any `x_(i,c)`, put `x` outside `X`;
* on `x = x_(i,c)`, compute `B = c*g(c*|x|) + c*|x| + c`, simulate `M_i` on `x`
  for `B` steps, and put `x` in `X` exactly when the simulation does **not**
  halt accepting.

`B` is computable because `g` is recursive, and the simulation is clocked, so
`X` is recursive.

`X` is not in `F(g)`. Suppose `M_i` decided `X` in time
`c*g(c*n) + c*n + c`. At the reserved input `x_(i,c)` the machine halts within
`B` steps, and the definition of `X` inverts its answer there. So `M_i` is
wrong at `x_(i,c)`, a contradiction. Since every bound in `F(g)` is of that
shape for some constant, no machine decides `X` within `F(g)`.

## Step 2: realize the hardness as a group

Apply `kms-arbitrarily-hard-fp-rf-groups` to `X`. It supplies a finitely
presented residually finite group `G`, solvable of class three, with decidable
word problem, satisfying `(KMS1)`. By the closure statement `(KMS2)` and Step
1, the word problem of `G` is not in `F(g)`.

## Step 3: transfer along any embedding

Suppose `G <= H` with `H` in `C`. Let `Y` be a finite generating set of `H`
whose word problem lies in `F(g)`, say decidable in time
`T(n) = C_1*g(C_1*n) + C_1*n + C_1`. Fix a finite generating set `X_G` of `G`
— it has one, being finitely presented — and for each `s` in `X_G` a word
`w_s` over `Y` with `w_s = s` in `H`. Put `L = max_s |w_s|`.

The substitution `u |-> u_hat`, replacing each letter of a word `u` over
`X_G` by the corresponding `w_s`, is computable in time `O(L*|u|)` and
satisfies `|u_hat| <= L*|u|`. Because `G` is a subgroup of `H`,

```text
u = 1 in G   iff   u_hat = 1 in H.                            (UWB2)
```

So the word problem of `G` is decidable in time `T(L*n) + O(L*n)`. Since `g`
is non-decreasing, that bound is again of the shape
`C_2*g(C_2*n) + C_2*n + C_2` with `C_2 = C_1*L + C_1 + L`, so the word problem
of `G` lies in `F(g)`, contradicting Step 2.

Hence `G` embeds in no member of `C`. `∎`

## The Boone--Higman reading

`G` is finitely presented with decidable word problem, so it is an admissible
input to `boone-higman-conjecture`. The conjecture asserts an embedding into a
finitely presented simple group; Step 3 says no member of `C` receives `G` at
all. Therefore `C` cannot serve as the target family of a universal
construction. Nothing here refutes the conjecture, and nothing here assumes it.

The argument uses only `(UWB2)`, which is the statement that `G` is a subgroup
of `H` — no normality, no finite index, no effectiveness of the embedding, and
no bound on `L` beyond finiteness.
