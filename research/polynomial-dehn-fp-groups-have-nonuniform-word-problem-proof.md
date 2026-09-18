---
rg: 2
id: polynomial-dehn-fp-groups-have-nonuniform-word-problem-proof
kind: route
title: Feed the halting-indexed free-or-abelian acceptor M_e to the effective BORS embedding
target: polynomial-dehn-fp-groups-have-nonuniform-word-problem
requires: [bors-embedding-is-effective-in-the-machine]
---

## Step 1: the inputs and their acceptors

Let `A = {a, a^-1, b, b^-1}`.  Let `G_e = F(a,b)` if `phi_e(0)` diverges, and
`G_e = <a, b | [a,b]>` if it halts.  Let `M_e` be the deterministic machine
that, on a nonempty word `w` over `A`, does the following.

1. It freely reduces `w` and accepts if the result is empty.
2. Otherwise it computes the exponent sums of `a` and `b` in `w` and rejects
   unless both are `0`.
3. It then simulates `phi_e(0)` and accepts if and when the simulation halts.

The code of `M_e` is computable from `e`.  The language accepted by `M_e` is
the word problem of `G_e`.

- If `phi_e(0)` diverges, `M_e` accepts exactly the freely trivial words.
- If `phi_e(0)` halts, `M_e` accepts exactly the words with both exponent sums
  `0`, which is the word problem of `Z^2`.  This set includes the freely
  trivial words.

Inputs are nonempty words, as in SBR, where `L ⊆ X^+`.

**Time.**  Steps 1 and 2 take time polynomial in `n = |w|`; quadratic is
generous for a multi-tape machine.  Step 3 takes a constant `s'_e`, the cost of
simulating the halting computation, which is present only when `phi_e(0)`
halts.  Hence the time function of `M_e` is `<= T_e(n) := C_e n^2` for
`n >= 1`, with `T_e(0) = 0` and `C_e` depending on `e`.  Then
`T_e(n)^4 = C_e^4 n^8` is superadditive.

## Step 2: the hosts

Put `P_e := P(M_e)`, `x_e := b_a` and `y_e := b_b`.  This is computable from `e`
by `bors-embedding-is-effective-in-the-machine`.  The hypotheses of its
conditional clause hold by Step 1.  Therefore:

- `a -> x_e`, `b -> y_e` induces an injective homomorphism `G_e -> H_e`, which
  gives (3) and (4);
- the Dehn function of `P_e` is equivalent to `n^2 T_e(n^2)^4 = C_e^4 n^18`.

Equivalence means that `D_e(n) <= K(C_e^4 (Kn)^18) + Kn + K` for some `K`, which
is `<= K_e n^18` for `n >= 1`.  This gives (1).

## Step 3: exact time bound

Let `k` be the number of generators of `P_e`, `rho` the maximal relator length,
and `D = D_e(n) <= K_e n^18`.

A word `w` of length `n` is trivial in `H_e` if and only if a minimal van Kampen
diagram with `<= D` faces exists.  Taking paths in a spanning tree of its
1-skeleton, which has at most `n + rho D` edges, `w` freely equals a product of
at most `D` conjugates `u_i r_i^(+-1) u_i^-1` of relators with
`|u_i| <= n + rho D`.

The deterministic procedure enumerates all such products and checks free
equality with `w`.  There are at most `2^(c_e n^36)` candidates.  Each has
length `O_e(n^36)` and is checked in polynomial time.  So the procedure runs in
time `<= 2^(c'_e n^36)` for `n >= 1`.

Choose `n_e` with `2 n + 2 + 2^(c'_e n^36) <= 2^((n+1)^37)` for all `n >= n_e`.
This is possible since `(n+1)^37 - c'_e n^36 -> infinity`.  Let `N_e` be the
following machine.

- It reads at most `n_e` input symbols.
- If the input ends before that, it answers from a finite table of all words of
  length `< n_e`, stored in its finite control.  This takes time `<= n + 2`.
- Otherwise it returns the head, taking `<= n_e + 1 <= n + 1` steps, and runs
  the enumeration.

Its running time is `<= 2^((n+1)^37)` for every `n`, since `n + 2 <= 2^((n+1)^37)`
for all `n >= 0`.  This gives (2).  The table depends on whether `phi_e(0)`
halts, so `N_e` is not computable from `e`, and neither is `n_e`.

## Step 4: consequences

Uniform solvability over either class would decide
`{e : [x_e, y_e] = 1 in H_e}`, the halting set, by (4).
