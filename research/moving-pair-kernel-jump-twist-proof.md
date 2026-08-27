---
rg: 2
id: moving-pair-kernel-jump-twist-proof
kind: route
title: Twist any lift by the parity character of a finite exhaustion window
target: exact-lamp-lifts-admit-moving-pair-kernel-jumps
requires: []
---

## Direct proof

**Item 1.**  For `m,m' in I_X`,

```text
|supp(m+m') cap A_n| = |supp(m) cap A_n| + |supp(m') cap A_n| - 2|...|,
```

so `sigma_n(m+m')=sigma_n(m)sigma_n(m')` and `sigma_n` is a character of
`I_X` with values in `{+1,-1}`.  Hence `tau_n(m)=diag(1,sigma_n(m))` is an
exact homomorphism into diagonal — so commuting — involutions of `U(2)`.

**Item 2.**  A fixed `m in I_X` has finite support, and `A_n` exhausts `X`, so
`supp(m) subset A_n` for all large `n`.  Then
`|supp(m) cap A_n|=|supp(m)|`, which is **even** because `m` lies in the
augmentation kernel.  Therefore `sigma_n(m)=1` and `tau_n(m)=I`.

Now take any finite presentation of `Gamma=I_X rtimes V` with generators
`s_1,...,s_k` (actor) and `b_1,...,b_l` (lamps, fixed elements of `I_X`), and
assign

```text
s_j |-> I_2,      b_i |-> tau_n(b_i).
```

Substituting `I_2` for every actor letter turns a relator word `r` into the
product of its lamp letters, that is into `tau_n(m_r)` where `m_r in I_X` is
the `F_2`-sum of the lamp letters of `r`.  Each `m_r` is a **fixed** element,
so `tau_n(m_r)=I` for all large `n` and every relator is satisfied exactly.
The lamp corona classes are all trivial by the previous paragraph, so this
model represents the trivial corona representation of `Gamma`, whose lamp
restriction is indeed killed — the conclusion the route wants is true here;
only the checksum fails.

**Item 3.**  Suppose `A_n` meets the infinite `s`-orbit.  If
`s^(-1)(A_n) = A_n` then `A_n` is `s`-invariant and finite, so it cannot meet
an infinite orbit; hence `s^(-1)(A_n) \ A_n != empty`.  Pick

```text
x_n in s^(-1)(A_n) \ A_n,
y_n in X \ (A_n cup s^(-1)(A_n)),
```

the second set being infinite.  Then `x_n != y_n`, both lie outside `A_n`, so

```text
sigma_n(b_(x_n,y_n)) = (-1)^0 = 1,     tau_n(b_(x_n,y_n)) = I.
```

On the other hand `s x_n in A_n` and `s y_n notin A_n`, so

```text
sigma_n(b_(s x_n,s y_n)) = (-1)^1 = -1,
tau_n(b_(s x_n,s y_n)) = diag(1,-1),
```

whose operator-norm distance from `I` is exactly `2`.

**Tail-partition variant.**  Choose finite `A_n` exhausting `X` and containing
`s^k x_0` for `|k|<=n` but not `s^(-n-1)x_0`, `s^(n+1)x_0`.  Let `E_n` make
every point of `A_n` a singleton class and `X \ A_n` one class, and realize
`E_n` by mapping `e_x |-> e_([x])` into `F_2^(X/E_n)` (finitely many classes)
followed by a faithful diagonal representation of that finite elementary
abelian group.  Every fixed distinct pair is eventually separated, so the
fixed-pair implication is eventually vacuous, while `x_n=s^(-n-1)x_0` and
`y_n=s^(n+1)x_0` share the tail class and their `s`-images do not.
