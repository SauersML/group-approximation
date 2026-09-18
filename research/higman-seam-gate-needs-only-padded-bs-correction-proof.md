---
rg: 2
id: higman-seam-gate-needs-only-padded-bs-correction-proof
kind: route
title: Pad every seam by a common identity block, telescope the occurrences, and run the smallest-prime chain on exact auxiliaries
target: higman-seam-gate-needs-only-padded-bs-correction
requires: []
---

All norms are operator norms.  Unitary conjugation and block sum with `0` do
not change norms.

## Item 1: `(TPC)+(CGC) => (HMF5)`

Fix `epsilon>0`.  Let `eta=eta_CGC(epsilon/2)` and
`epsilon_1=min(eta/2, epsilon/2)`, and let `delta=delta_TPC(epsilon_1)`.  Take
a tuple `U_0,...,U_3` in `U(N)` with relator defect at most `delta`.  For each
`i`, `(A,B)=(U_i,U_(i+1))` has `||A B A^* - B^2|| <= delta`.  So `(TPC)` gives
`k_i` and an exact packet `(C_i',Z_(i+1)')` in `U(N+k_i)` within `epsilon_1` of
`(U_i (+) 1_(k_i), U_(i+1) (+) 1_(k_i))`.  Put `k=max k_i` and

```text
C_i = C_i' (+) 1_(k-k_i),     Z_(i+1) = Z_(i+1)' (+) 1_(k-k_i).
```

A block sum of exact packets is exact (`(1,1)` is exact), and the distance to
`(U_i (+) 1_k, U_(i+1) (+) 1_k)` is still at most `epsilon_1`.  Now

```text
||Z_(i+1)-C_(i+1)||
 <= ||Z_(i+1)-(U_(i+1) (+) 1_k)|| + ||(U_(i+1) (+) 1_k)-C_(i+1)||
 <= 2 epsilon_1 <= eta.
```

By `(CGC)`, `||C_i-1|| <= epsilon/2`, so

```text
||U_i-1|| = ||(U_i (+) 1_k)-1|| <= epsilon_1+epsilon/2 <= epsilon.
```

## Item 2: `(HMF5) => (CGC)`

Let `(C_i,Z_(i+1))` be exact with `||Z_(i+1)-C_(i+1)|| <= eta`.  Then

```text
||C_i C_(i+1) C_i^* - C_(i+1)^2||
 <= ||C_i (C_(i+1)-Z_(i+1)) C_i^*|| + ||Z_(i+1)^2 - C_(i+1)^2||
 <= eta + 2 eta = 3 eta,
```

using `||X^2-Y^2|| <= ||X(X-Y)||+||(X-Y)Y|| <= 2||X-Y||` for unitaries.  So
`(C_i)` is a Higman tuple with defect `3eta`, and `(HMF5)` with
`delta=3eta` gives `max||C_i-1|| <= epsilon`.

## Item 3: exact finite-dimensional Higman tuples are trivial

Let `V_i V_(i+1) V_i^* = V_(i+1)^2` in `U(K)` with `K` finite.

*Spectra.*  `V_(i+1)^2` is unitarily conjugate to `V_(i+1)`, so they have the
same finite spectrum `sigma` with multiplicities.  The spectrum of
`V_(i+1)^2` is `{lambda^2 : lambda in sigma}`, so squaring maps `sigma` onto
`sigma` and is therefore a bijection of the finite set.  Hence each
`lambda in sigma` satisfies `lambda^(2^m)=lambda` for some `m>=1`, so
`lambda^(2^m-1)=1`.  Every eigenvalue is a root of unity of odd order.  Since
`V_(i+1)` is diagonalizable, it has finite odd order `o_(i+1)`.

*Divisibility.*  From `V_i^(o_i)=1` and iterating the relation `o_i` times,

```text
V_(i+1) = V_i^(o_i) V_(i+1) V_i^(-o_i) = V_(i+1)^(2^(o_i)),
```

so `o_(i+1)` divides `2^(o_i)-1`.

*Smallest-prime chain.*  Suppose `o_(i+1)>1` and let `p` be its smallest prime
factor.  Then `p` is odd, `2^(o_i) = 1 (mod p)`, and the multiplicative order
`d` of `2` mod `p` satisfies `d>1` (as `p>=3`), `d | p-1` and `d | o_i`.  So
`o_i>1`, and the smallest prime factor `p_i` of `o_i` is at most the smallest
prime factor of `d`, which is `<= d < p = p_(i+1)`.  If any `o_j>1`, applying
this four times around the cycle gives
`p_j > p_(j-1) > p_(j-2) > p_(j-3) > p_(j-4) = p_j`, a contradiction.  Hence
every `o_i=1`, that is, every `V_i=1`.

## Item 4: auxiliary gluing

Assume `||C_i-(U_i (+) A_i)|| <= epsilon` and
`||Z_(i+1)-(U_(i+1) (+) B_i)|| <= epsilon`.  The block operator
`(U_(i+1) (+) B_i) - (U_(i+1) (+) A_(i+1))` equals `0 (+) (B_i-A_(i+1))` and has
norm `||B_i-A_(i+1)||`.  The triangle inequality therefore gives

```text
| ||Z_(i+1)-C_(i+1)|| - ||B_i-A_(i+1)|| | <= 2 epsilon,
```

which proves both directions of the seam comparison.  If the family is a
`(CGC)` input with modulus `epsilon'`, then `||C_i-1|| <= epsilon'`.  The
compression of `C_i-1` to `K` is within `epsilon` of `A_i-1`, so
`||A_i-1|| <= epsilon'+epsilon`, and likewise
`||U_i-1|| <= epsilon'+epsilon`.  Since
`Z_(i+1)` is within `eta` of `C_(i+1)`, also
`||B_i-1|| <= eta+epsilon'+2epsilon`.  So `C_i` is within
`epsilon+||A_i-1||` of `U_i (+) 1` and `Z_(i+1)` within
`epsilon+||B_i-1||` of `U_(i+1) (+) 1`.  Each packet is thus an exact packet
near the trivially padded pair: a `(TPC)` instance at accuracy
`3epsilon+2epsilon'+eta`.

Finally, take a sequence of such families with `epsilon_n -> 0` and
auxiliary seams `-> 0`, in which some auxiliary generator `A_(i_n)` or
`B_(i_n)` stays at distance `>= c>0` from `1`.  Then the packet seams
`||Z_(i+1)-C_(i+1)||` tend to `0`, and the corresponding corrected generator
on `H (+) K` stays at distance `>= c-epsilon_n` from `1` (for a `B`, pass to
`C_(i_n+1)`, which is within the seam of `Z_(i_n+1)`).  Choosing one occurrence
of each generator gives, by Item 2's computation, Higman tuples with defect
`-> 0` and a generator at distance bounded below.  This contradicts `(HMF5)`.
