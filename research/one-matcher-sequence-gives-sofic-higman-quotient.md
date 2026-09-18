---
rg: 2
id: one-matcher-sequence-gives-sofic-higman-quotient
kind: claim
title: One sequence of finite doubling actions with a Hamming-small matcher whose fourth power almost commutes gives a nontrivial sofic Higman quotient
distinct_from:
  base-two-exponential-permutations-iff-sofic-higman-quotient: that needs order-four permutations for every large odd modulus; this needs one sequence of finite sets, any exact doubling action, and only almost-commutation of the fourth power, and with that equivalence it shows the weak and strong forms are the same.
  order-four-bs-matcher-builds-higman-opnorm-microstate: that builds operator-norm unitary microstates, which do not give soficity; this builds permutation microstates in normalized Hamming distance and concludes a nontrivial sofic quotient.
  order-four-exponential-permutations-exist-for-base-two: that is the open statement for all large odd moduli; this shows a subsequence with a weaker return condition already implies it.
artifacts:
  - research/one-matcher-sequence-gives-sofic-higman-quotient-proof.md
  - experiments/higman-exponential-permutations-2026-09-17/sat_min_breakpoints.py
---

**ESTABLISHED** by `one-matcher-sequence-gives-sofic-higman-quotient-proof`.

**Setting.** `H4 = < a,b,c,d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2 >`.
On a finite set `X` use the normalized Hamming distance
`d(s,t) = #{x : s(x) != t(x)} / |X|` on `Sym(X)`. A *doubling action* on `X` is a
pair `A, B` in `Sym(X)` satisfying the defining relator of `BS(1,2) = < a,b | b^a = b^2 >`
exactly, with `A` in the role of `a`. Example: `X = Z/nZ`, `n` odd, `A(x) = 2x`,
`B(x) = x + 1`.

**Theorem.** Let `(X_j, A_j, B_j)` be doubling actions and `f_j` in `Sym(X_j)`.
Put

```text
eps_j = d(f_j^-1 A_j f_j, B_j)            (matcher defect)
r_j   = d(f_j^4 A_j, A_j f_j^4)           (return defect)
```

If `eps_j -> 0`, `r_j -> 0` and `d(A_j, 1) >= delta > 0` for all `j`, then `H4` has a
nontrivial sofic quotient. Quantitatively, `U_i = f^-i A f^i` (`i = 0..3`) satisfy
all four Higman relators up to distance `3 eps + 3 r`, and `d(U_i, 1) = d(A, 1)`.

**Corollary.** For odd `n` let

```text
S(n)  = min { #{x : f(x+1) != 2 f(x)} : f in Sym(Z/nZ), f^4 = id },
S'(n) = min { #{x : f(x+1) != 2 f(x)} + #{x : f^4(2x) != 2 f^4(x)} : f in Sym(Z/nZ) }.
```

The following are equivalent:
1. `S(n)/n -> 0` along all odd `n` (the open statement
   `order-four-exponential-permutations-exist-for-base-two`);
2. `liminf S'(n)/n = 0` over odd `n`;
3. `H4` has a nontrivial sofic quotient.

(1 => 2) is trivial since `S' <= S`. (2 => 3) is the theorem with `A = x -> 2x`,
`B = x -> x+1`, which moves `n - 1` points. (3 => 1) is
`base-two-exponential-permutations-iff-sofic-higman-quotient`.

**What it changes for finite search.**
- A positive certificate never needs uniformity in `n`. Some sequence with
  defect ratio tending to `0` suffices, and its moduli can be chosen freely.
- The constraint `f^4 = id` may be relaxed to `f^4` commuting with doubling on all
  but `o(n)` points. For prime `p` the centralizer of `x -> 2x` contains every
  `x -> u x` and every equivariant permutation of the `<2>`-orbits, so the search
  space strictly grows.
- The dichotomy is sharp. If item 3 fails then `S'(n) >= kappa n` for all large odd
  `n`, for some `kappa > 0`: no subsequence can be sublinear.
