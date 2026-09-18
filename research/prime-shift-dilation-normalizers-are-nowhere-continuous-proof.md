---
rg: 2
id: prime-shift-dilation-normalizers-are-nowhere-continuous-proof
kind: route
title: Transport the dilation orbit, then compare x^r growth with prime shifts and use p-adic Euler sequences
target: prime-shift-dilation-normalizers-are-nowhere-continuous
requires: []
---

**Item 1.**
- `0` is the only fixed point of `m_2`. `π` maps the fixed points of `m_2` onto
  those of `m_(β(2))`, which are also `{0}`. So `π(0) = 0`.
- For `a > 0`, `π(a) = π(m_a(1)) = m_(β(a))(π(1)) = β(a) c_+`, and likewise
  `π(-a) = β(a) c_-`. So `π` determines `c_+` and `c_-`, and conversely.

**Item 2.**
- Let `x_0 > 0`. For `y > 0`, `π(x_0 y) = c_+ β(x_0) β(y) = π(x_0) β(y)`. So `π`
  is continuous at `x_0` if and only if `β` is continuous at `1`. The case
  `x_0 < 0` is the same.
- Suppose `β` is continuous at `1`. It is a homomorphism on the dense subgroup
  `Q_>0` of `R_>0`, and it is uniformly continuous in logarithmic coordinates. So
  it extends to a continuous homomorphism `R_>0 -> R_>0`, which has the form
  `x -> x^r`.
- `β(2)` is a prime `q >= 3`, so `r > 0` and `q = 2^r`. The prime
  `l = β^-1(2)` is not `2`, so `2 = l^r`.
- Hence `log q = r log 2` and `log 2 = r log l`. These give
  `log q · log l = (log 2)^2`.
- But `q` and `l` are both at least `3`, so the left side is at least
  `(log 3)^2 > (log 2)^2`. This is a contradiction.

**Item 3.**
- Fix `p`. The prime `l = β^-1(p)` differs from `p`. Put `y_j = l^((p-1)p^j)`.
- Euler's theorem gives `l^(p-1) ≡ 1 mod p`, and raising to the power `p^j`
  gives `y_j ≡ 1 mod p^(j+1)`. For `p = 2`, `l` is odd and `l^(2^j) ≡ 1 mod 2^(j+1)`.
  So `y_j -> 1` in `Q_p`.
- `β(y_j) = p^((p-1)p^j) -> 0` in `Q_p`.
- For `x_0 in Q^x`, `x_0 y_j -> x_0`. But
  `π(x_0 y_j) = π(x_0) β(y_j) -> 0 != π(x_0)`, since `π(x_0) != 0` by item 1.
- At `0`: `p^j -> 0`, while `π(p^j) = c_+ β(p)^j`. The prime `β(p)` is not `p`, so
  this is a `p`-adic unit of absolute value 1 and does not tend to `0 = π(0)`.

**Item 4.**
- By items 2 and 3 the conclusion holds for every such `π`, whatever the choice
  of `β` with no fixed prime.
- The map `φ_p` of the example sends `[1,2)` onto `[1,p)` affinely, so
  `φ_p(2x) = p φ_p(x)` by construction. It is a bijection of `Q_>0` because the
  intervals `[2^j, 2^(j+1))` and `[p^j, p^(j+1))` tile `Q_>0`.
