---
rg: 2
id: p-adic-dilation-normalizers-act-by-power-maps-proof
kind: route
title: Continuity makes the induced map on units a p-adic power map, and six exponentials forces the exponent to be rational
target: p-adic-dilation-normalizers-act-by-power-maps
requires: []
---

Lane proof. Notation as in the claim. Write `log` for the `p`-adic logarithm, and
`E = 1 + p^2 Z_p` for `p` odd, `E = 1 + 8 Z_2` for `p = 2`. `log` is injective on
`E`, and `E` is torsion-free.

**Step 1: β is an injective homomorphism and c(0) = 0.**
- `c(uvz) = β(u)β(v)c(z)` and `c(uvz) = β(uv)c(z)`. Take `z` with `c(z) != 0`; then
  `β(uv) = β(u)β(v)`. If `β(u) = 1`, then `c(uz) = c(z)`, so `uz = z` for all `z`
  and `u = 1`.
- `c(u·0) = β(u)c(0)` for all `u`. Pick `u` with `β(u) != 1`; then `c(0) = 0`.

**Step 2: β extends continuously.**
- Put `z_0 = p^N in U`. Then `c(z_0) != 0`, and `β(u) = c(u z_0)/c(z_0)` for
  `u in Q_0`. So `β` is continuous for the `p`-adic topology on `Q_0 ⊆ Z_p^x`.
- A homomorphism continuous at `1` is uniformly continuous. So `β` extends to a
  continuous homomorphism `β̄` on the closure `Q̄_0` of `Q_0` in `Z_p^x`, with
  values in `Z_p^x`.
- `W = Q̄_0 ∩ E ∩ β̄^-1(E)` is an open subgroup of the compact group `Q̄_0`,
  hence of finite index. Put `Q_1 = Q_0 ∩ W`, of finite index in `Q_0`.

**Step 3: β is a p-adic power map on W.**
- `log(W)` is a closed subgroup of `Z_p`. It is nonzero, since `Q_0` has
  elements of infinite order. So `log(W) = p^k Z_p` for some `k`.
- `L = log ∘ β̄ ∘ log^-1 : p^k Z_p -> Z_p` is continuous and additive, hence
  `Z_p`-linear. So `L(t) = α t` for some `α in Q_p`.
- Hence `log β(u) = α log u` for `u in Q_1`, and `α != 0` by Step 1.

**Step 4: α is rational.**
- Choose multiplicatively independent `u_0, u_1, u_2 in Q_0`, and `M >= 1` with
  `u_j^M in Q_1` (possible since `Q_1` has finite index). Put `y_j = log(u_j^M)`.
- `log` is injective on the torsion-free group `W`, so `y_0, y_1, y_2` are
  linearly independent over `Q`.
- Suppose `α ∉ Q`. Then `1, α` are linearly independent over `Q`, and the six
  numbers `exp(y_j) = u_j^M` and `exp(α y_j) = exp(log β(u_j^M)) = β(u_j)^M` are
  rational. The exponentials converge: `y_j` and `α y_j = log β(u_j^M)` lie in
  `log(E) ⊆ p^2 Z_p` (`8Z_2` when `p = 2`).
- **p-adic six exponentials theorem.** If `x_1, x_2` and `y_1, y_2, y_3` in `C_p`
  are each linearly independent over `Q`, and all `x_i y_j` lie in the domain
  of `exp_p`, then some `exp_p(x_i y_j)` is transcendental. This is the p-adic
  analogue of the six exponentials theorem of Lang and Ramachandra. For the
  p-adic statement see S. Lang, *Introduction to Transcendental Numbers* (1966),
  and M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*
  (Springer, 2000). The precise source and theorem number are not pinned; this
  is flagged for the citation referee.
- With `(x_1, x_2) = (1, α)` all six values are rational, a contradiction. So
  `α = a/b` with `a != 0`, `b >= 1`.

**Step 5: the power law.**
- For `u in Q_1`: `log(β(u)^b) = b α log u = log(u^a)`. Both `β(u)^b` and `u^a` lie
  in `E`, on which `log` is injective, so `β(u)^b = u^a`. This is item 1.
- **Item 2.** For a prime `q in Q_0`, take `M` with `q^M in Q_1`. Then
  `β(q)^(Mb) = q^(Ma)`, and `β(q)` is rational. By unique factorization,
  `β(q) = ± q^(a/b)`.
  - So `β(q_0) = q_1` is impossible for distinct primes.
  - The relations of item 2 generate `Q_0 = <q_0, q_1, q_2>`, of rank three.
    Since `c d_u c^-1 = d_(β(u))` is multiplicative in `u`, `β` is the shift on
    this group. That contradicts what was just shown.
  - Nothing above uses more than the germ of `c` at 0.
- **Item 3.**
  - For a cycle `q_0 -> q_1 -> q_0`, Step 3 gives `α^2 = 1`, so `α = ±1` is
    rational, and Step 5 applies without Step 4.
  - For a chain `q_0 -> q_1 -> q_2`, Step 3 gives `y_1 = α y_0` and `y_2 = α y_1`,
    so `y_1^2 = y_0 y_2`. Excluding this needs the four exponentials case, which
    is open.
