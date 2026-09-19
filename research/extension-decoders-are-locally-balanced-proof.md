---
rg: 2
id: extension-decoders-are-locally-balanced-proof
kind: route
title: Local fibre counts are moved by local bijections or by conjugation in a finite matrix algebra
target: extension-decoders-are-locally-balanced
requires: []
---

This route uses the notation of `extension-decoders-are-locally-balanced`.
- The shift is `(lambda_g u)_h = u_(g^-1 h)`, and a memory `W ∋ e` means that `sigma(u)_h` depends only on
  `u|_(hW)`.
- For `h ∉ D_F` we have `hW ∩ FS = ∅`, so `sigma(p ∪ c)_h` does not depend on `p`. This justifies restricting
  the count `N_c` to `D_F`.
- Only `c` restricted to `D_F W \ FS` affects `N_c`.

**Step 0: a reformulation.** Fix `F` and `c`. For `v` on `D_F`, put `Fib_c(v) = {p ∈ A^(FS) : sigma(p ∪ c)|_(D_F) = v}`.
Then `sigma` is balanced at `(F, c)` if and only if `|Fib_c(v)| = |Fib_c(v')|` whenever `v` and `v'` agree on
`B_F`. To prove this, it is enough to exhibit, for each such pair, an injection `Fib_c(v) -> Fib_c(v')`,
because the relation is symmetric. When `A = Z/d`, the pairs `(v, v + k)` with `k ∈ A^F`, extended by `0` on
`B_F`, are exactly the pairs agreeing on `B_F`.

**Step 1: (A), translation lifts.**
- Let `T_e` change only coordinates in `S`. Its conjugate `T_f = lambda_f T_e lambda_f^-1` changes only
  coordinates in `fS`.
- For `k ∈ (Z/d)^F`, the map `T^k = prod_(f ∈ F) T_f^(k_f)` is well defined, because the `T_f` commute. It
  changes only coordinates in `FS`, and the same holds for its inverse `T^(-k)`.
- So `T^k` restricts to a bijection of the slice `{u : u|_(G \ FS) = c}`.
- From `sigma o T_f = sigma + delta_f`, which follows from `sigma o T_e = sigma + delta_e` by equivariance, we
  get `sigma(T^k u) = sigma(u) + k`.
- So `T^k` maps `Fib_c(v)` bijectively onto `Fib_c(v + k)`. Step 0 finishes the proof.
- For an absorption `Psi`, (2) to (3) of the monomial theorem gives the lift `T_e(u) = Psi^-1(Psi(u) + (delta_e, 0))`.
  It is local because `Psi` and `Psi^-1` are cellular automata. If `M'` is a memory of `Psi^-1`, then `T_e`
  changes only coordinates in `M'^-1`, so `S = {e} ∪ M'^-1` works.

**Step 2: (B), quantum extensions.**
- Let `𝒜_Q` be the matrix algebra `(x)_(h ∈ Q) M_d`, for finite `Q`. Put `V_f = Phi(X_f)`. Then
  `V_f ∈ 𝒜_(fR)` by equivariance and finite propagation, and the `V_f` commute because the `X_f` do.
- For `k ∈ (Z/d)^F`, let `X^k = prod X_f^(k_f)` and `V_k = Phi(X^k) ∈ 𝒜_(FR)`. Put `S = R`, so
  `D_F = F ∪ FRW^-1`, and let `Q = D_F W`. Note `FR ⊆ Q`, since `e ∈ W` and `e ∈ W^-1`.
- Let `P_v ∈ 𝒜_(D_F)` be the diagonal cylinder projection onto `{u|_(D_F) = v}`. Since `X|j> = |j+1>`, we have
  `X^k P_v X^(-k) = P_(v+k)`.
- The projection `Pi_v = Phi(P_v)` is multiplication by the indicator of `{u : sigma(u)|_(D_F) = v}`. It lies in
  the diagonal of `𝒜_Q`, because that indicator depends only on `u|_Q`.
- Let `C_c ∈ 𝒜_(Q \ FR)` be the diagonal projection onto `{u|_(Q \ FR) = c}`. It commutes with `V_k`, because
  the supports are disjoint.
- Therefore `V_k (C_c Pi_v) V_k^* = C_c Phi(X^k P_v X^(-k)) = C_c Pi_(v+k)`.
- `C_c Pi_v` is a diagonal projection in `𝒜_Q ≅ M_(d^|Q|)`, and its rank is `|Fib_c(v)|`. Conjugation by the
  unitary `V_k ∈ 𝒜_Q` preserves rank, so `|Fib_c(v)| = |Fib_c(v + k)|`.
- Strictness and monomiality were never used.

**Step 3: (C), reversible automata.**
- Let `S = {e} ∪ W'^-1`, and let `v`, `v'` agree on `B_F`. Take `p ∈ Fib_c(v)` and put `u = p ∪ c`.
- Let `y` be `sigma(u)` with its values on `F` replaced by `v'|_F`. Then `y|_(D_F) = v'`, and `y` agrees with
  `sigma(u)` off `F`.
- Put `u' = sigma^-1(y)`. The value `u'_h` depends only on `y|_(hW')`. If `h ∉ FW'^-1`, then `hW'` misses `F`,
  so `u'_h = sigma^-1(sigma(u))_h = u_h`.
- So `u' = p' ∪ c` with `p' ∈ A^(FS)`, and `p' ∈ Fib_c(v')`.
- The map `p -> p'` is injective, because `sigma^-1` is. Step 0 finishes the proof.

**Step 4: (D), consequences of balance.**
- *(D1), post-surjectivity.* Let `z` agree with `sigma(u)` off the finite set `E`. Take `F = E` and
  `c = u|_(G \ ES)`, and put `v = sigma(u)|_(D_F)` and `v' = z|_(D_F)`.
  - `v` and `v'` agree on `B_F`, which is disjoint from `F = E`.
  - `Fib_c(v)` contains `u|_(ES)`, so by balance `Fib_c(v')` contains some `p'`.
  - Put `u' = p' ∪ c`. It agrees with `u` off `ES`, and `sigma(u')` equals `v'` on `D_F`.
  - Off `D_F`, the output `sigma(u')` equals `sigma(u)`, which equals `z` there, since `E ⊆ D_F`. So
    `sigma(u') = z`.
- *(D2), measure preservation.* Fix a finite `F`. Averaging over `u ~ mu` gives
  `mu(sigma|_(D_F) = v) = E_c[|Fib_c(v)|] q^(-|FS|)`.
  - This depends only on `v|_(B_F)`. So under `sigma_* mu`, the output on `F` is uniform conditionally on the
    output on `B_F`, and hence uniform.
  - This holds for every finite `F`, so all cylinder marginals of `sigma_* mu` are uniform, and
    `sigma_* mu = mu`.

**Step 5: (E), one-site lifts.**
- Take `F = {e}`, `D = D_(e) = {e} ∪ SW^-1`, and a context `c` on `G \ S`. The fibres `Fib_c(v)` partition
  `A^S` and depend only on `c|_(DW \ S)`.
- By balance, for each orbit `{v + j delta_e : j ∈ Z/d}` the fibres `Fib_c(v + j delta_e)` have a common size
  `m`. Enumerate them as `p_(j,1), ..., p_(j,m)`, and set `pi_c(p_(j,i)) = p_(j+1,i)`, indices mod `d`.
- This defines a permutation `pi_c` of `A^S` with `pi_c^d = id`. It maps `Fib_c(v)` to `Fib_c(v + delta_e)`, and
  it is chosen as a function of the finite pattern `c|_(DW \ S)`.
- Put `T_e(u) = pi_(c)(u|_S) ∪ c` with `c = u|_(G \ S)`. Then:
  - `T_e` is a local bijection that changes only `S`, and `T_e^d = id`;
  - `sigma(T_e u) = sigma(u) + delta_e`, on `D` by construction and off `D` because nothing there reads `S`.
- Put `T_g = lambda_g T_e lambda_g^-1`. Then `T_g` reads `gDW` and writes `gS`, and `S ⊆ DW`.
- So `T_e` and `T_g` commute whenever `gS ∩ DW = ∅` and `S ∩ gDW = ∅`. This leaves only the finite set
  `K = DW S^-1 ∪ S (DW)^-1` of `g` to check.
- Every other condition of (3) in `monomial-quantum-automata-are-topological-bernoulli-absorptions` holds by
  construction.

**Step 6: the recorded consequences.**
- *Non-injective implies not pre-injective, and no dual surjunctivity.* This is (D1) together with Capobianco–Kari–Taati
  Theorem 1 as recorded in `capobianco-kari-taati-dual-surjunctivity-toolkit`: post-surjective and pre-injective
  imply reversible.
- *Sofic calibration.* On sofic groups, CKT Theorem 2 upgrades post-surjective to pre-injective, hence to
  reversible. Conversely, (C) shows reversible automata are balanced.
- *The `Z/2` example.* `u_n + u_(n+1)` is onto, so it preserves `mu`, since `Z` is amenable. It is 2-to-1, so it is
  not injective.
  - By the Garden of Eden theorem on `Z`, surjective implies pre-injective.
  - If it were post-surjective, CKT would make it reversible, a contradiction.
  - So by (D1) it is not balanced for any lift set.
- *The quantum-transfer implication.* A decoder of a strict pair is not injective. If its pullback extends to a
  quantum automaton, then by (B) and (D1) it is post-surjective. So `(tau, sigma)` witnesses
  `strict-pairs-admit-post-surjective-decoders` for that group. Then
  `post-surjective-decoders-convert-strict-pairs-to-dual-failures` gives the dual failure.
