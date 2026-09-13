---
rg: 2
id: theorem-e-liftable-masa-crux-contains-sl-d-z-dec-proof
kind: route
title: Tensor the projective permutation modules over all torsion points, tensor with any model of SL_d(Z), and push partitions down by amplification invariance
target: theorem-e-liftable-masa-crux-contains-sl-d-z-dec
requires:
  - at-op62-holds-for-representation-lifts
  - liftable-abelian-subalgebras-are-amplification-invariant
  - elementary-groups-over-fg-rings-have-property-t
  - liftable-masa-in-every-model-iff-uniform-hs-kun-partitions
---

Notation of the claim; `p` is the characteristic of `F_q`, `l != p` a prime, and `[e]_Q = (Q^e - 1)/(Q - 1)`.

**1. The finite ring.** `B_l = L/(x_i^l - 1) = F_q[(Z/l)^d]` is semisimple since `l != p`, so
`B_l = prod_(P in X_l) F_P`. Because `x^(lw) - 1` lies in the ideal for every `w in Z^d`, each substitution
`phi_M(x^w) = x^(Mw)` preserves it. So `SL_d(Z)` acts on `B_l` and permutes `X_l` through field isomorphisms
`F_P -> F_(MP)`. `EL_r(L) -> EL_r(B_l) = prod_P SL_r(F_P)` is onto, and so is its restriction to `Gamma`, because
`R_+ -> B_l` is onto. Over `F_qbar`, with a primitive `l`-th root of unity `zeta`, the points `X_l` are the
orbits of `v -> qv` on `(Z/l)^d` via `v -> (zeta^(v_1), ..., zeta^(v_d))`. Every nonzero orbit has size
`o_l = ord_l(q)`, and `M` acts on `(Z/l)^d` by an invertible matrix `M'` (a transpose-inverse of `M` mod `l`).

**2. The representation.** `G_l = EL_r(B_l) x| SL_d(Z)` acts on the product set `Y_l = prod_P P^(r-1)(F_P)`:
`k` coordinatewise, and `M` by moving coordinate `P` to `MP` through the field isomorphism. The subspace
`V_l = (x)_P l^2_0(P^(r-1)(F_P))` of `l^2(Y_l) = (x)_P l^2(P^(r-1)(F_P))` is invariant. So `tau_l`, the action on
`V_l` composed with `G -> G_l`, is a unitary representation of `G`.

**3. Irreducibility on the vertex.** `SL_r(F)` acts 2-transitively on `P^(r-1)(F)`, so the permutation module is
the trivial module plus the irreducible `l^2_0`. A tensor product of irreducible representations of the
factors of a direct product is irreducible. Since `Gamma` maps onto `prod_P SL_r(F_P)`, `tau_l(Gamma)' = C`.

**4. One factor.** Let `k in SL_r(F)`, `|F| = Q`, be non-scalar. Its eigenlines are the disjoint union of the
projective spaces of its eigenspaces, of dimensions `e_i <= r - 1` with `sum e_i <= r`. Since
`[a]_Q + [b]_Q <= [a + b - 1]_Q + 1` for `a, b >= 1`, the count is at most `[r-1]_Q + 1`. The character of
`l^2_0` at `k` is (number of fixed lines) `- 1`, and its dimension is `[r]_Q - 1 = Q [r-1]_Q`. So
`|chi(k)| / dim <= 1/Q <= 1/2`.

**5. Traces vanish.** Fix `g = (k, M) != 1`. `tau_l(g)` maps factor `P` to factor `MP` by unitaries `T_P`, so
`tr tau_l(g) = prod_(cycles c) Tr(T_(M^(l_c - 1) P) ... T_P)`, one trace on one factor per cycle.
- **`M != I`.** A cycle of length `l_c >= 2` contributes at most `dim V_P` out of `(dim V_P)^(l_c)`, and
  `dim V_P >= 2`. So `|tr| / dim <= 2^(-m_l/2)`, where `m_l` counts the moved points. Since `d` is odd, `M` is
  not scalar over `Z`, so `M'` is non-scalar mod `l` for all but finitely many `l`. Then the `v` with
  `M'v in <q> v` lie in proper eigenspaces, at most `2 l^(d-1)` of them. So
  `m_l >= (l^d - 1 - 2 l^(d-1)) / o_l >= l^(d-1)/2` for large `l`.
- **`M = I`, `k != 1`.** A scalar matrix `c I` in `SL_r(L)` has `c = a x^w` with `c^r = 1`, so `w = 0` and
  `a^r = 1`, hence `a = 1` because `gcd(r, q - 1) = 1`. So `k` is not scalar, and some off-diagonal entry or
  difference of diagonal entries is a nonzero `f = x^(-w) g`, with `g` a polynomial of degree `<= D` in each
  variable. If `k_P` is scalar, `g` vanishes on the orbit of `P`. By induction on `d`, `g` has at most
  `d D l^(d-1)` zeros on `mu_l^d`. So at least `(l^d - 1 - d D l^(d-1)) / o_l >= l^(d-1)/2` points have
  `k_P` non-scalar, each contributing a factor `<= 1/2` by step 4.

In both cases `tr tau_l(g) / dim tau_l -> 0`.

**6. The model.** Let `h_n` be lifts of `h` with `h_n(1) = 1`, and `sigma_n = tau_(l_n) (x) (h_n o quo)`.
- The multiplicativity defect of `sigma_n` is that of `h_n`, so `sigma` is a homomorphism.
- `tau(sigma_n(g)) = tr(tau_(l_n)(g))/N_n * tau(h_n(quo g)) -> 0` for `g != 1`, so `sigma` is trace-preserving.
- `quo(Gamma) = 1`, so `sigma_n|Gamma = tau_(l_n)|Gamma (x) 1` is genuine: (H1) holds with `pi_n = sigma_n|Gamma`.

**7. The commutant.** `Gamma` is Kazhdan (`elementary-groups-over-fg-rings-have-property-t`, `r >= 3`). By
`at-op62-holds-for-representation-lifts` and step 3,
`sigma(Gamma)' cap M = prod_U (tau_(l_n)(Gamma)' (x) M_(k_n)) = 1 (x) prod_U M_(k_n)`. For `y` there,
`sigma(g) (1 (x) y) sigma(g)^* = 1 (x) h(quo g) y h(quo g)^*`, and `quo` is onto. So
`sigma(G)' cap M = 1 (x) (h(SL_d(Z))' cap prod_U M_(k_n))`.

**8. Masas.** The masas of `1 (x) Q_h` are `1 (x) D` for the masas `D` of `Q_h`. By
`liftable-abelian-subalgebras-are-amplification-invariant`, `1 (x) D` lifts to partitions of
`M_(N_n) (x) M_(k_n)` iff `D` lifts to partitions of `M_(k_n)`. This is item 2.

**9. Consequence.** If the crux holds at the pair, step 8 applies to every homomorphism
`h : SL_d(Z) -> U(prod_U M_(k_n))`, for every sequence and ultrafilter. `SL_d(Z)` is Kazhdan for `d >= 3`,
so `liftable-masa-in-every-model-iff-uniform-hs-kun-partitions` gives `DEC_kappa(SL_d(Z))`. ∎
