---
rg: 2
id: fw-window-zero-descending-sign-proof
kind: route
title: Proof that the descending sign of shell window zero forces a trivial endomorphism core for FW inputs
target: fw-window-zero-descending-sign-forces-trivial-core
requires:
  - fw-inputs-admit-no-twisted-shell-normalization
---

Notation as in the target. "Near equal" means equal off a finite set. The four steps
mirror `fw-inputs-admit-no-twisted-shell-normalization-proof`, with the two coordinates of
the graph exchanged; Steps 1, 2 and 4 differ, Step 3 is quoted unchanged.

Hypothesis (D1): `s rho_g s^-1 = rho_(theta(g))` near, for a homomorphism
`theta : P -> P`. Equivalently `s rho_g` and `rho_(theta(g)) s` are near equal.

**Step 1: a commensurated graph.** Let `P` act on `N x N` by
`g.(x,y) = (rho_g x, rho_(theta(g)) y)`. This is an action because `theta` is a
homomorphism. Let `Gamma = {(x, x+1) : x in N}` be the graph of `s`.
- `g.Gamma` is the graph of `rho_(theta(g)) s rho_g^-1`.
- By (D1) that map is near equal to `s`, so `g.Gamma` and `Gamma` differ in a finite set.
  Hence `Gamma` is commensurated.

**Step 2: transfixing.** By FW there is a `P`-invariant `Gamma'` with `Gamma' D Gamma`
finite. Write `Gamma'_x = {y : (x,y) in Gamma'}` and `Gamma'^y = {x : (x,y) in Gamma'}`.
Invariance gives

    Gamma'_(rho_g x) = rho_(theta(g))(Gamma'_x),
    Gamma'^(rho_(theta(g)) y) = rho_g(Gamma'^y).

- `D = {x : |Gamma'_x| != 1}` is finite, because `Gamma'` is near `Gamma`, and it is
  `rho(P)`-invariant by the first identity.
- `E = {y : |Gamma'^y| != 1}` is finite and `rho(theta(P))`-invariant by the second.
- Let `N_1` be the set of `x` outside `D` whose unique partner `s'(x)` lies outside `E`.
  It is cofinite. It is `rho(P)`-invariant: for `x` in `N_1` the first identity gives
  `s'(rho_g x) = rho_(theta(g)) s'(x)`, which lies outside `E` because `E` is
  `rho(theta(P))`-invariant. So

      s'(rho_g x) = rho_(theta(g)) s'(x)   for x in N_1, g in P.             (D2)

- `s'` is injective on `N_1`, since points outside `E` have a unique partner, and `s'` is
  near equal to `s`.
- `M_1 = s'(N_1)` is `rho(theta(P))`-invariant by (D2), so `K = N - M_1` is finite and
  `rho(theta(P))`-invariant.

Note the asymmetry with the cited proof: here `N_1` is invariant under all of `rho(P)`
while `K` is invariant only under `rho(theta(P))`. Step 4 is arranged around that.

**Step 3: the orbit graph of `s'`.** Quoted from Step 3 of the cited proof, which uses only
that `s'` is an injective partial map near equal to `s` with cofinite domain and cofinite
image. Choose `n_0` above the finite set where `s'` differs from `s` or is undefined and
above `K`. Then:
- all `n > n_0` lie on one forward-infinite path, the **main ray**
  `x_0 = k_0 -> x_1 -> x_2 -> ...` with `k_0 in K` and `x_j = s'^j(k_0)`;
- for every other `k in K` the iterate `s'^j(k)` is undefined once `j > n_0 + 1`.

**Step 4: the induction.** For `g in P` and `j >= 0`, whenever the iterates below are
defined,

    rho_(theta^j(g))(x_j) = s'^j(rho_g(k_0)).                                (D3)

- `j = 0` is `rho_g(x_0) = rho_g(k_0)`.
- For `j >= 1` use `x_j = s'(x_(j-1))` with `x_(j-1)` in `N_1`, then (D2) with the element
  `theta^(j-1)(g)`, then the induction hypothesis:

      rho_(theta^j(g))(x_j) = rho_(theta(theta^(j-1)(g))) s'(x_(j-1))
                            = s'(rho_(theta^(j-1)(g)) x_(j-1))
                            = s'(s'^(j-1)(rho_g(k_0))) = s'^j(rho_g(k_0)).

  In particular the right side is defined.

**Step 5: item 1.** Let `h` be in `P_inf` and fix `j > n_0 + 1`. Since `h` lies in
`theta^(j+1)(P)`, write `h = theta^(j+1)(g')` and put `g_j = theta(g')`, so that
`h = theta^j(g_j)` with `g_j` in `theta(P)`.
- `k' = rho_(g_j)(k_0)` lies in `K`, because `K` is `rho(theta(P))`-invariant.
- By (D3), `rho_h(x_j) = s'^j(k')`, so `s'^j(k')` is defined. Since `j > n_0 + 1`, Step 3
  forces `k' = k_0`.
- Hence `rho_h(x_j) = s'^j(k_0) = x_j`.

So `rho_h` fixes `x_j` for every `j > n_0 + 1`. The main ray contains every `n > n_0`, so
`rho_h` fixes all but finitely many points: it has finite support.

**Step 6: items 2 and 3.** If every `rho_g` with `g != 1` has infinite support, item 1
forces `P_inf = 1`; as `P != 1`, `theta` is not surjective, and it is injective because
`rho` is injective on `NearSym(N)` under the same hypothesis. If `P` is co-Hopfian then an
injective `theta` is surjective, so `P_inf = P != 1`, contradicting item 2; hence (D1) has
no solution. Combining with item 2 of the cited node, which rules out
`s^-1 rho(P) s <= rho(P)`, both signs of window zero fail for a co-Hopfian FW input.

**Inputs.** FW is used only in Step 2, exactly as in the cited proof, whose sentence on
"(T) implies FW" (Brailovsky--Pasechnik--Praeger) is inherited. Co-Hopfianity of
`SL_n(Z)` for `n >= 3` is cited in the target and not read at source; nothing in this proof
depends on it.
