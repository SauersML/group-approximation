---
rg: 2
id: balanced-decoders-colour-fibred-absorption-proof
kind: route
title: Run the one-site lifts colour class by colour class, so that a product in colour order trivializes every fibre; where no colouring can be read from the target, only the fibres over the symmetric part remain
target: locally-balanced-decoders-are-colour-fibred-absorption-decoders
requires:
  - extension-decoders-are-locally-balanced
---

Notation is as in the target. Conventions:
- the shift is `(lambda_g u)_x = u_(g^-1 x)`, written `g.u`;
- `g^-1 . y` is the translate with `(g^-1 . y)_x = y_(gx)`, which carries site `g` to `1`;
- all maps between compact zero-dimensional spaces are continuous. An equivariant continuous map has a local
  rule on a finite window (Curtis–Hedlund, by compactness).

**Step 0: one-site lifts.** Let `sigma` be locally balanced with lift set `S`.
- By (E) of `extension-decoders-are-locally-balanced`, and Step 5 of its proof, there is a bijection `T_e` of
  `A^G` that writes only on `S`, reads only on `R = DW` (where `D = {e} ∪ SW^-1` and `S ⊆ R`), has `T_e^q = id`,
  and satisfies `sigma ∘ T_e = sigma + delta_e`.
- Put `T_g = lambda_g T_e lambda_g^-1`. It writes on `gS`, reads on `gR`, and `sigma ∘ T_g = sigma + delta_g`.
- Put `E = {1} ∪ R S^-1 ∪ S R^-1`, a finite symmetric set.
- If `g ≠ h` and `g^-1 h ∉ E`, then `gS ∩ hR = ∅` and `hS ∩ gR = ∅`. So neither map reads what the other writes,
  and their write sets are disjoint because `S ⊆ R`.

**Step 1: products over an `E`-independent set.** Let `I ⊆ G` be *`E`-independent*, meaning `g^-1 h ∉ E` for
distinct `g, h ∈ I`. Let `n : I -> Z/q`. Define `P = P_(I,n)` by:
- `P(u)_x = (T_g^(n_g) u)_x` if `x ∈ gS` for some `g ∈ I`;
- `P(u)_x = u_x` otherwise.

Such a `g` is unique, since `x ∈ gS ∩ hS` gives `g^-1 h ∈ SS^-1 ⊆ RS^-1 ⊆ E`.

1. *Agreement with finite products.* For a finite `I' ⊆ I`, the product `Π_(g ∈ I') T_g^(n_g)`, taken in any
   order, writes `T_g^(n_g)(u)|_(gS)` on each `gS`. This is because no factor reads what another writes. So `P`
   agrees with these finite products on every finite region, once `I'` is large.
2. *Locality.* `P(u)_x` depends only on `u|_(gR)` and `n_g` for the unique `g`, or on `u_x`. So `P` is continuous,
   jointly in `(u, n)`, and local.
3. *Output.* `sigma(P u) = sigma(u) + Σ_(g ∈ I) n_g delta_g`. Each coordinate of `sigma` reads a finite window,
   so this follows from the finite case.
4. *Bijectivity.* `P_(I,-n)` inverts `P_(I,n)`. Again this follows from the finite case, coordinate by
   coordinate.
5. *Equivariance.* `lambda_h P_(I,n) lambda_h^-1 = P_(hI, n(h^-1 .))`, since `lambda_h T_g lambda_h^-1 = T_(hg)`.

**Step 2: scheduled products.** Let `kappa : J -> [m]` be a proper colouring, for the graph `g ~ gk` with
`k ∈ E \ {1}`, of a set `J ⊆ G`. Let `d : G -> Z/q` be supported in `J`. Put

    R^d_kappa = P_m ∘ ... ∘ P_1,   P_c = P_(kappa^-1(c), d|_(kappa^-1(c))).

Each colour class is `E`-independent. By Step 1:
- `R^d_kappa` is a bijection;
- `sigma ∘ R^d_kappa = sigma + d`, since round `c` changes the output only on `kappa^-1(c)`;
- `R^d_kappa` restricts to a bijection `sigma^-1(t) -> sigma^-1(t + d)` for every target `t`;
- `(R^d_kappa)^-1` is `P_1^-1 ∘ ... ∘ P_m^-1`;
- the value of `R^d_kappa(u)` at `x` depends only on `u`, `d` and `kappa` inside the finite set `x (S^-1 R)^m`.
  Round `c` at `x` uses only the sites `g ∈ x S^-1` and reads `gR`.
  So it is jointly continuous in `(u, d, kappa)` whenever `J` and `kappa` vary continuously. This means that
  whether `g ∈ J`, and the colour of `g`, are clopen conditions on the data near `g`.
- By Step 1.5, it is equivariant under simultaneous translation of `u`, `d`, `J` and `kappa`.
- Enlarging `E` keeps every colour class `E`-independent for the old `E`. So we may assume `E ≠ {1}` whenever
  `G ≠ 1`, and then `C_E` has no constant point.

**Step 3: Theorem I, (1) ⇒ (2).** Take `E` as in Step 0 and `N = |E|`.
- *`C_E` is nonempty.* Every vertex of the graph `g ~ gk`, `k ∈ E \ {1}`, has degree at most `N - 1`. So every
  finite subgraph has a greedy proper `N`-colouring, and compactness of `[N]^G` gives a colouring of `G`.
  `C_E` is an SFT, with forbidden patterns on the pairs `{1, k}`.
- *Definition.* Put `Y = sigma^-1(c_0)`. It is closed and shift-invariant, because `c_0` is constant, and it
  contains `0^G`. Define

      Psi(kappa, u) = (kappa, sigma(u), (R^(sigma(u) - c_0)_kappa)^-1 u),
      Theta(kappa, y, w) = (kappa, R^(y - c_0)_kappa w).

  Here `J = G`. By Step 2, `R^(y - c_0)_kappa` maps `Y = sigma^-1(c_0)` bijectively onto `sigma^-1(y)`. So the
  third coordinate of `Psi` lies in `Y`, and `sigma` of the second coordinate of `Theta(kappa, y, w)` is `y`.
- *Inverse pair.* `Theta ∘ Psi = id`, since `R^d (R^d)^-1 u = u` with `d = sigma(u) - c_0`. Conversely, for
  `u' = R^(y - c_0)_kappa w` we have `sigma(u') = y`, so `Psi(kappa, u') = (kappa, y, w)`.
- *Continuity and equivariance.* `d = sigma(u) - c_0` is a local function of `u`. By Step 2, `R^d_kappa` and its
  inverse are local in `(u, d, kappa)` and equivariant under simultaneous translation. Both `c_0` and `C_E` are
  translation-invariant. So `Psi` is a continuous equivariant bijection of compact Hausdorff spaces, hence a
  homeomorphism, and its decoder `sigma` does not see `kappa`.
- *Size of `Y`.* For fixed `kappa`, `u -> (sigma(u), W_kappa(u))` is a bijection `A^G -> A^G x Y`. So `sigma` is
  onto, and it is injective exactly when `|Y| = 1`.

**Step 4: Theorem I, (2) ⇒ (1).** Let `Psi(kappa, u) = (kappa, sigma(u), W(kappa, u))` be a `C_E`-fibred
absorption, and write `Psi^-1(kappa, y, w) = (kappa, theta(kappa, y, w))`.
- By Curtis–Hedlund for the diagonal shift, there is a finite `M ∋ e` such that `W(kappa, u)_x` depends only on
  `kappa|_(xM)` and `u|_(xM)`, and `theta(kappa, y, w)_x` depends only on `kappa`, `y` and `w` on `xM`.
- Fix any `kappa ∈ C_E`. For `g ∈ G`, put `T'_g(u) = theta(kappa, sigma(u) + delta_g, W(kappa, u))`.
  - `sigma(T'_g u) = sigma(u) + delta_g`.
  - `T'_g` is a bijection, with inverse `u -> theta(kappa, sigma(u) - delta_g, W(kappa, u))`.
  - `T'_g` changes only `gM^-1`. If `x ∉ gM^-1`, then `g ∉ xM`, so the inputs of `theta` on `xM` agree with
    those of `theta(kappa, sigma(u), W(kappa, u)) = u`, and `T'_g(u)_x = u_x`.
- *Balance with `S' = M^-1`.* Fix a finite `F`, a context `c` on `G \ FS'`, and `k ∈ A^F`. Let `T^k` be the
  composite of `k_f` copies of `T'_f` for each `f ∈ F`, in any fixed order. The `T'_f` need not commute, and they
  are not used as conjugates of one map.
  - Each factor maps the finite slice `{u : u|_(G \ FS') = c}` injectively into itself. So `T^k` is a bijection of
    the slice.
  - `sigma(T^k u) = sigma(u) + k`.
  - So `T^k` maps `Fib_c(v)` injectively into `Fib_c(v + k)`. Step 0 of `extension-decoders-are-locally-balanced-proof`
    then gives balance at `(F, c)`.
- Only commutation of the lifts (Step 1 there) is dropped. The count in Step 0 there needs only an injection per
  pair.

**Step 5: Theorem L.**
- *The map `y -> y_U`.* Whether `g ∈ Z_U(y)` depends only on `g^-1 . y ∈ U`. Since `U` is clopen, this is decided
  by `y` on a finite window around `g`. Also `Z_U(h.y) = h Z_U(y)` and `c_0` is constant. So `y -> y_U` is a
  continuous equivariant map (a cellular automaton), and `y_U = y` on `Z_U(y)`.
- *(i) ⇒ (iii).* Let `Psi = (sigma, W) : A^G -> A^G x Y'` be as in (i). Since `c_0` is `G`-fixed, `W` restricts to
  an equivariant homeomorphism `j : Y = sigma^-1(c_0) -> Y'`. For any clopen `U`, put
  `L(y, w) = Psi^-1(y_U, j(w))`. It is continuous and equivariant, and `L(y, .)` is a bijection
  `Y -> sigma^-1(y_U)`.
- *(iii) ⇒ (ii)* is trivial.
- *(ii) ⇒ (i), colouring from the target.* Put `K_U = A^G \ U`. It is compact and misses `Sym_E`. So every
  `z ∈ K_U` has `k.z ≠ z` for each `k ∈ E \ {1}`, and hence has a clopen neighbourhood `V_z` with
  `V_z ∩ k.V_z = ∅` for all `k ∈ E \ {1}`.
  - Take a finite subcover `V_1, ..., V_r` of `K_U`, and put `Q_i = (V_i ∩ K_U) \ (V_1 ∪ ... ∪ V_(i-1))`. This is
    a clopen partition of `K_U`, with `Q_i ∩ k.Q_i = ∅`.
  - Put `J(y) = G \ Z_U(y) = {g : g^-1 . y ∈ K_U}`, and set `kappa_y(g) = i` when `g^-1 . y ∈ Q_i`.
  - *Proper.* If `g`, `gk ∈ J(y)` have the same colour `i` with `k ∈ E \ {1}`, then `z = g^-1 . y ∈ Q_i` and
    `k^-1 . z = (gk)^-1 . y ∈ Q_i`. So `z ∈ Q_i ∩ k.Q_i`, a contradiction.
  - *Local.* Membership in `J(y)` and the colour of `g` are clopen conditions on `y` near `g`, and
    `J(h.y) = h J(y)`, `kappa_(h.y)(hg) = kappa_y(g)`.
- *(ii) ⇒ (i), the section.* Put `d(y) = (y - c_0) 1_(J(y))`. It is supported in `J(y)`, and `y = y_U + d(y)`
  because `Z_U(y)` and `J(y)` partition `G`. Define

      s(y, w) = R^(d(y))_(kappa_y) (L(y, w)).

  - By Step 2, `R^(d(y))_(kappa_y)` maps `sigma^-1(y_U)` bijectively onto `sigma^-1(y)`. So `sigma(s(y, w)) = y`,
    and `s(y, .)` is a bijection `Y -> sigma^-1(y)`.
  - Hence `s : A^G x Y -> A^G` is a bijection. By Step 2 and the locality above, it is continuous and
    equivariant.
  - It is a continuous bijection of compact Hausdorff spaces, so `Psi = s^-1` is an equivariant homeomorphism
    `A^G -> A^G x Y`, with first coordinate `sigma`. This is (i) with `Y' = Y`.
- *Absorption.* By the last bullet of Step 3, `|Y| >= 2` when `sigma` is not injective.

**Step 6: Proposition F.** Let `Psi = (sigma, W)` be as in (i), let `H ≤ G`, and let `y` be `H`-fixed.
- For `u ∈ sigma^-1(y)` and `h ∈ H`, we have `Psi(h.u) = (h.y, h.W(u)) = (y, h.W(u))`. So `W` restricts to an
  `H`-equivariant homeomorphism `sigma^-1(y) -> Y'`. All such fibres are `H`-conjugate to `Y' ≅ sigma^-1(c_0)`.
- *Constants.* Take `H = G`. The fibres `sigma^-1(c^G)`, `c ∈ A`, are pairwise `G`-conjugate. So they contain the
  same number `m` of `G`-fixed points, that is, of constant configurations.
  - `sigma` maps constants to constants. So each of the `q` constants of `A^G` lies in exactly one fibre over a
    constant target.
  - Counting gives `qm = q`, so `m = 1`.
  - Hence `sigma` is a bijection of the constants.

**Step 7: the measure remark (sketch only, not claimed).**
- Let `mu` be the uniform Bernoulli measure. Each `T_g` is a bijection changing finitely many coordinates, so it
  preserves `mu`. The same holds for each `P_(I, n)` and each `R^d_kappa`, coordinate window by window.
- With a Borel proper colouring `kappa(xi)` of the free part of an auxiliary Bernoulli shift `xi ∈ E'^G`, Step 3
  applies fibrewise in `xi`. Then `Psi_kappa` pushes `mu` to a measure on `A^G x Y` whose first marginal is `mu`
  (by (D2)). Its conditional fibre measures should be `R`-invariant, which would force the product form
  `mu x nu_kappa`.
- `nu_kappa` is not a point mass when `sigma` is not injective, by the mutually erasable pair in
  Capobianco–Kari–Taati. None of this is used above.