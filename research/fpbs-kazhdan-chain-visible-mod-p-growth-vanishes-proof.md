---
rg: 2
id: fpbs-kazhdan-chain-visible-mod-p-growth-vanishes-proof
kind: route
title: Run the support-shrinking iteration through the visible Frattini subgroup and check growth on a deep finite quotient
target: fpbs-kazhdan-chain-visible-mod-p-growth-vanishes
requires:
  - fpbs-shalom-property-t-is-open
  - fpbs-lackenby-cocycle-support-toolkit
  - fpbs-kazhdan-cofinal-mod-p-growth-vanishes
artifacts:
  - research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md
---

Written deduction, lane `sw-007`, 2026-09-17. The ingredients (K), (L5.1),
(L6.1), (L3.3) and (Tr) are stated and proved or cited in Section
"Theorem B / Ingredients" of
`research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md`. Only the
changes to that proof are written in full here.

## Notation

- `F` is a downward directed family of finite index normal subgroups of
  `Gamma`, for example a descending chain.
- For a finite index subgroup `H`, a homomorphism `f: H -> F_p` is *visible* if
  `ker f` contains a member of `F`. The visible homomorphisms form a subspace
  `V(H)` of `H^1(H;F_p)`, whose dimension is `d_p^vis(H)`.
- Put `Phi^vis(H) = intersection of ker f` over `f` in `V(H)`.

## Three facts about the visible Frattini subgroup

1. **It contains a member.** `V(H)` is finite dimensional, since `H` is finitely
   generated (Kazhdan groups are finitely generated). Choose a basis
   `f_1,...,f_k`, with `ker f_i` containing the member `N_i`. By
   directedness some member `N` lies in every `N_i`, so `N` lies in
   `Phi^vis(H)`.
2. **The quotient is elementary abelian of rank `d_p^vis(H)`.**
   - `Phi^vis(H)` is normal in `H`, since each `ker f` is.
   - `H/Phi^vis(H)` embeds in `F_p^k` via `(f_1,...,f_k)`.
   - The map is onto because the `f_i` are linearly independent.
3. **Visible rank is computed by one deep quotient.** Let `N''` be a member inside
   `Phi^vis(H)`, and suppose `N''` lies in `H`. Then
   `d_p(H/N'') = d_p^vis(H)`.
   - Every homomorphism `H/N'' -> F_p` is visible.
   - Every visible homomorphism kills `Phi^vis(H)`, which contains `N''`.

   For any member `N'` inside `H`, every homomorphism `H/N' -> F_p` is
   visible, so `d_p(H/N') <= d_p^vis(H)`.

## Proof of part 1

Suppose that for some prime `p` and `c > 0` the limit fails. Let `F'` be the set
of members `N` with `d_p^vis(N) >= c[Gamma:N]`.
- For a chain, `F'` is an infinite subchain, hence cofinal in `F`. A cofinal
  subfamily defines the same visible classes, so we may replace `F` by `F'`.
- For a directed family, failure of the limit gives `F'` cofinal in `F`, and
  the same replacement applies.
- Member indices are unbounded. Otherwise the chain is eventually constant,
  equal to `Gamma_inf`, and then `d_p^vis(Gamma_inf) = d_p(Gamma_inf/Gamma_inf) = 0`.

Take the finitely presented Kazhdan cover `pi: G -> Gamma` with `<X|R>`, pair
`(X,kappa)` and complex `K`. Put `u = ceil(2|R|/c)`, `theta = theta_u` and
`eps = kappa^2/(4|X|)`.

**Good subgroups.** A subgroup `A` of `G` containing `ker pi` is *good* if:
- `d_p^vis(pi A) >= c[G:A]`;
- `[G:A] > (u^2+u)/|R|`;
- `K_A` carries `u` cocycles representing independent classes in
  `H^1(K_A;F_p)`, whose union of supports is a fraction `sigma` of the 1-cells;
- `pi A` contains a member.

For the first good subgroup, take a member `N` of index above
`(u^2+u)/|R|` and `u/c`, and put `A = pi^(-1)N`. Then
`d_p(A) >= d_p(N) >= d_p^vis(N) > u`, and `sigma <= 1`.

**Step (from `A` with fraction `sigma` to `A'` with fraction at most
`theta sigma`).**

1. *Visible Frattini cover.*
   - Let `Phi = Phi^vis(pi A)` and `B = pi^(-1)Phi`.
   - By fact 2, `A/B` is elementary abelian of rank `n = d_p^vis(pi A) >= c[G:A]`.
   - So `K_B -> K_A` is a regular cover with elementary abelian deck group of rank `n`.
   - `K_A` has `r = |R|[G:A]` 2-cells.
2. *Lift (L5.1).* Theorem 5.1 of Lackenby holds for every regular elementary
   abelian cover. It gives at least
   `(n-u)u - r >= 2|R|[G:A] - u^2 - |R|[G:A] > u` independent classes on
   `K_B`, all supported in the preimage of the old support.
3. *Shrink (L6.1).* This gives `u` independent classes on `K_B` with support
   fraction at most `theta sigma`.
4. *Coprime descent.*
   - By fact 1, `Phi` contains a member `N`.
   - Let `P` be a Sylow `p`-subgroup of `Phi/N`, and `A'_Gamma` its preimage in `Phi`. Put `A' = pi^(-1)A'_Gamma`.
   - `[B:A']` is prime to `p`. So by (Tr) the pulled-back classes on `K_(A')` stay independent, with support fraction at most `theta sigma`.
5. *Visible growth is inherited.*
   - `N` is normal in `Gamma`, so it is normal in `A'_Gamma`, with index `p^k = |P|`.
   - By fact 1 applied to `N`, there is a member `N''` inside `Phi^vis(N)`. We may take `N''` inside `N`, by directedness.
   - Put `Q = A'_Gamma/N''`, a finite group. `N/N''` is a normal subgroup of `Q` of index `p^k`.
   - Lemma 3.3 of Lackenby holds for every finitely generated group, in particular for `Q`. It gives `d_p(N/N'') <= (d_p(Q)-1)p^k + 1`.
   - By fact 3, `d_p(N/N'') = d_p^vis(N) >= c[Gamma:N]` and `d_p(Q) <= d_p^vis(A'_Gamma)`.
   - Hence `d_p^vis(A'_Gamma) >= 1 + (c[Gamma:N]-1)/p^k = c[Gamma:A'_Gamma] + 1 - p^(-k) >= c[G:A']`.
   - Also `[G:A'] >= [G:A]`, and `A'_Gamma` contains the member `N`. So `A'` is good.

**Contradiction.** After `m` steps with `theta^m < eps`, some `K_(A_m)` carries a
nonzero class with a cocycle of support fraction below `eps`. This contradicts (K).

## Proof of part 2

- `Gamma_n/Gamma_m` is finite, so `d((Gamma_n/Gamma_m)^ab) = max_p d_p(Gamma_n/Gamma_m)`.
- By fact 3, `d_p(Gamma_n/Gamma_m) <= d_p^vis(Gamma_n)`.
- The Hadamard torsion bound on the cover (Corollary B' of the artifact) gives
  `d_p^vis(Gamma_n) <= d_p(Gamma_n) <= |R|[Gamma:Gamma_n] log L/log p`.
  Here `L` is the maximal relator length, at least 2.
- So for `p > L^(|R|/c)` the ratio is below `c` for every `n` and `m`.
- For the finitely many primes `p <= L^(|R|/c)`, part 1 gives an `n_0` beyond which each ratio is below `c`.

## Checks

- **Special case.** If `F` is `p`-Frattini closed, then `Phi_p(N)` contains a
  member for every member `N`. So every class of `N` is visible,
  `d_p^vis = d_p`, and the theorem restricts to Theorem B (general form).
- **Where the Kazhdan hypothesis enters.** Only in (K). For `F_2`, which is
  not Kazhdan, take the directed family of all normal subgroups of `p`-power
  index. Every class of a member is visible, so
  `d_p^vis(N) = [F_2:N] + 1`. Visible growth is linear, and steps 1--5 run
  without obstruction. By contrast, a normal chain of `F_2` with trivial
  intersection inside a `p`-adic analytic completion (a free subgroup of
  `SL_2(Z)` along the congruence chain at `p`) has bounded `d_p^vis`. So
  visible rank genuinely depends on the chain.
- **Why normality is needed.** Step 5 uses that `N` is normal in `A'_Gamma`
  with `p`-power index. For subnormal chains, such as Lackenby's (tau) chains,
  the member inside `Phi` need not be normal in the Sylow preimage, and the
  argument stops there.
