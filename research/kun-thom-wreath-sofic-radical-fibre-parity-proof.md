---
rg: 2
id: kun-thom-wreath-sofic-radical-fibre-parity-proof
kind: route
title: Kill fibre pairs with the rigid defect criterion in every sofic image, then embed the fibre-parity quotient in a residually finite product
target: kun-thom-wreath-sofic-radical-is-fibre-parity-kernel
requires:
  - sofic-groups-kill-rigid-compression-defects
  - sofic-radical-soficization
  - kun-thom-nonsofic-wreath
---

Notation as in the target. `kun-thom-nonsofic-wreath` supplies Theorem E:
`Gamma` and `G` are residually finite Kazhdan groups and `Gamma` is infranormal
in `G`, i.e. its compression semigroup `P_Gamma = {g : g Gamma g^-1 <= Gamma}`
generates `G`.

**Step 0: the normal closure is `EL_r(R)`.** `E = EL_r(R)` is normal in
`G = E x| SL_d(Z)` and contains `Gamma`, so `N <= E`. Conversely `N` contains
`e_ij(1)` for `i != j`. For `b in R` and `k` not in `{i, j}` (possible since
`r >= 3`), the Steinberg relation gives `[e_ij(1), e_jk(b)] = e_ik(b)`, and this
lies in `N` because `N` is normal. So `N` contains every elementary matrix, and
`N = E`.

**Step 1: every sofic image kills `K_even`.** Let `phi : W -> S` be a
homomorphism to a sofic group.
- **The criterion applies.** `H = phi(W)` is countable and sofic (subgroups of
  sofic groups are sofic). `phi(Gamma)` and `phi(G)` are Kazhdan, being quotients
  of Kazhdan groups. Since `phi(P_Gamma)` lies in `P_(phi(Gamma))` and generates
  `phi(G)`, `phi(Gamma)` is infranormal in `phi(G)`. The root lamp is fixed by
  `Gamma`, so `z = phi(e_Gamma)` centralizes `phi(Gamma)`.
- **One fibre pair.** By `sofic-groups-kill-rigid-compression-defects`, for
  `g in G` and `gamma in Gamma`,

      1 = [phi(g) z phi(g)^-1, phi(gamma)] = phi([e_(g Gamma), gamma]) = phi(e_(g Gamma) e_(gamma g Gamma)).

- **All conjugates.** Conjugating by `h in G` gives
  `e_(hg Gamma) e_(h gamma g Gamma)` in `ker phi`. With `y = hg` and
  `c = g^-1 gamma g`, this is `e_(y Gamma) e_(y c Gamma)`, for every `y in G`
  and every conjugate `c` of an element of `Gamma`.
- **The whole fibre.** Let `n = c_1 ... c_k in N` be a product of such conjugates.
  Telescoping gives

      e_(y Gamma) e_(y n Gamma) = prod_(i=1..k) e_(y c_1...c_(i-1) Gamma) e_(y c_1...c_i Gamma),

  which lies in `ker phi` (lamps are involutions and commute).
- **Even configurations.** Two cosets `x Gamma`, `x' Gamma` lie in one `N`-fibre
  iff `x' in x N Gamma = x N`, i.e. `x' = x n` with `n in N`. A fibre-even finite
  configuration is a product of such pairs. So `K_even <= ker phi`.

**Step 2: the fibre-parity quotient is residually finite.**
- **The quotient map.** Summing lamps over fibres,
  `direct_sum_(G/Gamma) Z/2 -> direct_sum_(G/N) Z/2`, is `G`-equivariant with
  kernel `K_even`. It extends to a surjection `W -> W_N` with kernel `K_even`.
- **The embedding.** `G` acts on `G/N` through `rho : G -> G/N = SL_d(Z)`, by left
  multiplication. So

      Psi(l, g) = ((l, rho(g)), g)  :  W_N -> ((Z/2) wr SL_d(Z)) x G

  is a homomorphism, since `g . l = rho(g) . l`. It is injective, because `g`
  and `l` are read off the two coordinates.
- **Residual finiteness.** `(Z/2) wr SL_d(Z)` is residually finite by Gruenberg's
  theorem: a restricted wreath product `A wr B` with `A` abelian and `A`, `B`
  residually finite is residually finite (K. W. Gruenberg, Proc. London Math.
  Soc. (3) 7 (1957), 29--62). `G` is residually finite by Theorem E. So `W_N` is
  residually finite, hence sofic.

**Step 3: conclusion.** `Rad_sof(W)` is the intersection of the kernels of all
homomorphisms from `W` to sofic groups (`sofic-radical-soficization`). Step 1
gives `K_even <= Rad_sof(W)`. Step 2 exhibits one such kernel equal to `K_even`,
so `Rad_sof(W) <= K_even`. Hence `Rad_sof(W) = K_even` and
`W / Rad_sof(W) = W_N`. QED

**Step 4: the profinite closure of `Gamma` is `N`.**
- **Finite quotients.** Let `Delta` be a finite-index normal subgroup of `G`, and
  `t` a compressor. In the finite group `G/Delta`, the image `Gamma-bar` of
  `Gamma` satisfies `t-bar Gamma-bar t-bar^-1 <= Gamma-bar`. Conjugation is
  injective and `Gamma-bar` is finite, so equality holds. Compressors generate
  `G`, so `Gamma-bar` is normal in `G/Delta`.
- **Lower bound.** Then `Gamma Delta` is normal in `G` and contains `Gamma`, so it
  contains `N`. Hence `Gamma-hat = intersection_Delta Gamma Delta >= N`.
- **Upper bound.** `G/N = SL_d(Z)` is residually finite, so `N` is closed, and
  `Gamma-hat <= N-hat = N`.
- **Conclusion.** `Gamma-hat = N`.

**Credit.** This is the binary-wreath analogue of `free-lamp-radical-is-free`, by
the same collapse along `G/Gamma -> G/N`. Its only nonelementary input is Kun--Thom
Theorem 4.1, through `sofic-groups-kill-rigid-compression-defects`, so the
unrefereed-preprint trust surface of arXiv:2608.06222 travels with it. Novelty is
checked against Cairn only.
