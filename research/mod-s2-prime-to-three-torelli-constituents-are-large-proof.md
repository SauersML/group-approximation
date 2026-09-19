---
rg: 2
id: mod-s2-prime-to-three-torelli-constituents-are-large-proof
kind: route
title: Split rho|K into isotypic blocks, untensor each block over its stabilizer, untwist the multiplicity factor by Malcev, and read the determinant of the extended constituent as a point of the census torus
target: mod-s2-prime-to-three-torelli-constituents-are-large
requires:
  - mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit
  - mod-s2-gamma4-torelli-census-is-one-thirtieth
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
---

Notation as in the target. Inputs:
- **[TA]** `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`: the definitions of `W`, `d`, `d_inf`;
  (TA2) monotonicity `Gamma'' <= Gamma' => d(Gamma'') <= d(Gamma')`; (TA4) `d(Sp_4 Z) = 1/15`, `d(Gamma(3)) = 1/15`;
  (TA5) the gap implies `d_inf > 0`.
- **[G4]** `mod-s2-gamma4-torelli-census-is-one-thirtieth`: `d(Gamma') >= 1/30` for every `Gamma' >= Gamma(4)`.
- **[HOM]** `genus-two-mapping-class-group-homology-and-symplectic-quotient`: `M` is finitely presented and
  `1 -> K -> M -> Sp_4(Z) -> 1` is exact. So every finite-index subgroup of `Gamma` is finitely generated.

Standard facts, not re-pinned:
- **(F1) Malcev.** Finitely generated subgroups of `GL_n(C)` are residually finite.
- **(F2) Finite-dimensional C\*-algebras.** A unital \*-subalgebra `A` of `M_D(C)` is `(+)_i M_(n_i)`. Its
  minimal central projections `e_i` give `e_i C^D = C^(n_i) (x) C^(m_i)`, with `e_i A = M_(n_i) (x) 1` and
  commutant of `e_i A` in `End(e_i C^D)` equal to `1 (x) M_(m_i)`.
- **(F3) Skolem-Noether.** Every \*-automorphism of `M_n(C)` is `Ad P` for a unitary `P`, unique up to a
  scalar.
- **(F4)** `|exp(2 pi i x) - 1| = 2 sin(pi ||x||)`. So if `||U - omega I||_op = eps < 2` for a unitary `U`, then
  every eigenvalue of `U` is `omega exp(2 pi i a)` with `|a| <= phi/(2 pi)`, `phi = 2 arcsin(eps/2) < pi`.
- **(F5)** `R/Z` is divisible, so a homomorphism from a subgroup of an abelian group to `R/Z` extends.

## Step 1: blocks and their stabilizers

`A = span rho(K)` is a unital \*-algebra, since `rho(K)` is a group of unitaries. Apply (F2). Because `K` is
normal, `Ad rho(g)` maps `rho(K)` onto itself for every `g in M`, so it is a \*-automorphism of `A` and
permutes the minimal central projections. For `k in K`, `rho(k) in A` commutes with the centre, so `K <= H_i`.
There are finitely many `e_i`, so `[M : H_i] < infinity`. Write `rho(k)|V_i = sigma_i(k) (x) 1`. As
`span sigma_i(K) = M_(n_i)`, `sigma_i` is irreducible.

## Step 2: untensoring over the stabilizer

Let `g in H_i`. Then `U = rho(g)|V_i` is a unitary of `V_i` with `U (M_n (x) 1) U^* = M_n (x) 1`. By (F3),
`Ad U` restricted to `M_n (x) 1` is `Ad (P (x) 1)` for a unitary `P`. Then `(P^* (x) 1) U` commutes with
`M_n (x) 1`, so by (F2) it is `1 (x) Q` with `Q` unitary. So `rho(g)|V_i = P(g) (x) Q(g)`, with `P(g)` and
`Q(g)` unique up to inverse scalars. For `k in K` choose `P(k) = sigma_i(k)` and `Q(k) = 1`.

Put `q(g) = [Q(g)] in PU(m_i)`. From `rho(g) rho(h) = rho(gh)`, `q` is a homomorphism `H_i -> PU(m_i)`, and it is
trivial on `K`. So it factors through `Gamma_i = H_i / K`.

Also, for `g in H_i` and `k in K`,
```text
sigma_i(g k g^(-1)) (x) 1 = rho(g) (sigma_i(k) (x) 1) rho(g)^* = P(g) sigma_i(k) P(g)^* (x) 1 .
```
So `sigma_i(g k g^(-1))` and `sigma_i(k)` are unitarily conjugate. (*)

## Step 3: Malcev untwisting (PC1)

`Delta = q(Gamma_i) <= PU(m)` is finitely generated, by [HOM]. Its preimage `Delta~ <= SU(m)` is a central
extension of `Delta` by `mu_m`, so it is finitely generated and linear, hence residually finite by (F1). Choose a
finite-index normal `Lambda~ <= Delta~` with `Lambda~ ∩ mu_m = 1`. Then `Lambda~` maps isomorphically onto a
finite-index `Lambda <= Delta`. Let `s : Lambda -> Lambda~` be the inverse isomorphism, put
`Gamma''_i = q^(-1)(Lambda)` (finite index in `Gamma_i`) and `M'' = pi^(-1)(Gamma''_i)`.

For `g in M''` put `Q''(g) = s(q(g))`. This is an honest homomorphism `M'' -> SU(m)` with `Q''(K) = 1`, and
`Q(g) = lambda(g) Q''(g)` for a scalar `lambda(g)`. Put `P''(g) = lambda(g) P(g)`. Then
`rho(g)|V_i = P''(g) (x) Q''(g)`. Multiplicativity of `rho` and of `Q''` gives
`P''(g) P''(h) (x) Q''(gh) = P''(gh) (x) Q''(gh)`, so `P''` is an honest unitary representation of `M''`. For
`k in K`, `sigma_i(k) (x) 1 = P''(k) (x) 1`, so `P''|K = sigma_i`.

If `m_i = 1`, `Q` is a scalar, `q` is trivial, and one takes `Lambda = Delta = 1`, `Gamma''_i = Gamma_i`.

## Step 4: the determinant is a point of the census torus (PC2)

`psi = det P''` is a character of `M''`, so it factors through `H_1(M''; Z)`. Take right coset representatives
`g_c` of `M''` in `M`, as in [TA], and put `T_c = g_c t_s g_c^(-1) in K`, whose class in `H_1(M'')` is `v_c`.
Define `theta_c in R/Z` by `psi(T_c) = exp(2 pi i theta_c)`. For `w in W(Gamma''_i)`,
`sum_c w_c theta_c` is the value of `psi` on `sum_c w_c v_c = 0`, so `theta in W(Gamma''_i)^perp`.

Compute `theta_c` from the spectrum. `rho(T_c)` is conjugate to `rho(t_s)`, so
`||rho(T_c) - omega I|| = eps`. Since `rho(T_c)|V_i = sigma_i(T_c) (x) 1`, the eigenvalues of `sigma_i(T_c)` are
eigenvalues of `rho(T_c)`. By (F4) they are `omega exp(2 pi i a_j)` with `|a_j| <= phi/(2 pi)`. Hence
```text
psi(T_c) = det sigma_i(T_c) = exp(2 pi i (n/3 + n h_c)),     h_c = (1/n) sum_j a_j,   |h_c| <= phi/(2 pi).
```
- If `n ≡ 1 (mod 3)`, then `theta_c - 1/3 ≡ n h_c (mod 1)`.
- If `n ≡ 2 (mod 3)`, then `-theta` also lies in the subgroup `W^perp`, and `-theta_c - 1/3 ≡ -n h_c (mod 1)`.

In both cases some point of `W(Gamma''_i)^perp` has all coordinates within `n phi/(2 pi)` of `1/3`, so
```text
d(Gamma''_i) <= n phi/(2 pi) = n arcsin(eps/2)/pi .
```
This is (PC2), since `d(Gamma''_i) >= d_inf` by definition. For `omega^(-1)`, apply this to the complex
conjugate representation `rho-bar`: it has the same blocks and dimensions, with constituents `sigma_i-bar`. At
`n = 1`, (PC2) reads `arcsin(eps/2) >= pi d_inf`, which is (TA1).

## Step 5: the unconditional case (PC3)

If `m_i = 1`, then `Gamma''_i = Gamma_i` (Step 3). If `Gamma_i >= Gamma(3)`, then by (TA2) and (TA4)
`d(Gamma_i) >= d(Gamma(3)) = 1/15`. If `Gamma_i >= Gamma(4)`, then `d(Gamma_i) >= 1/30` by [G4]. If
`Gamma_i >= Gamma(2)`, then `Gamma_i >= Gamma(4)`. If `rho(K)` acts irreducibly, then there is one block,
`H_1 = M`, `Gamma_1 = Gamma`, `m = 1`, and `d(Gamma) = 1/15` by (TA4).

## Step 6: consequences (PC4, PC5)

(PC4) is (PC2) read contrapositively. For (PC5):
- The gap implies (TAP), by (TA5).
- The gap implies (SB) vacuously: under the gap, `1/3` is not in `Z_hon`.
- Conversely, suppose (TAP) and (SB) hold and the gap fails. `Z_hon` is closed under negation, so `1/3 in Z_hon`.
  Then (SB) gives an honest `rho` with `eps < 2` and a constituent with `3` not dividing `n` and
  `n arcsin(eps/2) < pi d_inf`, which contradicts (PC2).
- The reduction `1/3 in Z_hon => 1/3 in Z_ab` implies (SB). Torelli-abelian `rho` with `eps -> 0` have all
  constituents of dimension `1`, so `n arcsin(eps/2) = arcsin(eps/2) -> 0`.

## Step 7: the determinant-type kill (PC6)

**What the class retains.**
- Any extension of the irreducible `sigma_i` to a finite-index `M''' >= K` equals `chi (x) P''` on
  `M''' ∩ M''` for a character `chi` trivial on `K` (Schur's lemma). So its determinant agrees with `psi` on `K`.
- The characters of `M'''` that restrict to `(det sigma_i)^j` on `K` take the values `j theta` on separating
  twists.
- Restriction to a smaller level `Gamma''' <= Gamma''` pulls `theta` back to a point of `W(Gamma''')^perp`,
  giving no new condition.

So a determinant-type argument knows only `n_i` and the conditions
"`theta^(i)` with `theta^(i)_c = n_i/3 + n_i h_i(T_c)` lies in `W(Gamma'')^perp` for some finite-index
`Gamma''`." Here `h_i(T)` depends only on the `M''`-class of `T`, because every separating twist is
`M''`-conjugate to some `T_c` and (*) holds.

**Consistency points.** For each constraint set below, an assignment of eigen-angles meets every retained
condition. Fix `Gamma''` and put all eigen-angles of `sigma_i(T_c)` equal to `h_c`.
- *Case `3 | n`.* Take `h = 0`. Then `theta = 0`, which lies in every `W^perp`. So no bound at all.
- *Case `3` does not divide `n`, level-wise optimum.* Let `theta*` attain `d(Gamma'')` (replace it by
  `-theta*` if `n ≡ 2 mod 3`). Let `n h_c` be the representative of `theta*_c - n/3` in `[-1/2, 1/2]`. Then
  `|h_c| <= d(Gamma'')/n`, and by (F5) there is a character of `M''` with values `theta*` on the `T_c`. The
  eigenvalue distance is `2 sin(pi d(Gamma'')/n)`. So the best bound any determinant-type argument can prove
  at level `Gamma''` is `n arcsin(eps/2) >= pi d(Gamma'')`, which is (PC2).
- *Uniform point.* Let `h_c = (j - n/3)/n` with `|j - n/3| = 1/3`. Then `theta = 0`, which is consistent at
  every level, with eigenvalue distance `2 sin(pi/(3n))`.

**Where every member dies.** The retained data depend on the constituent only through `n mod 3` and the
product `n h`. A representation all of whose near-`omega` Torelli constituents have `3 | n`, or `n >= 1/(3 eps)`
or so, passes every determinant-type test. This is the step "`3 | n_i`, or `n_i >= c/eps`". The kill is at the
level of the arguments: it does not assert that such representations exist.
