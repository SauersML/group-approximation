# Pro-p completions of cocompact arithmetic Sp(2,1) lattices

Lane `hyperbolic-rf-pro-p`, 2026-09-12. Context: `sp21-lattice-few-alternating-and-large-rank-quotients`
records a necessary condition for the only known alternating-quotient mechanism
(surjections onto Caprace–Kassabov transvection groups). The lattice's pro-p
completion must have infinite rank. This artifact decides what that condition
means arithmetically, gives the one certificate that would establish it, and
records why neither direction is settled.

## Setting

- `k` is a number field with ring of integers `O`. `G` is a simply connected,
  absolutely almost simple `k`-group that is `k`-anisotropic, with
  `G(k_v) = Sp(n,1)` (`n >= 2`) or `F_4^(-20)` at one archimedean place and
  compact at the other archimedean places.
- `Γ <= G(O)` has finite index, so `Γ` is a cocompact lattice with property (T).
  Every finite-index subgroup of `Γ` is again such a lattice.
- Fix a rational prime `p`, and put `Γ(p) = Γ ∩ G(O, pO)`. For `v | p` the level-`𝔭`
  principal congruence subgroups of `G(O_v)` are pro-p groups. So for every
  finite-index `Δ <= Γ(p)` the closure `Δ̄_p` of `Δ` in `G(O ⊗ Z_p) = ∏_(v|p) G(O_v)`
  is a pro-p group, a compact p-adic analytic group.
- `Δ̂_p` is the pro-p completion. The universal property gives a continuous
  surjection `π_Δ: Δ̂_p ->> Δ̄_p`. Its kernel is the **pro-p congruence kernel**
  of `Δ`.

## Imported inputs (statements only; sources not re-read in this lane)

- **(L) Lazard, Lubotzky–Mann.** A finitely generated pro-p group has finite rank
  iff it is p-adic analytic, iff it has an open uniform subgroup (Dixon–du Sautoy–
  Mann–Segal, *Analytic pro-p groups*). For uniform `U` with `Q_p`-Lie algebra
  `𝔭`, closed normal subgroups correspond to ideals up to finite index. The
  adjoint map `Ad: U -> GL(𝔭)` is continuous, with `Ad(exp X) = exp(ad X)` for
  small `X`.
- **(SR) Margulis-form superrigidity**, the same trust surface as in
  `sp21-bounded-rank-simple-quotients-almost-all-congruence-proof`. For `L` of
  characteristic `0` and `X` adjoint absolutely simple over `L`, every
  `ρ: Γ₁ -> X(L)` with Zariski-dense image (`Γ₁` of finite index in `Γ`) is
  `τ ∘ σ` for a field embedding `σ: k -> L̄` and an isogeny `τ: ^σG -> X`.
- **(V) First-cohomology vanishing.** For every finite-index `Γ₁ <= Γ` and every
  finite-dimensional complex representation `E` of `(Res_(k/Q) G)(C)`,
  `H^1(Γ₁, E) = 0`.
  - At the noncompact place this is Raghunathan's vanishing theorem (1965). It
    covers the groups `Sp(n,1)`, `F_4^(-20)` with no `SO(n,1)` or `SU(n,1)` factor.
  - For trivial and unitary constituents it is property (T)
    (Delorme–Guichardet).
  - It passes to any characteristic-`0` field by flat base change, since `Γ₁` is
    finitely presented.
- **(T)** Kostant: `Γ` and all its finite-index subgroups have finite
  abelianization.

## Theorem A. Finite rank iff finite pro-p congruence kernel

For every finite-index `Δ <= Γ(p)`, `Δ̂_p` has finite rank iff `ker π_Δ` is finite.

**(⇐)** `Δ̄_p` is p-adic analytic, and a finite extension of a finite-rank group
has finite rank.

**(⇒)** Let `P = Δ̂_p` have finite rank. By (L) choose an open uniform
`U <= P` with Lie algebra `𝔭`. Put `Δ₀ = Δ ∩ U`: it has finite index in `Δ` and is
dense in `U`.

**Step 1: `𝔭` is perfect.** If `[𝔭,𝔭] != 𝔭`, the closed commutator subgroup of
`U` has smaller Lie algebra, so `U^ab` is infinite. `Δ₀ -> U^ab` has dense image,
so `Δ₀^ab` is infinite. That contradicts (T).

**Step 2: `𝔭` is semisimple.**
- Let `𝔯` be the radical of `𝔭`. Since `𝔭` is perfect, `𝔯 = [𝔭,𝔯]` lies in the
  nilradical, so `ad X` is nilpotent on `𝔭` for `X ∈ 𝔯`.
- If `ad(𝔯) = 0`, then `𝔯` is central. With a Levi factor `𝔰`,
  `𝔯 ⊆ [𝔭,𝔭] = [𝔰,𝔰] + [𝔰,𝔯] + [𝔯,𝔯] ⊆ 𝔰`, so `𝔯 = 0`.
- Suppose `ad(𝔯) != 0`. Let `H` be the Zariski closure of `Ad(Δ₀)` in `GL(𝔭)` over
  `Q_p`. `Δ₀` is dense in `U` and `Ad(exp X) = exp(ad X)`, so `H°` contains the
  unipotent elements `exp(ad X)`, `X ∈ 𝔯` small, and these generate a nontrivial
  normal unipotent subgroup. So `R_u := R_u(H°) != 1`.
- Write `H° = S ⋉ R_u` (Levi decomposition over `Q_p`). Let `Δ₁ <= Δ₀` be the finite-
  index subgroup mapping into `H°`, and write `Ad(γ) = s(γ)u(γ)`.
- Modulo `[R_u,R_u]`, `u` gives a cocycle `ū ∈ Z^1(Δ₁, V)` with
  `V = R_u/[R_u,R_u] != 0`. Here `Δ₁` acts on `V` through `s`.
- `s: Δ₁ -> S(Q_p)` is Zariski dense in the semisimple group `S`. Apply (SR) to
  each absolutely simple factor of `S_ad` over `Q̄_p`, and lift through the
  simply connected `G`. On a finite-index `Δ₂`, `s` is then `γ ↦ (τ_i σ_i(γ))_i`.
  So `V|Δ₂` is an algebraic representation of `Res_(k/Q) G` over `Q̄_p`.
- By (V), `H^1(Δ₂, V) = 0`. Restriction to finite index is injective in
  characteristic `0`, so `H^1(Δ₁, V) = 0`. Hence `ū = s·v₀ - v₀`.
- Conjugating `Ad` by a lift of `v₀` puts `Ad(Δ₁)` inside `S ⋉ [R_u,R_u]`, a
  proper algebraic subgroup of `H°` because `V != 0`. That contradicts Zariski
  density. So `ad(𝔯) = 0`, and `𝔯 = 0`.

**Step 3: the kernel ideal vanishes.**
- `N = ker π_Δ` is closed and normal. Let `𝔫 = Lie(N ∩ U)`, an ideal of the
  semisimple `𝔭`.
- Consider `Ad|_𝔫: Δ₀ -> Aut(𝔫)`. Its Zariski closure has identity component
  `Int(𝔫)`: it contains `exp(ad 𝔫)`, and `Aut(𝔫)° = Int(𝔫)` for semisimple `𝔫`.
  So on a finite-index `Δ₃` the image is Zariski dense in the adjoint semisimple
  group `Int(𝔫)`.
- By (SR) over `Q̄_p`, factor by factor, `Ad|_𝔫 (γ) = (τ_i σ_i(γ))_i`.
  - Each embedding `σ_i: k -> Q̄_p` is continuous for a unique place `v_i | p`.
  - So `γ ↦ Ad|_𝔫(γ)` is continuous for the `p`-adic congruence topology, i.e.
    it is `F ∘ π_Δ` on `Δ₃` for a continuous `F` on `Δ̄_p`.
- Let `W₃` be the closure of `Δ₃` in `P`, an open subgroup. The continuous maps
  `w ↦ Ad(w)|_𝔫` and `F ∘ π_Δ` agree on the dense subgroup `Δ₃`, hence on all of
  `W₃`.
- For `w ∈ N ∩ W₃`, `π_Δ(w) = 1`, so `Ad(w)|_𝔫 = id`. Taking `w = exp X` with
  `X ∈ 𝔫` small gives `exp(ad X|_𝔫) = id`, so `ad X|_𝔫 = 0`. So `𝔫` is abelian,
  hence `0`.
- `N ∩ U` is a compact p-adic analytic group with zero Lie algebra, hence finite,
  and `N` is finite. ∎

**Consequences.**
- **CSP gives finite rank.** CSP (`sp21-lattice-has-congruence-subgroup-property`)
  makes the whole congruence kernel finite, so every pro-p congruence kernel is
  finite. Hence every `Δ̂_p` has finite rank. This is the classical direction
  (Lubotzky's method, Annals 1983).
- **What the transvection mechanism needs.** Its necessary condition, infinite
  rank of a pro-p completion, is exactly an infinite pro-p congruence kernel at
  `p`. That is failure of CSP *at `p`*, and it is strictly stronger than the
  "non-congruence p-quotients exist" reading recorded before.
- **Novelty.** Unchecked (no web access in this lane). The argument is
  Lubotzky's method, with the Sp(n,1) superrigidity of Corlette and
  Gromov–Schoen supplying the Zariski-dense step.

## Theorem B. The Golod–Shafarevich certificate

If some finite-index `Δ <= Γ` has `d = dim H^1(Δ;F_p) >= 2` and
`dim H^2(Δ;F_p) < d²/4`, then `Δ̂_p` has infinite rank.

- **Imported inputs** (statements only):
  - (GSV) Golod–Shafarevich–Vinberg: a pro-p group with a presentation of `d`
    generators and `r` relations with `r < d²/4` and `d >= 3` satisfies the
    Golod–Shafarevich condition (test `t = 2/d`) and is infinite.
  - (Z) Zelmanov: Golod–Shafarevich pro-p groups contain non-abelian free pro-p
    subgroups.
  - (H) `H^1(Δ̂_p;F_p) = H^1(Δ;F_p)`, and `H^2(Δ̂_p;F_p) -> H^2(Δ;F_p)` is
    injective.
- **Proof.**
  - By (H), `Δ̂_p` has a presentation with `d` generators and at most
    `dim H^2(Δ;F_p)` relations.
  - For `d = 2` the bound forces `r = 0`, so `Δ̂_p` is free of rank `2`.
  - For `d >= 3`, (GSV) and (Z) give a free pro-p subgroup of rank `>= 2`. Its
    open subgroups have unbounded rank (Schreier), so `Δ̂_p` has infinite rank. ∎
- **Combined with Theorem A.** Applied to `Δ <= Γ(p)`, one such `Δ` makes the
  pro-p congruence kernel of `Δ` infinite. So CSP fails.

## What was tried and where it stops

- **Deciding either side.** Finite rank for all `Δ <= Γ(p)` is pro-p CSP, which
  is open for every uniform `Sp(n,1)` lattice (Lubotzky arXiv:1105.4785 §4 records
  full CSP as open). Serre's philosophy predicts CSP failure in rank one. It does
  not predict at which primes the kernel is infinite.
- **Lackenby constraint on the certificate.** For any derived p-series `D_i` of
  `Δ`, `liminf d_p(D_i)/[Δ:D_i] = 0`. Otherwise `Δ` is p-large
  (`fpbs-lackenby-derived-p-series-largeness`), contradicting (T). So a
  Golod–Shafarevich certificate must use sublinear `d_p` along p-towers, with the
  mod-p `H^2` below `d²/4`.
  - This is not excluded: Ershov and Jaikin-Zapirain give Golod–Shafarevich
    Kazhdan groups.
  - `fpbs-power-p-deficiency-excludes-property-t` excludes only power
    p-deficiency.
- **Computation.** No explicit presentation of a cocompact arithmetic `Sp(2,1)`
  lattice was available, so no p-quotient or mod-p homology computation was run.
  The known Kazhdan hyperbolic presentations on main (`GHB(7)`, the
  Caprace–Kassabov family) are not arithmetic `Sp(2,1)` lattices.
- **Mod-p Betti numbers.** For a torsion-free `Δ`, `dim H^2(Δ;F_p) >= b_2(Δ)`, and
  `b_2(Δ)/[Γ:Δ] -> 0` along residual chains, because the L²-Betti numbers of
  `Sp(2,1)` vanish outside degree `4`. Torsion in `H_1` feeds both `d` and
  `H^2(-;F_p)`. So the certificate hinges on torsion growth in `H_1`, which is
  not controlled anywhere in Cairn.
