# sk-strong-6: which approximation classes have simple Kazhdan envelopes

Lane sk-strong-6, 2026-09-13. Every new claim below is unreviewed; they are queued with sk-verify-7.

For a class `P` of countable groups closed under subgroups, write

  (Env_P)  a finitely generated group lies in `P` iff it is a subgroup of an infinite finitely generated simple group
  with property (T) that lies in `P`.

The backward direction is automatic, so Env_P is an embedding theorem.

## 1. The table

| class `P` | infinite simple Kazhdan members | Env_P |
|---|---|---|
| residually finite; locally residually finite; amenable; residually amenable; residually solvable | none (§3) | FALSE: `Z ∈ P` has no host |
| LEF | the subshift groups `G_X`; the lamplighter hosts | TRUE (`lef-groups-embed-in-simple-kazhdan-lef-groups`, three PASSes). New: the hosts can be taken to be marked limits of finite simple expanders `SL_(3N)(F_2)` (§2) |
| sofic; hyperlinear; weakly sofic; initially subamenable; operator-MF | every known one with a proved property is LEF | OPEN. Forces a non-LEF host containing the Abels–Prüfer quotient (§4) |
| linear sofic over a finite field | a non-LEF example exists (`simple-kazhdan-linear-sofic-non-lef-group-exists`, unreviewed) | OPEN. Perfect amenable inputs have hosts (`amenable-perfect-groups-embed-in-kazhdan-linear-sofic`, unreviewed) |

Not examined: Env for all finitely generated groups (embedding into simple Kazhdan groups with no approximation
property).

**Reading.**
- LEF is the one standard approximation class, above the residually finite groups, where envelopes are known.
- Below LEF (RF, amenable, ...) they cannot exist.
- Above LEF they cost a new kind of simple Kazhdan group.

## 2. LEF groups are exactly the subgroups of simple Kazhdan limits of finite simple expanders

Claim `lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple`, route `...-proof`.

**Setup.**
- `Γ ≤ [Δ,Δ]`, with `Δ` finitely generated, infinite and LEF, by the Ore overgroup.
- `L = Z/2 ≀ Δ` acts on `Y = 2^Δ` by `(δx)(h) = x(δ^(-1)h)`, and `a` flips `x(e)`.
- `R = LC(Y,F_2) ⋊ L` and `G = EL_3(R)`.
- By `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef` (three PASSes), `G` is infinite, finitely generated,
  simple and Kazhdan, and `ℓ ↦ diag(u_ℓ,1,1)` embeds `[L,L] ⊇ Γ`.

**Configuration-space models.** This is the new point. The earlier models live on `2^(Q_n) × Q_n`. Here the base point
is dropped:
- LEF models `φ_n: B_n → Q_n` of `Δ`, with `Q_n = ⟨φ_n(S)⟩`;
- `L_n = Z/2 ≀ Q_n` acting on `Y_n = 2^(Q_n)`;
- `φ̂_n` the induced partial homomorphism on the part of `L` supported in the `n`-ball;
- `P_g` the permutation matrices;
- `D_n(f)δ_y = f(x_y)δ_y`, where `x_y ∈ Y` is any point with `x_y(w) = y(φ_n(w))` on the window of `f`;
- `ψ_n(Σ f_ℓ u_ℓ) = Σ D_n(f_ℓ)P_(φ̂_n(ℓ))`.

(i) **Covariance.** Take `ℓ = (δ,f_1)`, acting `x ↦ δx + f_1`. Then `(ℓ̂^(-1)y)(φ(w)) = y(φ(δw)) + f_2(w)`, where
`ℓ^(-1) = (δ^(-1),f_2)`, for all `w` in a fixed ball once `n` is large, and this matches `(ℓ^(-1)x_y)(w)`. So
`P_ℓ̂ D_n(f) P_ℓ̂^(-1) = D_n(f∘ℓ^(-1))`. With multiplicativity of `φ̂_n` on bounded pairs, `ψ_n` is additive and
multiplicative on fixed pairs for large `n`.

(ii) **Nonvanishing.**
- Let `r = Σ f_ℓ u_ℓ ≠ 0` with `f_(ℓ_0) ≠ 0`, and let `E = {ℓ^(-1)ℓ' : ℓ ≠ ℓ' ∈ supp r}`.
- Fixed-point sets of the `g ∈ E` are closed with empty interior, so the open set `ℓ_0^(-1){f_(ℓ_0) = 1}` contains a
  point `x` moved by every `g ∈ E`. Each inequality `ℓx ≠ ℓ'x` is witnessed at one coordinate.
- A configuration `y` agreeing with `x` on a large ball has distinct points `ℓ̂y`, `ℓ ∈ supp r`, and the entry of
  `ψ_n(r)` at row `ℓ̂_0 y` and column `y` is `f_(ℓ_0)(ℓ_0x) = 1`.

(iii) **Onto `M_(2^|Q_n|)(F_2)`.**
- `P_t D_n(1_[x(e)=1]) P_t^(-1) = diag(1_[y(t)=1])`, since `x_(t^(-1)y)(e) = y(t)`. Products of these and their
  complements give every diagonal matrix unit.
- The flips `y ↦ y + 1_t`, the conjugates of `P_a`, act simply transitively on `Y_n`, so `P_g E_(yy) = E_(gy,y)` gives
  every matrix unit.

(iv) **Marked limit and expanders.**
- Let `F = F_2⟨t_s, t_a, t_p⟩` (`s ∈ S` symmetric), with `π: F → R` and `ρ_n = ψ_n∘π` on generators. Both are onto.
- For each `w ∈ F`, (i) gives `ρ_n(w) = ψ_n(π(w))` for large `n`. So by (ii) a word in the `e_ij(t)` is trivial in `G`
  iff it is trivial in `EL_3(M_(N_n)(F_2)) = SL_(3N_n)(F_2)` for large `n`, where `N_n = 2^|Q_n|`.
- `EL_3(F)` is Kazhdan (`elementary-groups-over-fg-rings-have-property-t`) and has both groups as quotients with
  compatible generators. So the Cayley graphs form expanders with a uniform spectral gap.

**Converse.** Marked limits of finite groups are LEF, and LEF passes to subgroups.

**Model tests.**
- `Δ = Z`: `Q_n = Z/n`, `Y_n = 2^(Z/n)`, and the models are `M_(2^n)(F_2)`.
- A non-LEF `Γ`, e.g. `BS(2,3)`: the converse shows no host exists. Consistently, `Δ` would have to be LEF.
- Finite `Δ` is excluded: then `N_n` is bounded and there is no infinite limit.

## 3. Classes with no infinite simple Kazhdan members

Claim `approximation-classes-without-simple-kazhdan-members`, direct route.
- Simplicity turns a single nontrivial homomorphism into an embedding, so residual versions reduce to the class itself.
- Amenable plus (T) is finite: amenability gives almost invariant unit vectors in `ℓ^2(G)`, (T) then gives an
  invariant one, and an invariant vector is constant.
- So residually finite, residually amenable and residually solvable groups contain no infinite simple Kazhdan group.
- **Firewall.** An RF input has a host (`rf-groups-embed-in-simple-kazhdan-lef-groups`), but the host is never RF. The
  natural statement for RF groups is the LEF one.

## 4. Above LEF: the cost of an envelope theorem

Claim `simple-kazhdan-envelope-theorems-force-non-lef-hosts`, route `...-proof`.
- **The witness.** `Γ_p` (`abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`) is finitely presented and
  amenable, and has a central `c_p ≠ 1` killed by every finite-dimensional unitary representation.
  - So `Γ_p` is not RF: a finite quotient separating `c_p` would have a faithful regular representation.
  - So it is not LEF: finitely presented LEF groups are RF (`finitely-presented-lef-groups-are-residually-finite`).
- **Covered classes.** Every class in row 3 of the table contains all amenable groups:
  - sofic, hyperlinear and weakly sofic groups: amenable ⇒ sofic;
  - linear sofic groups over any field: `n − #cycles(π) = rank(I − P_π)`, which lies between half the number of moved
    points and that number;
  - initially subamenable groups: by definition;
  - operator-MF groups: `amenable-implies-operator-mf`.
- **Conclusion.** Env_P forces a host containing `Γ_p`, which cannot be LEF. This generalizes
  `sofic-universal-envelope-forces-non-lef-simple-kazhdan` (sofic, witness `BS(2,3)`) to every class containing the
  amenable groups, including hyperlinear and operator-MF groups, where `BS(2,3)` is not known to help.
- **Open claims landed with Attempts:** `hyperlinear-groups-embed-in-simple-kazhdan-hyperlinear-groups`,
  `operator-mf-groups-embed-in-simple-kazhdan-mf-groups`. The sofic target is peer node
  `sofic-groups-embed-in-simple-kazhdan-sofic-groups`.

## 5. Firewalls respected
- `diag(a,a^(-1),1)` and `γ ↦ (γ,γ^(-1))` are not homomorphisms on noncommuting inputs. §2 uses only
  `ℓ ↦ diag(u_ℓ,1,1)` on `[L,L]`, through the identity displayed in the lamplighter route.
- LEF hosts contain only LEF groups, so none of the row-3 statements can be proved with them.
