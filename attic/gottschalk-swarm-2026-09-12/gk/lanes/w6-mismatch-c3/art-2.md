
## 3. The firewall

Notation from `research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md`:
`ε_- = 2(1 - [z])`, `S_- = ε_- F_3[G]`, and the reflection ideal `J_omega` of its Section 1 (the subscript
there is the stage index, unrelated to the weight `ω`).

**Theorem 3.** Let `Γ_0 <= G` contain `z`. Suppose `u Γ_0 u^(-1) ⊆ H^ω_≤` or `u Γ_0 u^(-1) ⊆ H^ω_≥` for some
`u in G` and some weight `ω`. Then `ε_- F_3[Γ_0]` has a nonzero weakly finite image, i.e.
`1 ∉ J_omega(ε_- F_3[Γ_0])`. So no finite certificate for `ternary-anti-central-summand-has-no-weakly-finite-image`
has all its group elements (entries of the pairs, of their defects, and of the ideal multipliers) in `Γ_0`.

*Proof.*
- Conjugation by `u` is a ring automorphism of `F_3[G]` fixing `[z]`, so take `u = 1`.
- **Case `≤`.** `φ` of Corollary 2 extends linearly to a unital ring map `Φ : F_3[Γ_0] -> Q` with
  `Φ([z]) = -1`. Then `Φ(ε_-) = 2·2 = 1` in characteristic three, so `Φ` restricts to a unital ring map
  `ε_- F_3[Γ_0] -> Q` (`ε_-` is the unit of that corner).
- `Q` is weakly finite, so Theorem 1(b) of that artifact gives `Φ(J_omega) = 0`, while `Φ(1) = 1 != 0`.
- **Case `≥`.** The same, with `g -> φ(g*)` into `Q^op`.
- A certificate with all group elements in `Γ_0` is a derivation of `1 in J_omega` inside the subring
  `ε_- F_3[Γ_0]`, since the stages use only the displayed identities. QED

**Relation to the sofic firewall.** By Corollary 2(b) every such `Γ_0` is sofic, so Theorem 3 also follows
from `linear-sofic-group-algebra-is-stably-finite`, since the anti-central summand is a nonzero corner of a
stably finite algebra. What is new is the placement: the configurations below lie in locally residually
finite subgroups, and `φ` is an explicit model.

**Relation to `w6-mismatch-c2`.** `research/artifacts/mismatched-factor-graph-of-groups-firewall-2026-09-12.md`
(Corollary 2.2) realizes `a = T_(0,1)` and `c = T_(1,00)` over `F_2` in a weakly finite rank model of a graph of
locally finite groups. That model keeps `rk(D) != 0`, but only relations inside its vertex groups hold. Theorem 3
is complementary: every relation of the actual subgroup holds, but `D -> 0` (Remark 3.2).
- `ac` also has infinite order over `F_3`. The formulas in the proof of that artifact's Proposition 2.1(1) for
  `ac - 1` on the points `q_n`, `r_m` have all coefficients `+1`, so they hold over `F_3`.
- Modulo lower levels, `(ac - 1)^2` maps the level-`l` pair to the level-`(l-1)` pair by the matrix `[[1,1],[0,1]]`.
  So `ac - 1` is nilpotent on each level space, with unbounded index.
- Suppose `(ac)^m = 1`, and let `3^k` be the largest power of three dividing `m`. Then `U = 1 + (ac - 1)^(3^k)`
  is unipotent on each level space with `U^(m / 3^k) = 1`. Its order is prime to three, so `U = 1`. Then
  `(ac - 1)^(3^k) = 0` on every level space, a contradiction. So `ac` has infinite order.
- So `H^1_≤` over `F_3` holds a non-locally-finite subgroup together with all its relations, and it still has a
  weakly finite model with `z -> -1`.

**What `H^1_≤` contains.**
- `z`, the sign group `E` (units `Σ ε_μ s_μ t_μ`), the level part `∪_n Sym({0,1}^n)` of `V`, and all of
  `(R^1_0)^x = ∪_n GL_(2^n)(K)` (Section 2, Remarks).
- Every transvection `T_(σ,κ)(λ)` with `|σ| <= |κ|`:
  - all level root elements at every depth, in particular `T_(0,1)(λ)`, `T_(1,0)(λ)`, and
    `w_0 = T_(0,1)(1) T_(1,0)(-1) T_(0,1)(1) = s_0 t_1 - s_1 t_0`, with `w_0^2 = z`;
  - the depth-decreasing `T_(1,00)(λ)`, `T_(0,11)(λ)`, `T_(1,000)(λ)`, and so on.
- The mismatched pair and every product of these.

**Task 1: the mismatched pair.** Put `A = s_0 t_1` and `B = s_1 t_00`, so `T_(0,1) = 1 + A` and
`T_(1,00) = 1 + B`. In `R`:
- `A^2 = 0` and `B^2 = 0`;
- `AB = s_0 t_00`, `BA = s_1 t_10`, `ABA = s_0 t_10` and `BAB = s_1 t_000`;
- `(AB)^n = s_0 t_(0^(n+1))` and `(BA)^n = s_1 t_(1 0^n)`, nonzero for every `n` (the contracting partial maps
  `0^(n+1) y -> 0y` and `1 0^n y -> 1y`);
- `T_(0,1) T_(1,00) = 1 + s_0 t_1 + s_1 t_00 + s_0 t_00`.

Every term has degree `<= 0`. So `N_A = φ(A)` and `N_B = φ(B)` satisfy all of these in the weakly finite
algebra `Q`, where `z -> -1`. Any identity derived in `W` from group relations among elements of `H^1_≤`
(root squares, commutators with level roots at both depths, conjugation by `E` and level `V`) holds in this
model. So that computation, confined to those elements, cannot produce a one-sided invertible matrix with
nonzero defect, nor a contradiction with `z = -1`.

**Remark 3.2 (the two-root defect).** In the three-leaf frame, `D = N_23 N_12` in `F_3[G]` evaluates to
`e_23 e_12 = 0` in `M_3(R) ≅ R`. Suppose `x_12(1), x_23(1) in Γ_0` and `u Γ_0 u^(-1) ⊆ H^ω_≤`, and put
`Φ([g]) = φ(u g u^(-1))`. Then `Φ(D) = φ(u e_23 u^(-1)) φ(u e_12 u^(-1)) = φ(u e_23 e_12 u^(-1)) = 0`, and the
same holds on the `≥` side. With the code `(0,10,11)`, `e_12 = s_0 t_10` and `e_23 = s_10 t_11` both
lie in `R^1_≤`.
- So these models violate form (iv) (`D_rho != 0`) of that artifact's Theorem 3. They give no firewall for the
  defect form `ternary-weakly-finite-representations-kill-two-root-defect`.
- They do show that the implication "`D` killed ⟹ trivial" (its Theorem 2) cannot be run inside `H^1_≤`:
  `φ` kills `D` and is injective.
- Whether `H^1_≤` has a weakly finite representation with `z -> -1` and `D != 0` is not decided here.

## 4. What an obstruction must contain

**Lemma 4.1 (Kraft).** Let `g in V` be given by prefix codes `(c_i) -> (d_i)`, so `g = Σ_i s_(d_i) t_(c_i)`.
Let `p in (0,1)` solve `p^a + p^b = 1` and let `μ_ω` be the Bernoulli measure with `μ_ω[w] = p^(ω(w))`.
These are equivalent:
- (i) `g in R^ω_≤`; (ii) `g in R^ω_≥`;
- (iii) `ω(d_i) = ω(c_i)` for all `i`;
- (iv) `g` preserves `μ_ω`.

*Proof.*
- (iii) ⟹ (i), (ii): every term is weight-level.
- (i) ⟹ (iii). The `R_n`-component of `g` is `Σ s_(d_i) t_(c_i)` over the `i` with `c(d_i) - c(c_i) = n`. It
  is nonzero when that index set is nonempty, because `π` of it sends the constant function `1` to the
  indicator of `∪ [d_i]`. So (i) forces `ω(d_i) <= ω(c_i)` for all `i`. The codes partition `X`, so
  `Σ_i p^(ω(c_i)) = 1 = Σ_i p^(ω(d_i))`, and `p < 1` gives `p^(ω(d_i)) >= p^(ω(c_i))` termwise. So equality
  holds termwise. (ii) ⟹ (iii) is the same with the inequalities reversed.
- (iii) ⟺ (iv): `g` maps `[c_i v]` onto `[d_i v]`, and `μ_ω[d_i v] / μ_ω[c_i v] = p^(ω(d_i) - ω(c_i))`. QED

**Consequences.**
- For `θ = 1`, `V ∩ R^1_≤` is the level part of `V`, which is locally finite.
- A non-level element such as `x_0` (`00 -> 0`, `01 -> 10`, `1 -> 11`) lies in no `H^ω_≤` and no `H^ω_≥`: its
  pieces change weight by `-a`, `0` and `+b`.
- `G = ⟨V, 1 + s_00 t_01⟩` (`leavitt-prime-field-units-generated-by-v-and-one-transvection`), and
  `1 + s_00 t_01` lies in `R^1_0`. So the group elements of a certificate must generate a subgroup that no
  conjugation puts inside any `H^ω_≤` or `H^ω_≥`. Elements of `V` that are weight-level for no `ω` are the obvious
  source. Transvection sets such as the four-element set below are another.

**Depth vectors.** For `λ != 0` put `v(T_(σ,κ)(λ)) = c(σ) - c(κ) in Z^2`. The element `λ s_σ t_κ` is
homogeneous of degree `v` and nonzero, so with `a = 1`, `b = θ`: `T in H^θ_≤` iff `v_0 + θ v_1 <= 0`, and
`T in H^θ_≥` iff `v_0 + θ v_1 >= 0`.

| transvection | `v` | in `H^θ_≤` iff | in `H^θ_≥` iff |
|---|---|---|---|
| `T_(0,1)` | `(1,-1)` | `θ >= 1` | `θ <= 1` |
| `T_(1,0)` | `(-1,1)` | `θ <= 1` | `θ >= 1` |
| `T_(1,00)` | `(-2,1)` | `θ <= 2` | `θ >= 2` |
| `T_(00,1)` | `(2,-1)` | `θ >= 2` | `θ <= 2` |
| `T_(0,10)` | `(0,-1)` | every `θ` | no `θ` |
| `T_(10,0)` | `(0,1)` | no `θ` | every `θ` |

- `{T_(0,1), T_(1,00)} ⊆ H^θ_≤` for `1 <= θ <= 2`.
- `{T_(0,1), T_(1,00), T_(00,1)} ⊆ H^2_≤`, the golden-ratio weight (`p + p^2 = 1`).
- `{T_(0,1), T_(1,0), T_(00,1)} ⊆ H^1_≥`.
- `{T_(0,1), T_(1,0), T_(1,00), T_(00,1)}` lies in no `H^θ_≤` and no `H^θ_≥`: the level pair forces `θ = 1`,
  and at `θ = 1` the last two have degrees `-1` and `+1`.
- **Escaping without conjugation is not enough.** `{T_(10,0), T_(0,10)}` lies in no `H^θ_±`. But the element
  `u in V` with `0 -> 00`, `10 -> 01`, `11 -> 1` gives `u T_(10,0) u^(-1) = T_(01,00)` and
  `u T_(0,10) u^(-1) = T_(00,01)`, both in `R^1_0`.

**Open.**
- Is `⟨E, level V, T_(0,1), T_(1,0), T_(1,00), T_(00,1)⟩` conjugate into some `H^ω_±`, or sofic for another
  reason?
- For elements of `V`, slopes at fixed points are conjugation invariants
  (`research/artifacts/thompson-v-rank-models-torsion-spectra-2026-09-12.md`, Section 3). An invariant of that
  kind for units of `R` that detects the depth vectors above would turn Section 4 into a criterion. None is
  proved here.
- Does `H^1_≤` carry a weakly finite representation with `z -> -1` and `D != 0`?
