# Binary fullness: chain audit, rank-deficient tower coverings, and a linear census design

Lane `gk3-binary-fullness`, 2026-09-14. User order: "let's do breakthroughs and fully solve Gottschalk".
Supports `rank-deficient-tower-coverings-decide-binary-cyclic-corner` and
`two-order-three-coset-ideals-never-contain-one`.

References: [CS] `research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md`;
[OS] `research/artifacts/brin-thompson-2v-obstruction-state-profile-2026-09-12.md`;
[H] `research/artifacts/brin-thompson-2v-gottschalk-host-2026-09-12.md`.

## 0. Directive and outcome

- **Audit (Section 1): the chain is valid.** "Full averaging idempotent ⇒ strict automaton" was re-derived at
  printed generality, step by step. Nothing in it proves too much: it can only fire on a nonsofic host, and the
  locally finite calibration host realizes the obstruction profile.
- **New certificate form (Section 2).** Fullness is equivalent to `1 = Σ_(j=1..r) a_j E_k b_j` for some `k` and
  some `r < 3^k`.
  With the left factors fixed this is linear over `F_2`, and with group-element left factors it is a covering of
  `δ_1` by functions invariant under `r < 3^k` conjugates of `C_3^k`.
- **First exclusion (Section 3).** Two order-three coset families never cover `δ_1`, in any group. So a coset
  certificate needs `k >= 2`.
- **Census (Section 4).** Designed as a linear peeling-plus-elimination search over Thompson's `V`. Its results are
  recorded in Section 5 when they land.
- **Decision.** None. No certificate, and no obstruction to fullness, is known for `V`, the unit group or `2V`.

## 1. Audit of the chain

### 1.1 The dynamical step
`stable-finiteness-failure-refutes-surjunctivity`: if `B A = I_n != A B` over `k[G]` with `k` finite, the linear
automaton of `A` on `(k^n)^G` is injective and not surjective. It is the contrapositive of the published
"surjunctive ⇒ stably finite" and carries its own proof. Checked: valid at `n = 1`, `k = F_2`.

### 1.2 From a corner solution to a one-sided inverse
`brin-thompson-2v-nonsurjunctive-from-averaging-fullness`: `c e b = 1` gives `d a = 1` with `a = e b`, `d = c`. If
`a d = 1` then `e = e (e b c) = e b c = 1`, false because `e` has three group elements in its support. Checked.
The argument uses only `e² = e` and `e != 1`, so it holds in every group algebra.

### 1.3 Theorem B ([CS] Section 2), re-derived
- `D(h) = Σ_i s_i h t_i` is a unit (`D(h) D(h^(-1)) = Σ_i s_i t_i = 1`), and it commutes with every ternary
  permutation unit `π_σ = Σ_i s_(σ i) t_i`: both products equal `Σ_j s_(σ j) h t_j`. So `[D(h)]` commutes with
  `[g]`, and `ψ`, `ψ'` are unital ring homomorphisms (Lemma 1.1).
- The `D^j(g)` commute pairwise: `D^(i)(g)` and `D^(j)(g)` with `i < j` differ by applying `D^i` to `g` and
  `D^(j-i)(g)`, which commute. `⟨g⟩` commutes with `D(C_3^k)` and meets it trivially, so `ψ(E_k) = E_(k+1)`:
  over `F_2`, the product of the averaging sums of two commuting subgroups meeting trivially is the averaging sum of
  their product.
- `F_2[C_3²] = F_2 × F_4^4`, with `f_K` primitive for the pair of characters with kernel `K`. `f_K e_(K_2) = f_K` iff
  `K = K_2`, so `ψ'(f) = f_(K_3) + f_(K_4)`.
- 4 ⇒ 5 needs an `M` in `GL_2(F_3)` moving `K_2`, `K_3`, `K_4` among themselves. The stabilizer of the line `K_1` acts
  transitively on the other three lines, so the three `f_K` inside `f` are equivalent in `T`.
- 6 ⇒ 2: iterating `N v + v + q = N v` and applying `F^k` gives `N d_k + v + x = N d_k`. `p >= N d_k` once
  `(3^k - 1)/2 >= N`. Checked line by line, in agreement with the PASS verdicts of `w4-vf-linear-b` and `w6-vf-chain`.

### 1.4 Scope for 2V
Theorem B is stated for `D`-stable subgroups of the Leavitt units containing `g` and the `π_M`. For `2V`, [H]
Proposition 2.1 transfers it using the baker unit. The Attempts entry of `brin-thompson-2v-nonsurjunctive` records
that transfer as on paper and awaiting verification, and I did not re-derive it. So Section 2 below applies to `2V`
exactly as far as [H] Proposition 2.1 does.

### 1.5 Model tests
- **Sofic hosts.** Any certificate makes `F_2[Γ]` not directly finite, which is impossible for sofic `Γ`
  (Elek–Szabó). So the chain can never fire on a sofic group, as it must not.
- **Calibration host.** `L_3 = ∪_k Sym(3^k)` satisfies the hypotheses of Theorem B, and its regular rank realizes
  the profile `s(p_k) = 3^(-k)` ([CS] Remark 2.2). Theorem B then correctly says `e` is not full there.
- **Finite control.** In `F_2[C_3²]`, `δ_1 = 1_(C_3²) + Σ_K 1_K` over the four subgroups of order three (value `5 = 1`
  at the identity, `1 + 1 = 0` on each `K \ {1}`, `1` minus itself elsewhere). This is a covering with `r = 4 > 3^1`,
  consistent with the regular rank `4/3 >= 1`. No covering with `r < 3` exists there (Section 3).

## 2. Rank-deficient tower coverings

**Proposition 2.1.** Let `Γ` be a Theorem B host and `A = F_2[Γ]`. Then `c e b = 1` is solvable iff for some
`k >= 1` and `r < 3^k` there are `a_j`, `b_j` in `A` with `Σ_(j=1..r) a_j E_k b_j = 1`.

*Proof.*
- If `c e b = 1`, take `k = r = 1`.
- Conversely, the row `R = (a_j E_k)_j` and the column `C = (E_k b_j)_j` satisfy `R C = 1`. So `A` is a direct
  summand of `(E_k A)^r`, and `u <= r p_k` in `V(A)`.
- Let `s` be a state with `x = s(v) > 0`. Then `s_T = x^(-1) s ∘ K_0(ι_T)` is a state of `T`, and `s' = s_T ∘ K_0(ψ')`
  is a state of `A` with `s'(v) = 2/3` ([CS] 4 ⇒ 5; [OS] Theorem 1.1(b)).
- The tower relations give `s'(p_k) = 3^(-k)` ([OS] Theorem 1.1(d)). So `1 <= r 3^(-k) < 1`, a contradiction.
- Hence every state vanishes on `v`, and [CS] Theorem B (4 ⇒ 1) gives `c e b = 1`. QED

**Coset form.** For group elements `a_j = x_j`, `x E_k b = (x E_k x^(-1)) (x b)`, and `E^(K) A` for
`K = x C_3^k x^(-1)` is the space of finitely supported functions constant on the sets `K w`. The certificate is
`δ_1 = Σ_(j=1..r) f_j` with `f_j` constant on the `K_j`-cosets `K_j w`. Equivalently, `A` is a direct summand of
`⊕_(j<=r) F_2[K_j \ Γ]`. This generalizes the permutation-module form of `w4-binary-cyclic`, which is `r = 1`.

**Remarks.**
- Once `k` and the left factors are fixed, the certificate is linear in the `b_j`. An infeasible bounded instance
  has a dual certificate: a function `λ` on the equation set with `λ(1) = 1` whose sum over every variable coset is `0`.
- Completeness is not claimed. A solution `c e b = 1` gives `k = 1`, `r = 1` with the general left factor `c`.
  Pushing it up the tower with `ψ` multiplies supports, so there is no guarantee that some coset certificate with
  group-element left factors and `r < 3^k` exists.
- A coset certificate lives in `F_2[L]` for `L = ⟨K_1, ..., K_r⟩`, which must therefore be nonsofic.

## 3. Two order-three coset families never cover

**Lemma 3.1.** For any group `G` and subgroups `K_1`, `K_2` of order three, `1` is not in
`e_(K_1) F_2[G] + e_(K_2) F_2[G]`.

*Proof.* See `two-order-three-coset-ideals-proof`. The covering is a `0/1` labelling `φ` of the three-regular graph
`B`: its vertices are the cosets `K_1 w`, `K_2 w` of `L = ⟨K_1, K_2⟩`, and its edges are the elements `w`. `φ`
agrees across every edge except the edge `1`. So the edge `1` is a bridge. `L` acts edge-transitively by right
multiplication, so every edge is a bridge, and `B` is a three-regular tree. It cannot be finite. If it is infinite,
both sides of the edge `1` are infinite, and one of them carries the value `1` on infinitely many cosets,
contradicting finite support. QED

**Consequence.** A coset certificate in Proposition 2.1 needs `k >= 2`. The first live level is `k = 2`, with two to
eight conjugates of `C_3² = ⟨g, D(g)⟩` translating the nine ternary cylinders.

## 4. Census design (linear, over Thompson's V)

- **Host.** `Γ = V`. It is `D`-stable and contains `g` and the `π_M`, so it is a Theorem B host. Elements are prefix
  code bijections, reduced to the minimal leaf pair.
- **Level.** `k = 2`, `K_1 = C_3²`, and `K_j = x_j C_3² x_j^(-1)` for `j = 2..r`, `r <= 8`. The conjugators are
  sampled from small elements outside the normalizer of `C_3²`, so that the `K_j` are not all equal.
- **Instance.** `L = ⟨K_1, ..., K_r⟩`, explored breadth first to a budget of `N` elements. The variables are the
  cosets `K_j w` meeting the ball. The equations are `Σ_(variable cosets ∋ w) φ = δ_1(w)` for every `w` in their union.
  The instance is exact: a solution is a certificate, and infeasibility means no certificate supported on cosets
  meeting the ball.
- **Solver.** Peel equations with one live variable (value forced: `0` except at `w = 1`). Then run dense Gaussian
  elimination over `F_2` on the remaining core, and output a solution or a dual vector.
- **Controls.**
  - Positive: `k = 1` with the four order-three subgroups of `C_3²` inside `V` (`r = 4`) must be feasible.
  - Negative: `r < 3^k` inside a finite subgroup, the finitary permutations of depth-two ternary cylinders, must be
    infeasible.
  - Section 3 predicts every `k = 1`, `r = 2` instance infeasible, which cross-checks the solver.
- **Checking.** Any feasible `r < 3^k` instance is re-verified by an independent product computation in the shared
  certificate checker `experiments/nonsofic-certificates/`, and lands only as OPEN, awaiting independent re-derivation.

## 5. Census results and where it stops

Pending at first landing. The exact gap is recorded here when the census lands.
