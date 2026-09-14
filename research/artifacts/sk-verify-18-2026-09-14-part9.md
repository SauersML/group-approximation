# sk-verify-18 part 9: character rigidity of the lamplighter hosts (2026-09-14)

Queue lines 21–22 (sk-lamplighter-characters, `research/artifacts/sk-lamplighter-characters-2026-09-14-part1.md` and `-part2.md`):
- `lamplighter-host-elementary-groups-are-character-rigid` (Theorem L), route `lamplighter-host-elementary-groups-character-rigid-proof`;
- `lamplighter-host-elementary-groups-have-trivial-irs`, route `lamplighter-host-elementary-groups-have-trivial-irs-proof`.

## Verdicts
- **Theorem L: PASS**, re-derived by hand. The only import is Larsen–Tiep through the reviewed Z-case Lemma 3 (`subshift-tower-unit-group-characters-are-constant`).
- **Trivial IRS: PASS**, conditional on Theorem L, `binary-el-simple-iff-minimal-topologically-free`, and the IRS principle already passed for the Z-case (sk-verify-8).
- One wording note (W1). No FAIL, no GAP.

## Re-derivation of Theorem L
**L1 (UHF stages).**
- The lamp translation u_κ maps the cylinder [w] to [w+κ], so u_κ e_{[w]} = e_{[w+κ]} u_κ.
- For E_{v,v′} = e_{[v]}u_{v−v′}: E_{v,v′}E_{w,w′} = e_{[v]}e_{[w+v−v′]}u_{v−w′} = δ_{v′w}E_{v,w′}, and Σ_v E_{v,v} = 1. So A_W ≅ M_{2^{|W|}}(F_2), with inclusions x ↦ x⊗I.
- L = ⋃ GL_3(A_{W_m}) ⊆ G, because transvections between different positions are root elements and those within one position are commutators.
- rank(h⊗I_s − I) = s·rank(h − I) ≥ s, which is the support bound.

**L2 (constancy).**
- τ(p_{Q_n}) is the trivial weight of χ|_{Q_n}.
- For nontrivial ρ, the Z-case Lemma 3 bound with α_h = 1/N_m tends to 0, so χ(h) = lim τ(p_{Q_n}) = τ(p_Q).

**L3 (generation).**
- d_δ = diag(u_δ,1,1) sends e_12(r) ↦ e_12(u_δr), e_13(r) ↦ e_13(u_δr), e_21(r) ↦ e_21(ru_δ⁻¹), e_31(r) ↦ e_31(ru_δ⁻¹), and fixes e_23, e_32. So it normalizes G.
- d e_12(1)d⁻¹ = e_12(u_δ), d⁻¹e_21(1)d = e_21(u_δ), and so on. Then [e_21(u_δ^{±1}), e_13(1)] = e_23(u_δ^{±1}) and [e_31(u_δ^{±1}), e_12(1)] = e_32(u_δ^{±1}).
- The set {r : e_ij(r) ∈ Q for all i ≠ j} is a subring. It contains R_K and every u_δ^{±1}, hence every u_{(δ,f)} = u_f u_δ, so it is all of R.

**L4 (central trivial part).**
- τ(p_{A′_m}) = (1 + (|A′_m|−1)c)/|A′_m| → c. A′ = e_23(LC) is fixed by d_δ, so it lies in L and in every d_δLd_δ⁻¹.
- p_L ≤ p_{A′} with equal traces and a faithful τ gives p_L = p_{A′} = p_{dLd⁻¹}.
- The fixed-vector identity holds on generating subgroups, so p_{A′} is central, and χ = c + (1−c)χ_2.

**L5 (Bessel).**
- **(a)** Nontriviality over a small V passes to every nonempty clopen V′ ⊆ V. A nonzero coefficient f_ξ is constant on ξV, so it is nonzero on ξV′. (The artifact's "and back" is the converse direction.)
- **(b), (c)** The noncommuting root and the tower groups use only topological freeness of Λ_0 and the rev4 product formula.
- **(d)** Far-apart points exist, because a small set is infinite and B_{2w}-orbits are finite.
- **(e) Conjugating into the UHF algebra.**
  - Invariance of the Bernoulli measure μ gives rank e_{aV_k} = 2^{|W|}μ(V_k) for every a ∈ B_w, so matrix units ε′ in A_W connect them.
  - ww̄ = (1−e) + Σ_{k,a} ε_{a,e}ε′_{e,e}ε_{e,a} = (1−e) + e = 1. The cross terms vanish because aV_k ⊆ U gives e_{V_k}(1 − e_{a⁻¹U}) = 0.
  - w ε′ w⁻¹ = ε, and w fixes (1−e)R_K(1−e).
  - So H_{V_k} ⊆ GL_3(F_0) ⊆ GL_3(wR_Kw⁻¹) = wLw⁻¹ =: M. The complement 1 − e_{B_wV_k} lies in F_0, and M ⊆ G by L1.
- **(f)** For k ≠ l, ⟨v_k,v_l⟩ = ψ(g⁻¹ygy⁻¹) with y = x_lx_k. H_{V_k} and H_{V_l} commute, so this equals ψ((g⁻¹x_lg·x_l)(g⁻¹x_kg·x_k)). The product is a nontrivial element of M, since H_{V_k} ∩ H_{V_l} = 1 and x_k does not commute with g.
- **(g)** ⟨ξ,v_k⟩ is the conjugate of ψ(g), and Bessel gives K|ψ(g)|² ≤ 1 for every K.

**§4 (c_M = c).** A‴ = e_23((1−e)LC(Ω,F_2)) lies in L, and in M because w fixes (1−e)R_K(1−e). It is an increasing union of finite groups of unbounded order, so computing τ(p_{A‴}) through L and through M gives c_M = c. Hence χ_2 vanishes on M∖1, and L5 applies.

**Firewalls re-checked.**
- Finite Δ fails: Ω is finite.
- Over F_q with q > 2, GL_N is not quasisimple.
- The invariant measure enters only in (e).
- No amenability, finite generation or property (T) of Δ is used anywhere.

**W1 (wording).** Lemma L5's hypothesis is stated for every unit w with wLw⁻¹ ⊆ G, but §4 checks it only for the w built in (e). The artifact already notes that this suffices. Say in the route that L5 is applied to the unit built from g.

## Trivial IRS
- Minimality: orbits contain x + ⊕_Δ F_2, which is dense.
- Topological freeness: the fixed-point equation.
- `binary-el-simple-iff-minimal-topologically-free` makes G_Δ simple, with no finite-generation input. It is infinite, so it has no proper finite-index subgroup.
- With Theorem L, the IRS principle (`research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md` §§1–2, as passed for the Z-case) gives IRS(G_Δ) = {(1−b)δ_{1} + bδ_{G_Δ}}.
