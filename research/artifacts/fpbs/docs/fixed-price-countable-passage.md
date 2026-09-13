# Fixed price: from finitely generated to countable groups

## Status

Research artifact for `fpbs-fixed-price-countable-from-finitely-generated`.
That node stays **OPEN**. This file was written on September 12, 2026.

What is proved here:

1. **Theorem B (unconditional).** A countably infinite group Γ has fixed price
   iff (i) C(Γ) = ∞, or (ii) C(s_Γ) = C(Γ) < ∞ and every free action of Γ has
   finite cost. Assume C(s_Γ) = C(Γ) < ∞ and some free action b has C(b) = ∞.
   Then b satisfies PC(b) < C(b). This is a positive answer to Tucker-Drob's
   Question 7.6.
2. **Proposition A (unconditional).** For every p.m.p. action a,
   PC(a) ≤ sup_F inf_{Δ ⊇ F f.g.} C(a|Δ).
3. **Under H** ("every infinite finitely generated group has fixed price"):
   - Corollary C: every free action satisfies C(Γ) ≤ PC(a) ≤ PC(s_Γ) ≤ c*(Γ).
   - Corollary D: fixed price one when c*(Γ) = 1.
   - Theorem E: H + (L) + (U) implies fixed price. (L) is a vanishing
     subgroup-defect condition and (U) is finiteness of all free-action costs.
4. **Proposition F (unconditional).** (U) holds when Γ has an infinite finitely
   generated subgroup that is normal, commensurated, or the base of a Gaboriau
   chain.
5. **The obstruction (§6).** H fixes only the costs of subgroup orbit
   relations. Cost and pseudocost are governed by intermediate relations,
   which H does not see. §6 records the exact shape of any counterexample to
   the passage.
6. **Test cases (§7).** They include an unconditional fixed price 2 for the
   non-free, locally free, infinitely generated kernel Γ_∞ of an ascending HNN
   extension of F_2. Step (4) of that proof uses standard ℓ²-dimension facts
   from Lück's monograph. Those facts were not re-read from source in this
   session.

Not proved: the passage itself.

## 1. Verified tools and their scopes

**Conventions.**
- Γ is a countably infinite group and a is a p.m.p. action on (X, μ).
- E_a is the orbit relation and C(a) = C_μ(E_a).
- FR is the set of free actions and s_Γ is the Bernoulli shift.
- C(Γ) = inf over free a of C(a). This infimum is attained (Coût Prop VI.21).
- a|Δ is the restriction of a to a subgroup Δ.
- a ≼ b means a is weakly contained in b.

Sources read in full text for this artifact:
- [TD] R. Tucker-Drob, *Weak equivalence and non-classifiability of measure
  preserving actions*, [arXiv:1211.6395](https://arxiv.org/abs/1211.6395),
  TeX source. The published numbering is used: Cost is §6 and Questions is
  §7. TeX labels are given in brackets.
- [AW] M. Abért and B. Weiss, *Bernoulli actions are weakly contained in any
  free action*, [arXiv:1103.1063](https://arxiv.org/abs/1103.1063).
- [BK] P. Burton and A. S. Kechris, *Weak containment of measure preserving
  group actions*, [arXiv:1611.07921](https://arxiv.org/abs/1611.07921), §7.1.
  This section quotes Kechris, *Global aspects of ergodic group actions*,
  Cor. 10.14.
- [G00] D. Gaboriau, *Coût des relations d'équivalence et des groupes*,
  Invent. Math. 139 (2000).
- [GL] D. Gaboriau, *Around the orbit equivalence theory, measure equivalence,
  cost and ℓ² Betti numbers*, lecture notes, version of October 3, 2025,
  [PDF](https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf).

| Tool | Statement | Scope |
|---|---|---|
| [AW] main theorem | every free p.m.p. action weakly contains every Bernoulli action | all countably infinite Γ |
| Kechris Cor. 10.14, quoted as [BK] Thm 6.1 | a ≼ b, both free ⇒ C(a) ≥ C(b) | **finitely generated Γ only** |
| [TD] Def 6.6 [def:pseudo] | PC(E) = inf over exhaustions E_n ↗ E of liminf C(E_n); PC ≤ C; PC ≥ 1 if E is aperiodic | all |
| [TD] Lemma 6.2 [lem:open] | a ∈ A_{F,r} iff some E with E_{a\|⟨F⟩} ⊆ E ⊆ E_a has C(E) < r, iff the same holds with E ⊆ E_{a\|⟨Q⟩} for some finite Q | all countable Γ |
| [TD] Thm 6.4 [thm:KecOpen] | A_{F,r} ∩ FR lies in the interior of A_{F,r} | all |
| [TD] Prop 6.7 [prop:unions] | for an exhaustion, C(E) ≤ liminf C(E_n) if C(E) < ∞ or E is treeable; lim C(E_n) = 1 ⇒ C(E) = 1 | all |
| [TD] Cor 6.8 [cor:PC=C] | PC = C if C < ∞ or E is treeable; PC = 1 iff C = 1 | all |
| [TD] Lemma 6.14 [lem:exhaust] | an exhaustion bound r is equivalent to b ∈ A_{F,r+ε} for all F and ε, and to a sandwiched exhaustion E_{b\|⟨Q_n⟩} ⊆ E_n ⊆ E_{b\|⟨Q_{n+1}⟩} | all |
| [TD] Cor 6.19 [cor:PCdef] | PC(a) ≤ r iff a ∈ A_{F,r+ε} for every finite F and every ε > 0 | all |
| [TD] Cor 6.20 [cor:AFrPC] | a free and a ≼ b ⇒ PC(b) ≤ PC(a) | all |
| [TD] Cor 6.22 [cor:weakcon] | a free and a ≼ b ⇒ C(b) ≤ C(a) if C(b) < ∞ or E_b is treeable; C(a) = 1 ⇒ C(b) = 1 | all |
| [TD] Cor 6.24 [cor:FP1] | fixed price 1 ⇔ C(s_Γ) = 1 | all |
| [TD] Prop 6.26(1) [prop:analogue] | if C(Γ) < ∞, then for every free b and every exhaustion of E_b, liminf C(E_n) ≥ C(Γ); so PC(b) ≥ C(Γ) | all |
| [TD] Q 7.6 [Q:unions] | can PC < C? Equivalently, can sup C(E_n) < ∞ while C(∪E_n) = ∞? | open |
| [TD] Q 7.7, 7.8 | does one free action of infinite (resp. finite) cost force C(s_Γ) = ∞ (resp. < ∞)? | open |
| [G00] Lemme V.3 | let ψ : A → B be a partial isomorphism and T = (ψ⁻¹ R\|_B ψ) ∩ R\|_A; if T has infinite classes, Φ ∨ {ψ} and Φ ∨ {ψ restricted to a set of measure ≤ ε} generate the same relation | all |
| [G00] Critères VI.24(2),(4) | Λ ◁ Γ infinite with fixed price ⇒ C(Γ) ≤ C(Λ); a Gaboriau chain over a fixed-price Γ_1 ⇒ C(Γ) ≤ inf C(Γ_n) | all |
| [G00] VI.26(a) | an infinite normal subgroup of fixed price 1 ⇒ fixed price 1 | all |
| [G00] Prop VI.21 | a treeing of a free action realizes C(Γ); C(Γ) is attained; if every free action is treeable, Γ has fixed price | all |
| [G00] Corollaire 1 | F_p is treeable with fixed price p | |
| [GL] Thm 2.45 | if Γ_{n+1} = ⟨Γ_n, γ_{n+1}⟩ and γ_{n+1}⁻¹Γ_nγ_{n+1} ∩ Γ_n is infinite, every free action has C(R_Γ) ≤ C(R_{Γ_0}) | all |
| [GL] Cor 2.48, 2.49 | Λ infinite normal, or commensurated ⇒ C(R_Γ) ≤ C(R_Λ) for every free action | all |
| [GL] Prop 2.53, Cor 2.52(1) | Λ × Δ with both factors infinite has C_* = 1; it has fixed price 1 if Λ contains a fixed-price-1 subgroup | |
| [GL] Prop 2.57, Cor 2.40(c) | cost is semicontinuous along finite-cost unions; unions with costs tending to 1 have cost 1 | all |
| [GL] Thm 2.64 | C_*(Γ) − 1 ≥ β_1(Γ) − β_0(Γ) | all countable |
| [GL] Q 2.62, 2.63, 2.65, 2.66 | fixed price; direct products; cost versus β_1; strict semicontinuity of unions | open |

**Where the non-finitely-generated case needs care.**
- Monotonicity of cost under weak containment is proved only for finitely
  generated Γ.
  - For arbitrary countable Γ, only pseudocost is monotone ([TD] Cor 6.20).
  - The cost version needs C(b) < ∞ or treeability ([TD] Cor 6.22).
  - Whether s_Γ attains the maximal cost is [TD] Q 7.7.
- Semicontinuity along exhaustions is known only for finite-cost or treeable
  unions. A strict example is [TD] Q 7.6, which is the same as [GL] Q 2.66.
- A finitely generated group has cost at most its number of generators. Groups
  that are not finitely generated have no such bound.

## 2. Pseudocost through subgroups (unconditional)

For an m.p. action a of Γ and a finite F ⊆ Γ, set

    p_F(a) = inf { C(E) : E_{a|⟨F⟩} ⊆ E ⊆ E_a },
    q_F(a) = inf { C(a|Δ) : Δ finitely generated, F ⊆ Δ ⊆ Γ }.

Both quantities are nondecreasing in F. The relation E_{a|Δ} is admissible for
p_F, so p_F(a) ≤ q_F(a).

**Lemma 2.1.** PC(a) = sup_F p_F(a).

*Proof.* By [TD] Lemma 6.2(1), a ∈ A_{F,r} iff p_F(a) < r. By [TD] Cor 6.19,
PC(a) ≤ r iff p_F(a) < r + ε for all F and ε. That holds iff
sup_F p_F(a) ≤ r. ∎

**Proposition A.** For every m.p. action a of a countable group Γ,

    PC(a) ≤ σ(a) := sup_F q_F(a).

*Proof.* Combine Lemma 2.1 with p_F ≤ q_F. ∎

In σ, each F gets its own finitely generated subgroup, and these subgroups
need not form a chain. Any finitely generated exhaustion Γ_n ↗ Γ gives
σ(a) ≤ liminf_n C(a|Γ_n), since each F lies in Γ_n for large n. So
Proposition A sharpens the chain bound recorded in the claim. In the
F_(4^n) × (Z/2)^n example the chain values diverge while σ = 1 (§7, T2).

## 3. The unconditional criterion

**Theorem B.** Let Γ be countably infinite. Then Γ has fixed price iff either

- (i) C(Γ) = ∞, or
- (ii) C(Γ) < ∞, C(s_Γ) = C(Γ), and every free action of Γ has finite cost.

Assume C(s_Γ) = C(Γ) < ∞, and let b be a free action with C(b) = ∞. Then
PC(b) ≤ C(Γ) < C(b). This answers [TD] Q 7.6 positively by the orbit relation
of a free action of Γ, and E_b is not treeable by [TD] Cor 6.8(2).

*Proof.* Under (i), every free action has cost ∞.

Assume (ii) and let b be free.
1. s_Γ is free because Γ is infinite, and [AW] gives s_Γ ≼ b.
2. [TD] Cor 6.20 gives PC(b) ≤ PC(s_Γ) ≤ C(s_Γ) = C(Γ).
3. [TD] Prop 6.26(1) gives PC(b) ≥ C(Γ), so PC(b) = C(Γ).
4. C(b) < ∞, so [TD] Cor 6.8(1) gives C(b) = PC(b) = C(Γ).

Conversely, suppose Γ has fixed price with value c. If c = ∞ then (i) holds.
Otherwise C(Γ) = c = C(s_Γ) and all costs are finite, so (ii) holds. The final
assertion is steps 1–3, which use only C(s_Γ) = C(Γ) < ∞. ∎

**Corollary B′.** Assume Γ has a free action of finite cost, and PC(b) = C(b)
for every free action b of Γ. Then Γ has fixed price iff C(s_Γ) = C(Γ).

Theorem B sharpens the two remaining requirements stated in §9 of
`fixed-price-conditional-traffic.md`.
- Vanishing defect is exactly C(s_Γ) = C(Γ).
- Once that holds, a mixed finite/infinite sector is exactly a free-action
  instance of [TD] Q 7.6.

For finitely generated Γ, finiteness in (ii) is automatic. Kechris' Cor. 10.14
makes s_Γ the maximal-cost action, and Theorem B becomes the statement that s_Γ
attains the minimum. For other countable groups, Theorem B shows that nothing
beyond "s_Γ attains the minimum" and the exclusion of free-action instances of
Q 7.6 is needed.
