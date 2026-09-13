# Fixed price: from finitely generated to countable groups

## Status

Research artifact for `fpbs-fixed-price-countable-from-finitely-generated`.
That node stays **OPEN**. This file was written on September 12, 2026.

What is proved here:

1. **Theorem B (unconditional).** A countably infinite group Γ has fixed price
   iff (i) C(Γ) = ∞, or (ii) C(s_Γ) = C(Γ) < ∞ and every free action of Γ has
   finite cost. Assume C(s_Γ) = C(Γ) < ∞ and some free action b has C(b) = ∞.
   Then PC(b) < C(b), which answers Tucker-Drob's Question 7.6 positively.
2. **Proposition A (unconditional).** Every p.m.p. action a of Γ satisfies
   PC(a) ≤ σ(a) := sup_F inf { C(a|Δ) : Δ ⊇ F finitely generated }.
   σ(a) is also the least value of liminf_n C(a|Γ_n) over finitely generated
   exhaustions Γ_n ↗ Γ.
3. **Under H** ("every infinite finitely generated group has fixed price").
   Only the finitely generated subgroups of Γ are used.
   - Corollary C: if C(Γ) < ∞, every free action satisfies
     C(Γ) ≤ PC(a) ≤ PC(s_Γ) ≤ c*(Γ).
   - Corollary D: fixed price one when c*(Γ) = 1.
   - Theorem E: H + (L) + (U) implies fixed price. (L) is the vanishing
     subgroup-defect condition c*(Γ) ≤ C(Γ). (U) is finiteness of all
     free-action costs.
4. **Proposition F (unconditional).** (U) holds when Γ has an infinite finitely
   generated subgroup that is normal, commensurated, or the base of a Gaboriau
   chain.
5. **The obstruction (§6).** H fixes only the costs of subgroup orbit
   relations. Cost and pseudocost are governed by arbitrary intermediate
   relations, which H does not see. §6 records the exact shape of any
   counterexample to the passage.
6. **Test cases (§7).** They include fixed price 2 for the kernel Γ_∞ of an
   ascending HNN extension of F_2. Γ_∞ is locally free, infinitely generated
   and not free. Step (4) of that proof uses standard ℓ²-dimension facts from
   Lück's monograph. Those facts were not re-read from source in this session.

Not proved: the passage itself.

## 1. Verified tools and their scopes

**Conventions.**
- Γ is a countably infinite group and a is a p.m.p. action on (X, μ).
- E_a is the orbit relation and C(a) = C_μ(E_a).
- FR is the set of free actions and s_Γ is the Bernoulli shift.
- C(Γ) = inf over free a of C(a). This infimum is attained ([G00] Prop VI.21).
- a|Δ is the restriction of a to a subgroup Δ.
- a ≼ b means a is weakly contained in b.
- [GL] writes C_* and C^* for the infimum and supremum of free-action costs.

Sources read in full text for this artifact:
- [TD] R. Tucker-Drob, *Shift-minimal groups, fixed price 1, and the unique
  trace property*, [arXiv:1211.6395](https://arxiv.org/abs/1211.6395), TeX
  source. §6 is Cost and §7 is Questions. TeX labels are given in brackets.
- [AW] M. Abért and B. Weiss, *Bernoulli actions are weakly contained in any
  free action*, [arXiv:1103.1063](https://arxiv.org/abs/1103.1063).
- [BK] P. Burton and A. S. Kechris, *Weak containment of measure preserving
  group actions*, [arXiv:1611.07921](https://arxiv.org/abs/1611.07921), §7.1
  (Cost). This section quotes Kechris, *Global aspects of ergodic group
  actions*, Cor. 10.14.
- [G00] D. Gaboriau, *Coût des relations d'équivalence et des groupes*,
  Invent. Math. 139 (2000).
- [GL] D. Gaboriau, *Around the orbit equivalence theory, measure equivalence,
  cost and ℓ² Betti numbers*, lecture notes, version of October 3, 2025,
  [PDF](https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf).

| Tool | Statement | Scope |
|---|---|---|
| [AW] main theorem | every free p.m.p. action weakly contains every Bernoulli action | countably infinite Γ |
| Kechris Cor. 10.14, quoted in [BK] §7.1 | a ≼ b, both free ⇒ C(a) ≥ C(b) | **finitely generated Γ only** |
| [TD] Cor 6.5 (Kechris) | cost is upper semicontinuous at free actions | **infinite finitely generated Γ only** |
| [TD] Lemma 6.2 [lem:open] | for any p.m.p. a: a ∈ A_{F,r} iff some E with E_{a\|⟨F⟩} ⊆ E ⊆ E_a has C(E) < r, iff the same holds with E ⊆ E_{a\|⟨Q⟩} for some finite Q | countable Γ |
| [TD] Thm 6.4 [thm:KecOpen] | A_{F,r} ∩ FR lies in the interior of A_{F,r} | infinite countable Γ |
| [TD] Def 6.6, Cor 6.17 | PC(E) = inf over exhaustions E_n ↗ E of liminf C(E_n), and the infimum is attained; PC ≤ C; PC ≥ 1 if E is aperiodic | all |
| [TD] Prop 6.7 [prop:unions] | for an exhaustion: C(E) ≤ liminf C(E_n) if (1) C(E) < ∞ or (2) E is treeable; (3) lim C(E_n) = 1 ⇒ C(E) = 1 | all |
| [TD] Cor 6.8 [cor:PC=C] | (1) PC = C if C < ∞; (2) PC = C if E is treeable; (3) PC = 1 iff C = 1 | all |
| [TD] Cor 6.11, 6.13 | a treeable E of infinite cost has C(E_n) → ∞ along every exhaustion; Takahasi: ascending chains of bounded-rank subgroups of a free group stabilize | all |
| [TD] Lemma 6.14 [lem:exhaust] | for any p.m.p. b, the following are equivalent: some exhaustion of E_b has limsup C(E_n) ≤ r; b ∈ A_{F,r+ε} for all finite F and ε > 0; some sandwiched exhaustion E_{b\|⟨Q_n⟩} ⊆ E_n ⊆ E_{b\|⟨Q_{n+1}⟩} has limsup C(E_n) ≤ r | all |
| [TD] Cor 6.19 [cor:PCdef] | PC(a) ≤ r iff a ∈ A_{F,r+ε} for every finite F and every ε > 0 | all |
| [TD] Cor 6.20 [cor:AFrPC] | a free and a ≼ b ⇒ PC(b) ≤ PC(a) | countable Γ |
| [TD] Cor 6.22 [cor:weakcon] | a free and a ≼ b ⇒ C(b) ≤ C(a) if C(b) < ∞ or E_b is treeable; C(a) = 1 ⇒ C(b) = 1 | countably infinite Γ |
| [TD] Cor 6.24 [cor:FP1] | fixed price 1 ⇔ C(s_Γ) = 1 | countable Γ |
| [TD] Prop 6.26(1) [prop:analogue] | if C(Γ) < ∞, then for every free b and every exhaustion of E_b, liminf C(E_n) ≥ C(Γ); so PC(b) ≥ C(Γ) | countably infinite Γ |
| [TD] Q 7.6 [Q:unions] | can PC < C? Equivalently, can sup C(E_n) < ∞ while C(∪E_n) = ∞? A positive instance is not treeable and has β_1 + 1 < C | open |
| [TD] Q 7.7, 7.8 | does one free action of infinite (resp. finite) cost force C(s_Γ) = ∞ (resp. < ∞)? Positive answers to both would exclude groups with free actions of both finite and infinite cost | open |
| [G00] Lemme V.3 | R an (SP1) relation with graphing Φ; ψ : A → B a partial isomorphism; T = (ψ⁻¹·R\|_B·ψ) ∩ R\|_A with infinite classes ⇒ for every ε > 0, R_{Φ∨{ψ}} is generated by Φ ∨ {ψ\|_ε}, of cost ≤ C(Φ) + ε, where ψ\|_ε restricts ψ to a Borel set of measure ≤ ε meeting almost every T-class | all |
| [G00] Corollaire 1, Prop VI.9 | F_n (n finite) and F_∞ are treeable with fixed price n and ∞ | |
| [G00] Prop VI.21 | a treeing of a free action realizes C(Γ); C(Γ) is attained; the proof gives C(a × b) ≤ C(a) for free a; if every free action is treeable, Γ has fixed price | all |
| [G00] Prop VI.23 | Γ_1 has an element of infinite order and Γ_2 is infinite ⇒ Γ_1 × Γ_2 has fixed price 1 | |
| [G00] Critères VI.24(2),(4) | Λ ◁ Γ infinite with fixed price ⇒ C(Γ) ≤ C(Λ); a Gaboriau chain over a fixed-price Γ_1 ⇒ C(Γ) ≤ inf C(Γ_n) | all |
| [G00] Lemme VI.25, VI.26(a) | increasing unions of cost-1 relations with infinite classes have cost 1; an infinite normal subgroup of fixed price 1 ⇒ fixed price 1 | all |
| [GL] Thm 2.45 | Γ_{n+1} = ⟨Γ_n, γ_{n+1}⟩ with γ_{n+1}⁻¹Γ_nγ_{n+1} ∩ Γ_n infinite ⇒ every free action has C(R_Γ) ≤ C(R_{Γ_0}) | all |
| [GL] Cor 2.48, 2.49 | Λ infinite normal, or N infinite commensurated ⇒ every free action has C(R_Γ) ≤ C(R_Λ) (resp. C(R_N)) | all |
| [GL] Cor 2.52(1), Prop 2.53 | Λ × Δ with both factors infinite has C_* = 1; it has fixed price 1 if Λ contains a fixed-price-1 subgroup | |
| [GL] Cor 2.40(c), Prop 2.57 | increasing infinite relations with C(R_i) → 1 have union of cost 1; a finite-cost increasing union has C(∪R_n) ≤ liminf C(R_n) | all |
| [GL] Cor 2.58, 2.59 | Bernoulli shifts restrict to Bernoulli shifts; C_*(SL(2,Q)) = 1, and the Nota credits Mellick with fixed price 1 | |
| [GL] Thm 2.64 | C_*(Γ) − 1 ≥ β_1(Γ) − β_0(Γ) | countable Γ |
| [GL] Q 2.62, 2.63, 2.65, 2.66 | fixed price; direct products; cost versus β_1; can C(∪R_n) > liminf C(R_n)? | open |

**Where the non-finitely-generated case needs care.**
- **Monotonicity of cost under weak containment** is proved only for finitely
  generated Γ (Kechris Cor. 10.14, [TD] Cor 6.5).
  - For arbitrary countable Γ, only pseudocost is monotone ([TD] Cor 6.20).
  - The cost version needs C(b) < ∞ or treeability ([TD] Cor 6.22).
  - Whether s_Γ attains the maximal cost is [TD] Q 7.7.
- **Semicontinuity along exhaustions** is known only for finite-cost or
  treeable unions. A strict example is exactly a positive answer to [TD]
  Q 7.6. That is the same as [GL] Q 2.66: by [GL] Prop 2.57 a strict example
  must have infinite union cost.
- **Cost bounds.** A finitely generated group has cost at most its number of
  generators. Groups that are not finitely generated have no such bound, so a
  priori they can have a free action of infinite cost.

## 2. Pseudocost through subgroups (unconditional)

For a p.m.p. action a of Γ and a finite F ⊆ Γ, set

    p_F(a) = inf { C(E) : E_{a|⟨F⟩} ⊆ E ⊆ E_a },
    q_F(a) = inf { C(a|Δ) : Δ finitely generated, F ⊆ Δ ⊆ Γ }.

Both quantities are nondecreasing in F. The relation E_{a|Δ} is admissible for
p_F, so p_F(a) ≤ q_F(a).

**Lemma 2.1.** PC(a) = sup_F p_F(a).

*Proof.* By [TD] Lemma 6.2, a ∈ A_{F,r} iff p_F(a) < r. By [TD] Cor 6.19,
PC(a) ≤ r iff p_F(a) < r + ε for all F and ε > 0. That holds iff
sup_F p_F(a) ≤ r. ∎

**Proposition A.** For every p.m.p. action a of a countable group Γ,

    PC(a) ≤ σ(a) := sup_F q_F(a) = min_{(Γ_n)} liminf_n C(a|Γ_n),

where the minimum runs over finitely generated exhaustions Γ_n ↗ Γ.

*Proof.* The inequality combines Lemma 2.1 with p_F ≤ q_F.

For the identity, let (Γ_n) be a finitely generated exhaustion. Each F lies in
Γ_n for large n, so q_F(a) ≤ liminf_n C(a|Γ_n). Hence σ(a) is at most every
such liminf. If σ(a) = ∞, every exhaustion attains the minimum.

Otherwise fix a finite exhaustion (F_n) of Γ and ε_n → 0.
1. Choose a finitely generated Δ_0 ⊇ F_0 with C(a|Δ_0) < σ(a) + ε_0.
2. Given Δ_n with a finite generating set S_n, choose a finitely generated
   Δ_{n+1} ⊇ F_{n+1} ∪ S_n with
   C(a|Δ_{n+1}) < q_{F_{n+1} ∪ S_n}(a) + ε_{n+1} ≤ σ(a) + ε_{n+1}.
3. The Δ_n form a finitely generated exhaustion with
   limsup C(a|Δ_n) ≤ σ(a). ∎

Proposition A is therefore the exhaustion bound recorded in the claim,
optimized over the choice of exhaustion. The choice matters. For the chain
Γ_n = F_(4^n) × (Z/2)^n, the values C(a|Γ_n) diverge, while σ(a) = 1 for every
free action (§7, T2).

## 3. The unconditional criterion

**Theorem B.** Let Γ be countably infinite. Then Γ has fixed price iff either

- (i) C(Γ) = ∞, or
- (ii) C(Γ) < ∞, C(s_Γ) = C(Γ), and every free action of Γ has finite cost.

Assume C(s_Γ) = C(Γ) < ∞, and let b be a free action with C(b) = ∞. Then
PC(b) ≤ C(Γ) < C(b). So the orbit relation of a free action of Γ answers [TD]
Q 7.6 positively, and E_b is not treeable by [TD] Cor 6.8(2).

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

For finitely generated Γ, the finiteness in (ii) is automatic. Kechris' Cor.
10.14 makes s_Γ the maximal-cost action, and Theorem B becomes the statement
that s_Γ attains the minimum. For other countable groups, Theorem B shows that
nothing is needed beyond "s_Γ attains the minimum" and the exclusion of
free-action instances of Q 7.6.

## 4. Under H: subgroup costs

Throughout this section, assume H for the infinite finitely generated
subgroups of Γ. For such a subgroup Δ, write c(Δ) for its fixed price.

**Locally finite groups.** A locally finite Γ is a directed union of finite
groups, so it is amenable. It therefore has fixed price 1 ([GL] Thm 2.20,
Ornstein–Weiss).

For the rest of this section, assume Γ is not locally finite. Fix a finite
F_0 ⊆ Γ with ⟨F_0⟩ infinite, so every subgroup containing F_0 is infinite.

**Definitions.** For finite F ⊆ Γ,

    c_F(Γ) = inf { c(Δ) : Δ ≤ Γ infinite, finitely generated, F ⊆ Δ },
    c*(Γ)  = sup_F c_F(Γ).

**Lemma 4.1 (H).** Every free action a of Γ satisfies q_F(a) = c_F(Γ) for
F ⊇ F_0. Hence σ(a) = c*(Γ).

*Proof.* The restriction a|Δ is free, so C(a|Δ) = c(Δ) under H for every
infinite finitely generated Δ. For F ⊇ F_0, every Δ ⊇ F is infinite. Both q_F
and c_F are nondecreasing in F, so their suprema may be taken over F ⊇ F_0. ∎

**Corollary C (H).** Every free action a of Γ satisfies
PC(a) ≤ PC(s_Γ) ≤ c*(Γ). If C(Γ) < ∞, then also C(Γ) ≤ PC(a).

*Proof.* [AW] and [TD] Cor 6.20 give PC(a) ≤ PC(s_Γ). Proposition A and
Lemma 4.1 give PC(s_Γ) ≤ σ(s_Γ) = c*. [TD] Prop 6.26(1) gives C(Γ) ≤ PC(a). ∎

**Corollary D (H).** If c*(Γ) = 1, then Γ has fixed price 1.

*Proof.* A free action a is aperiodic. [TD] Def 6.6 and Corollary C give
1 ≤ PC(a) ≤ c* = 1, and [TD] Cor 6.8(3) gives C(a) = 1. ∎

When the subgroups whose costs tend to 1 already form a chain, Corollary D is
[GL] Cor 2.40(c) or [G00] Lemme VI.25. Corollary D asks only that c_F → 1; the
chain selection in Proposition A supplies the chain.

**Theorem E (H).** Assume

- (L) c*(Γ) ≤ C(Γ), and
- (U) every free action of Γ has finite cost.

Then Γ has fixed price C(Γ) = c*(Γ).

*Proof.* (U) gives C(Γ) < ∞. For every free a, Corollary C and (L) give
C(Γ) ≤ PC(a) ≤ c* ≤ C(Γ). Then (U) and [TD] Cor 6.8(1) give
C(a) = PC(a) = C(Γ). ∎

Theorem E does not claim that (L) is necessary. Theorem B needs only
PC(s_Γ) ≤ C(Γ), and c* is merely an upper bound for PC(s_Γ).

**Defect formulation (H).** Assume C(Γ) < ∞ and c* < ∞. For a free a and
F ⊇ F_0, set D_F(a) = c_F − p_F(a). It is ≥ 0 because p_F ≤ q_F = c_F. Both
terms are nondecreasing and bounded, so D_F(a) → c* − PC(a) by Lemma 2.1.
- By [TD] Prop 6.26(1), every free action has asymptotic defect at most
  c* − C(Γ).
- A free action a_0 of cost C(Γ) exists ([G00] Prop VI.21) and attains this
  bound, by [TD] Cor 6.8(1).
- By Corollary C, s_Γ has the least asymptotic defect.

Assume (U). By Theorem B, Γ has fixed price iff every free action has the same
asymptotic defect c* − C(Γ), i.e. iff s_Γ attains the largest defect. H fixes
the subgroup term c_F. It says nothing about the intermediate-relation term
p_F.

## 5. Groups with a finitely generated anchor (unconditional)

**Proposition F.** Suppose Γ contains an infinite subgroup Λ generated by d
elements, such that one of the following holds:
- Λ is normal;
- Λ is commensurated;
- Λ = Γ_0 is the base of a chain Γ_0 ≤ Γ_1 ≤ ⋯ with ∪_n Γ_n = Γ,
  Γ_{n+1} = ⟨Γ_n, γ_{n+1}⟩, and γ_{n+1}⁻¹Γ_nγ_{n+1} ∩ Γ_n infinite.

Then every free action of Γ has cost ≤ d, so (U) holds and C(Γ) ≤ d. Hence Γ
has fixed price iff C(s_Γ) = C(Γ), iff PC(s_Γ) = C(Γ).

*Proof.*
1. Let a be free. In the three cases, [GL] Cor 2.48, Cor 2.49 and Thm 2.45
   give C(a) ≤ C(a|Λ).
2. The d generators of Λ form a graphing of E_{a|Λ} of cost d.
3. Theorem B gives the first equivalence.
4. C(s_Γ) < ∞, so C(s_Γ) = PC(s_Γ) by [TD] Cor 6.8(1). ∎

Under H, Proposition F leaves shape (A) of §6 as the only possible
obstruction.

## 6. The obstruction

H fixes the costs C(a|Δ) = c(Δ) of subgroup orbit relations. By Lemma 4.1,
these values determine σ(a) = c* for all free actions at once.

Whether Γ has fixed price is decided by C(Γ), PC(s_Γ), and whether all free
costs are finite (Theorem B). Pseudocost is an infimum over arbitrary
intermediate relations E_{a|⟨F⟩} ⊆ E ⊆ E_a ([TD] Lemma 6.2, Lemma 6.14,
Cor 6.19). Those relations need not be orbit relations of subgroups, and H
does not constrain them.

Unconditionally, PC(Γ) = C(Γ) when C(Γ) < ∞ ([TD] Prop 6.26(1)), and s_Γ has
the largest pseudocost among free actions ([AW] and [TD] Cor 6.20). Say Γ has
*fixed pseudocost* if all free actions have the same pseudocost. By Theorem B
and [TD] Cor 6.8(1), a group with C(Γ) < ∞ has fixed price iff it has fixed
pseudocost and satisfies (U).

**Theorem G (H; the shape of a counterexample).** Assume H, and let Γ be a
countably infinite group without fixed price. Then Γ is neither finitely
generated nor locally finite. Moreover C(Γ) < ∞, and

    1 + β_1(Γ) ≤ C(Γ) ≤ PC(s_Γ) ≤ c*(Γ).

Exactly one of the following holds.

**(A) No fixed pseudocost:** C(Γ) < PC(s_Γ) ≤ c*(Γ). Then:
- (L) fails;
- s_Γ is not treeable;
- no free action weakly contained in s_Γ has pseudocost C(Γ);
- a free action a_0 of cost C(Γ) has p_F(a_0) ≤ C(Γ) < c_F for all large F.
  Near-optimal intermediate relations for a_0 are therefore not subgroup
  orbit relations.

**(B) Fixed pseudocost C(Γ), with an infinite cost:** PC(b) = C(Γ) for every
free b, and some free b has C(b) = ∞. Then:
- E_b answers [TD] Q 7.6 and [GL] Q 2.66 positively;
- E_b is not treeable;
- β_1(E_b) + 1 < C(E_b), by the remark after [TD] Q 7.6 (citing Gaboriau
  2002, 5.13 and 3.23). This answers the relation part of [GL] Q 2.65;
- Γ has none of the subgroups of Proposition F.

*Proof.*
1. H excludes finitely generated Γ. Locally finite groups have fixed price 1
   (§4). If C(Γ) = ∞, then Γ has fixed price ∞. So C(Γ) < ∞.
2. The first inequality is [GL] Thm 2.64, with β_0(Γ) = 0 because Γ is
   infinite. The other two inequalities are Corollary C.
3. Suppose PC(s_Γ) > C(Γ).
   - (L) fails because c* ≥ PC(s_Γ).
   - If s_Γ were treeable, [TD] Cor 6.8(2) and [G00] Prop VI.21 would give
     PC(s_Γ) = C(s_Γ) = C(Γ).
   - If a free a ≼ s_Γ had PC(a) = C(Γ), [TD] Cor 6.20 would give
     PC(s_Γ) ≤ C(Γ).
   - a_0 exists by [G00] Prop VI.21, and PC(a_0) = C(Γ) by [TD] Cor 6.8(1).
     So p_F(a_0) ≤ C(Γ) by Lemma 2.1, while c_F ↑ c* > C(Γ).
4. Suppose PC(s_Γ) = C(Γ). By Corollary C, every free b has PC(b) = C(Γ).
   - If all free costs were finite, [TD] Cor 6.8(1) would give fixed price.
     So some free b has C(b) = ∞, and PC(b) < C(b) answers [TD] Q 7.6.
   - Along an exhaustion attaining PC(b) ([TD] Cor 6.17),
     liminf C(E_n) < C(E_b). This answers [GL] Q 2.66.
   - Non-treeability is [TD] Cor 6.8(2), and the β_1 inequality is the cited
     remark.
   - Proposition F would give (U). ∎

**Remarks.**
- **Shape (B)** is exactly a free-action instance of [TD] Q 7.6 at a group of
  finite cost. After Q 7.6, Tucker-Drob notes that a free-action instance need
  not refute fixed price, because the group might have C(Γ) = ∞. Shape (B) is
  the complementary case C(Γ) < ∞, where an instance does refute it.
  - A positive answer to [TD] Q 7.7 forces C(s_Γ) = ∞ in shape (B).
  - A positive answer to Q 7.8 forces C(s_Γ) < ∞, because a_0 has finite
    cost. Then the infinite-cost b is not s_Γ.
  - Positive answers to both would exclude shape (B).
- **Shape (A)** is invisible to any argument that passes only through
  subgroups. It is compatible with every value H assigns.
  - By [TD] Cor 6.19, excluding it is the statement
    s_Γ ∈ ∩_{F,ε} A_{F, C(Γ)+ε}.
  - The action a_0 lies in that intersection, and s_Γ ≼ a_0 ([AW]).
  - But the openness of A_{F,r} ∩ FR ([TD] Thm 6.4) moves membership only
    along a ≼ b, from a to b, here from s_Γ to a_0. It never moves it from a_0
    down to s_Γ.
- **Locally free groups.** Their finitely generated subgroups are free, with
  fixed price equal to the rank ([G00] Corollaire 1). So H holds for them
  unconditionally, and §4–§6 apply with no hypothesis. For locally free Γ, the
  passage is therefore exactly the fixed price problem for Γ itself. A
  counterexample there would be an unconditional group without fixed price
  ([GL] Q 2.62).

## 7. Test cases

**T1. F_∞.** [G00] Prop VI.9 gives C(F_∞) = ∞ and fixed price, which is case
(i) of Theorem B. Also c* = ∞. Let F = {x_1, …, x_n} be part of a basis, and
let Δ ⊇ F be finitely generated. The map Δ → F_∞^{ab} → Z^n, onto the
coordinates of x_1, …, x_n, is surjective. So rank Δ ≥ n, and c_F ≥ n.

**T2. Direct sums.** Let Γ = ⊕_{i∈N} G_i with every G_i nontrivial.
- If every G_i is locally finite, then Γ is locally finite and has fixed
  price 1.
- If some G_i has an element of infinite order, then
  Γ = G_i × ⊕_{j≠i} G_j with both factors infinite. [G00] Prop VI.23 gives
  fixed price 1 unconditionally.
- *Under H*, suppose infinitely many G_i are not locally finite (for instance,
  all are nonamenable). Given a finite F, choose n with
  F ⊆ P_n := G_1 × ⋯ × G_n and P_n not locally finite.
  - Let Δ_1 ≤ P_n be infinite, finitely generated and contain F.
  - Let Δ_2 ≤ ⊕_{j>n} G_j be infinite and finitely generated.
  - By [GL] Prop 2.53, C_*(Δ_1 × Δ_2) = 1. So c(Δ_1 × Δ_2) = 1 under H.
  - Hence c* = 1, and Corollary D gives fixed price 1.
- Without H, the case where every G_i is torsion and some G_i is infinite is
  an instance of [GL] Q 2.63. The remark there says it "can be done" when a
  factor contains arbitrarily large finite subgroups, as ⊕_{j≠i} G_j does. No
  proof is given in [GL], and none was checked here.

**T3. The chain F_(4^n) × (Z/2)^n.** Its union Γ = F_∞ × ⊕_N Z/2 has fixed
price 1 by [G00] VI.26(a), since ⊕_N Z/2 is an infinite amenable normal
subgroup. The chain values 1 + (4^n − 1)/2^n diverge.

The claim's treeing computation works for any k and M. It gives
F_k × (Z/2)^M fixed price 1 + (k − 1)/2^M. A finite F lies in
F_k × (Z/2)^{M'} for large k and every large M'. Hence σ(a) = 1 = C(Γ) for
every free action a. The looseness of the recorded bound comes from the choice
of exhaustion, not from H.

**T4. SL(2, Q).** [GL] Cor 2.59 gives C_*(SL(2, Q)) = 1. The Nota after it
credits Mellick with fixed price 1. Mellick's paper was not re-read here.

**T5. A locally free, non-free group of fixed price 2.** Let
M = ⟨a, b, t | tat⁻¹ = aba⁻¹, tbt⁻¹ = b²⟩, and let Γ_∞ = ker(M → Z), t ↦ 1.

1. *Structure.*
   - Fold the petals of aba⁻¹ and b². The resulting folded core graph has 3
     vertices and 4 edges, so ⟨aba⁻¹, b²⟩ ≤ F_2 = ⟨a, b⟩ is a proper subgroup
     of rank 2.
   - Since F_2 is Hopfian, φ(a) = aba⁻¹, φ(b) = b² defines an injective,
     non-surjective endomorphism, and M is its ascending HNN extension.
   - By the normal form t^{-p}wt^q (w ∈ F_2), Γ_∞ = ∪_n H_n with
     H_n = t^{-n}F_2t^n ≅ F_2. Also H_n ⊊ H_{n+1}, because
     H_0 = t⁻¹φ(F_2)t ⊊ t⁻¹F_2t = H_1.
   - Hence Γ_∞ is locally free and not finitely generated.
2. *Chain.* Put A = t⁻¹at and B = t⁻¹bt, so H_1 = ⟨A, B⟩, a = ABA⁻¹ and
   b = B².
   - The group ⟨H_0, A⟩ contains B = A⁻¹aA, so it equals H_1.
   - A⁻¹H_0A contains B, hence B² = b ∈ H_0. So A⁻¹H_0A ∩ H_0 ⊇ ⟨b⟩ is
     infinite.
   - Conjugating by t^{-n} gives the chain condition at every stage.
3. *Upper bound.* [GL] Thm 2.45 over Γ_0 = H_0 ≅ F_2 shows that every free
   action has cost ≤ 2.
4. *Lower bound: β_1^{(2)}(Γ_∞) = 1.*
   - Let V = N(Γ_∞). For H_n free of rank 2, H_1(H_n; V) is the kernel of the
     boundary V² → V and has dimension 1.
   - On 1-chains, H_0 → H_1 acts by the Fox matrix of (ABA⁻¹, B²) in (A, B):
     (v_1, v_2) ↦ (v_1(1 − ABA⁻¹), v_1A + v_2(1 + B)).
   - This map is injective. If g has infinite order and v(1 ∓ g) = 0, then
     the ℓ²-vector vδ_e has constant modulus on the infinite cosets of ⟨g⟩, so
     it vanishes.
   - So each H_1(H_n; V) → H_1(H_{n+1}; V) is injective, and
     H_1(Γ_∞; V) = colim_n H_1(H_n; V) has dimension 1.
   - Inputs: induction and colimit properties of dim_{N(G)}, and homology
     commuting with directed unions (Lück, *L²-invariants*, Ch. 6). They are
     standard, but were **not re-read from source** here.
   - [GL] Thm 2.64 gives C_*(Γ_∞) ≥ 1 + β_1 − β_0 = 2.
5. *Conclusions.* Γ_∞ has fixed price 2, modulo the inputs of step 4.
   - It is not free. If it were, it would be F_∞, and [G00] Prop VI.9 would
     give cost ∞. Alternatively, by Takahasi ([TD] Cor 6.13), a free group has
     no strictly ascending chain of rank-2 subgroups.
   - Its finitely generated subgroups are free, so c_F is unconditional. If F
     contains a basis of H_n, every Δ ⊇ F is nonabelian free, so c_F = 2.
     Hence c* = 2.
   - (U) holds by Proposition F, and (L) by step 4, in agreement with
     Theorem E.

## 8. What remains

Group by group, the passage is equivalent to excluding shapes (A) and (B) of
Theorem G. H excludes neither.
- Excluding (B) at groups of finite cost is a special case of [TD] Q 7.6.
- Excluding (A) needs a way to transfer intermediate-relation cost bounds
  from a_0 down to s_Γ. No source read here supplies one.

The node stays open.
