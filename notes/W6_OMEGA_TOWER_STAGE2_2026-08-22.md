# W6 stage 2: building the `ωₘ` tower

Design memo for the concrete construction that inhabits
`Higman.Omega.Tower` and `Higman.Omega.TowerClosure`
(`GroupApproximation/Higman/OmegaTower.lean`).  Stage 1 of that file is
landed: the interface, the easy half of Mikaelian's computation
`F₃ ∩ W_B = A_{ωₘ B}`, and the reduction of `Omega.OmegaInput` to two named
obligations.  This memo is the plan for those two.

Source: V. Mikaelian, *A modified proof for Higman's embedding theorem*,
arXiv:1908.10153v8, §4 (last part of Theorem 4.4), with §2.4--2.5 for the free
constructions and §3 for the benign calculus.  Every in-repo name below was
grep-verified against the working tree on 2026-08-22; file:line is given once
per name.

---

## 0.  The single most important structural fact

**There are two towers, not one, and they do different jobs.**

* **Ω′, the slim tower**, is built over the rank-two free group `⟨b, c⟩`
  itself.  Its purpose is that we possess *the full list of defining
  relations*, so a Britton normal-form analysis can be run in it.  The paper
  says this in as many words: the advantage of the slim group is that it is an
  extension of `⟨b, c⟩` by three nested HNN extensions.
* **Ω, the fat tower**, is built over `K` and `M` --- benign witnesses --- and
  is the one that is finitely presented, hence the one in which `W_B` can be
  benign.

**Ω′ is not finitely presented, and cannot be.**  Its first stage centralizes

    B₀ₘ = ⟨bᵢ : i < 0 or i ≥ m⟩ ,

and the rows are a free basis of the row subgroup (`Row.basisHom_injective`,
`Higman/RowBasis.lean:187`), so `B₀ₘ` is free of countably infinite rank ---
*not* finitely generated.  `Higman.isFinitelyPresented_centHNN`
(`Higman/HNNCentralizer.lean:151`) requires `L.FG` and therefore does not
apply.  That is exactly why Mikaelian introduces `K` and `P` at all: `P ≤ K`
is *finitely generated* with `⟨b,c⟩ ∩ P = B₀ₘ`, which is the statement that
`B₀ₘ` is benign in `⟨b,c⟩`.  Same story one level up for `L` and `R`.

So do not try to discharge `TowerClosure.benign` in Ω′, and do not try to
discharge `TowerClosure.descent` in Ω directly.  The two obligations live in
different groups and are joined by Mikaelian's Lemma 2.4 (§4 below).

---

## 1.  The two towers, stage by stage

Notation as in `OmegaTower.lean`: `ℰ_m = blockSet m` (sequences supported on
`[0, m)`), `b_f = bElt f`, `a_f = aElt f`, and `g, h, k` a second copy of the
coding with `hᵢ = h^{kⁱ}`, `h_β = ∏ᵢ hᵢ^{β i}`, `g_β = g^{h_β}`.

| stage | slim (Ω′) | fat (Ω) | centralized / associated subgroup |
|---|---|---|---|
| 0 | `⟨b, c⟩` | `K`, f.p., with f.g. `P`, `⟨b,c⟩ ∩ P = B₀ₘ` | --- |
| 1 | `Σ′ = ⟨b,c⟩ ∗_{B₀ₘ} (g,h,k)` | `Σ = K ∗_P (g,h,k)` | `B₀ₘ` resp. `P`, **centralized**, three stable letters |
| 2 | `Π′ = Σ′ ∗_L a` | `Π = M ∗_R a`, `M` f.p. with f.g. `R`, `Σ ∩ R = L` | `L = ⟨g_β b_β⁻¹ : β ∈ ℰ_m⟩` resp. `R`, **centralized** |
| 3 | `Ω′ = Π′ ∗_ρ r` | `Ω = Π ∗_ρ r` | `F₃ = ⟨a,b,c⟩`, associated to itself by `ρ` |

with `ρ` the `m`-shift automorphism `a, b, c ↦ a, b^{c^m}, c`, which is
`Seq.shiftEquiv ^ m` (`Higman/ShiftOperation.lean:148`), i.e.
`(⇑Seq.shiftAut)^[m]` on elements.

Three points that the briefing had wrong and that cost real effort to pin, all
now confirmed against the source:

1. **`∗_P` is a multiple HNN extension, not an amalgam.**  §2.4 defines
   `G ∗_{φ₁,φ₂,…}(t₁,t₂,…)` as the HNN extension with several stable letters.
   `Σ = K ∗_P (g,h,k)` therefore means: adjoin `g`, `h`, `k`, each inducing
   the identity on `P`, i.e. each **centralizing** `P`.  Consequence: every
   stage of both towers is an HNN extension, `Higman.CentHNN` covers stages 1
   and 2 verbatim, and **no amalgam appears anywhere in the `ωₘ` tower**.
   `Higman/AmalgamPushout.lean` and
   `Algebra/PushoutITorsionFree.isPowerTorsionFree_pushoutI_of_nonempty`
   (`:449`) are therefore *not* needed on this lane; neither is
   `Higman.CoprodTorsion.isPowerTorsionFree_coprod`
   (`Higman/CoprodTorsion.lean:86`).
2. **The base omits `a`.**  `a` re-enters at stage 2 as the stable letter
   centralizing `L`.  It has to: the relation the whole argument turns on is
   that `a` commutes with `g_β b_β⁻¹`, and in a base containing both they do
   not commute.  So `emb : F₃ →* Ω` being injective is a *conclusion* (Britton
   at stage 2), which is why it is a field of `Omega.Tower` rather than a
   hypothesis-free construction.
3. **`ρ` moves only `a, b, c`, not `g, h, k`, and fixes `a`.**  Hence `r`
   commutes with `a`.  The source's worked example (`m = 3`: conjugating
   `a^{b₀⁷b₁²b₂⁴}` by `r` gives `a^{b₃⁷b₄²b₅⁴}`) settles it.

---

## 2.  Discharging `Omega.Tower`'s three relations

These are cheap once the tower is built, and none of them is Britton.

* **`commute_row`** (`gen β` commutes with `rowElt i` for `i ∉ [0,m)`).  Each
  of `g, h, k` centralizes `B₀ₘ` by the stage-1 defining relation, which is
  `Higman.conj_eq_self_of_mem` (`Higman/HNNCentralizer.lean:55`):
  `t⁻¹ * of l * t = of l` for `l ∈ L`.  Push it up two levels along
  `HNNExtension.of` and induct over words in `g, h, k` with
  `FreeGroup.induction_on`.  `rowElt i ∈ B₀ₘ` for `i ∉ [0,m)` is
  `Subgroup.subset_closure`.  *`OmegaTowerStages.lean` proves this half.*
* **`conj_gen`** (`(gen β)⁻¹ · a · gen β = a_β` for `β ∈ ℰ_m`).  Same lemma one
  level up: `a` centralizes `L`, and `g_β b_β⁻¹ ∈ L` is
  `Subgroup.subset_closure`.  Unwinding `[a, g_β b_β⁻¹] = 1` gives
  `a^{g_β} = a^{b_β} = a_β`, which is three lines of `group`.
* **`conj_stable`** (`r⁻¹ · emb x · r = emb (shiftAut^[m] x)`).  The stage-3
  defining relation, `HNNExtension.equiv_eq_conj` /
  `equiv_symm_eq_conj` (the two forms `Higman/HNNDescent.lean:198,204` uses),
  plus `⇑(shiftEquiv ^ m) = (⇑shiftAut)^[m]` by induction on `m`
  (`pow_succ` + `MulAut.mul_apply`).

**The one real obstacle to even *defining* stage 3** is that its associated
subgroup is `emb.range` and its isomorphism is `ρ` transported along `emb`,
which needs `MulEquiv.ofInjective emb hemb` --- so stage 3's *data* depends on
stage 2's Britton theorem.  Parameterize on `hemb : Function.Injective emb`
and build `ρ` as
`((MulEquiv.ofInjective emb hemb).symm.trans (shiftEquiv ^ m : MulAut F₃)).trans
(MulEquiv.ofInjective emb hemb)`.  Note `shiftEquiv ^ m` needs the ascription
to `MulAut F₃`: `MulAut` is a plain `def`, so instance search will not find
`Group (F₃ ≃* F₃)` on its own.

---

## 3.  Discharging `TowerClosure.benign`

`Omega.benignTF_W_of_gen` (`OmegaTower.lean:570`) already reduces this to

> `Ω` is finitely presented, `Ω` is torsion-free, and
> `⟨g_β : β ∈ B ∩ ℰ_m⟩` is benign in `Ω`.

### 3a.  Finite presentation of Ω

Four HNN stages (three stable letters at stage 1, one each at stages 2 and 3),
each over a finitely generated associated subgroup:

* stages 1 and 2: `Higman.isFinitelyPresented_centHNN`
  (`Higman/HNNCentralizer.lean:151`), hypotheses
  `[Group.IsFinitelyPresented K]` and `L.FG`.  The pushed-up subgroup stays
  finitely generated by `Higman.fg_map` (`Higman/Benign.lean:58`).
* stage 3: `GroupApproximation.HNNFinitePresentation.isFinitelyPresented_hnnExtension`
  (`Algebra/HNNFinitePresentation.lean:220`), hypotheses
  `[Group.IsFinitelyPresented G] [Group.FG A]`, `φ` explicit.  Here `A = F₃`,
  finitely generated.

Finite generation of `P` and `R` is *given*, being the definition of the
benign witnesses for `B₀ₘ` and for `L`.

### 3b.  Torsion-freeness of Ω

`GroupApproximation.HNNBritton.isPowerTorsionFree_hnn`
(`GroupTheory/HNNBrittonCyclic.lean:330`), signature
`(φ : A ≃* B) (hG : IsPowerTorsionFree G) : IsPowerTorsionFree (HNNExtension G A B φ)`,
applied four times.  It is unconditional, so the only input is
torsion-freeness of `K` and of `M`, which is what `BenignTF` witnesses carry
(`Higman.TorsionFreeBenignWitness`, `Higman/BenignTorsionFree.lean`).

### 3c.  The two benignness inputs

**(i) `B₀ₘ` is benign in `⟨b,c⟩`.**  The source states the general form: for
fixed `k ≤ l`, `⟨bᵢ : i < k or i ≥ l⟩` is benign in the rank-two free group.
This is the same shape as `Higman.Row.comap_Lsub`
(`Higman/RowSubgroup.lean:335`), which computes `Lsub.comap of = Row` in the
shift extension `Gam` --- a collecting argument over a finitely generated
subgroup of a finitely presented HNN extension.  It is a self-contained
sub-task and a good candidate to hand to a second agent.

**(ii) `L = Z_{ℰ_m} = ⟨z_β : β ∈ ℰ_m⟩`, `z_β = g_β b_β⁻¹`, is benign in `Σ`.**
This is the source's Example 3.12, and it is an induction on `m` inside the
free group `⟨b₀,…,b_{m-1}, g, h₀,…,h_{m-1}⟩` of rank `2m+1`:

* base: `Z_{ℰ_0} = ⟨g_{(0)} b_{(0)}⁻¹⟩ = ⟨g⟩`, benign because finitely
  generated --- `Higman.benignTF_of_fg` (`Higman/BenignTorsionFree.lean:50`);
* step: `Z_{ℰ_m} = ⟨Z_{ℰ_{m-1}}, V_{ℰ_m}⟩`, benign by the *join* clause of his
  Lemma 3.2(2), which this repository has as `Higman.BenignTF.sup`
  (`Higman/BenignTorsionFree.lean:146`), given `V_{ℰ_m}` benign by his
  Example 3.11.

  **Open:** I have not read Example 3.11, so `V_{ℰ_m}` is an unresolved
  citation.  Do not budget the step until someone reads it; the shape
  (a one-parameter family cut out of a free group) suggests it is in the same
  territory as `Agree.AgreeInputs` (`Higman/AgreeClosure.lean:231`), which a
  sibling is closing --- worth checking whether `Agree.rowSub Agree.piV` /
  `Agree.zetaV` already covers it before writing anything new.

Note the join clause is where the repo's own architecture pays off:
`BenignTF.sup` is proved over a direct product with two HNN extensions and
**introduces no amalgam**, so the torsion clause is free
(`Higman/BenignTorsionFree.lean:131--150`).

---

## 4.  Discharging `TowerClosure.descent` --- and the one missing lemma

### 4a.  Why the existing descent lemmas do not do it

`Higman.HNNDescent.closure_inf_range` (`Higman/HNNDescent.lean:410`) proves
`⟨Z, t⟩ ⊓ P = Z` for a `Stable` subgroup `Z` (`:182`), and
`Higman.Pinch.pinch` (`Higman/Pinch.lean:467`) is the centralizing special
case.  **Neither applies at stage 3**, and it is worth recording why, because
it is the reason the `ωₘ` step is a genuine normal-form analysis rather than a
descent:

> `W_B = ⟨Z, r⟩` with `Z = ⟨g_β : β ∈ B ∩ ℰ_m⟩ ⊔ ⟨a⟩`, and `Z` is **not**
> `ρ`-stable.  `Z ∩ F₃` contains `a_β` for every `β ∈ B ∩ ℰ_m`, and
> `ρ(a_β) = a_{β[1]}`, the same block one window along --- which is *not* in
> `Z`; reaching it is exactly what `r` is for.  So `HNNDescent.Stable` fails
> by design.

The descent lemmas remain the right tool for stages 1 and 2 (where the
centralized subgroups *are* stable, trivially, `φ` being the identity), and
`Higman.mem_of_conj_mem_range` (`Higman/HNNCentralizer.lean:68`) is Britton in
the exact form those two stages need.

### 4b.  The normal-form analysis, in Ω′

Run in `Ω′`, where the full relation list is available.  Scanning a word
`w ∈ W_B ∩ F₃` produces three cases (the source's, in its numbering):

* **Case 1** --- `w′ = g_β⁻¹ · a^{b_l} · g_β` with `l` vanishing on the window
  `[0,m)`.  Then `g_β` commutes with `b_l` (stage 1) and the subword collapses
  to `a^{b_{β + l}}`, i.e. to `a_{l₃}` with `l₃ ∈ ωₘ B`.  This is the *only*
  case that stays in the base, and it is precisely the inverse of the peeling
  step already proved as `Omega.emb_aElt_eq_conj` (`OmegaTower.lean:442`).
* **Case 2** --- `l` is nonzero somewhere on the window.  Then `g_β` does
  **not** commute with `b_l`, and `w ∉ ⟨a,b,c⟩`.  This is the content, as the
  briefing said.
* **Case 3** --- `g_β` occurs, but not inside a subword of Case 1's shape.
  Again `w ∉ ⟨a,b,c⟩`.

Cases 2 and 3 are both "a `g`-letter survives the scan", so both are Britton
at stage 1 --- `mem_of_conj_mem_range` with the centralized subgroup `B₀ₘ`,
whose defining property is exactly that `bᵢ` for `i ∈ [0,m)` is *not* in it.

### 4c.  The missing lemma: Mikaelian 2.4

Transferring the Ω′ computation to Ω needs his Lemma 2.4:

> Let `Γ = G ∗_φ t`, `φ : A ≃* B` with `A, B ≤ G`.  If `G′ ≤ G` and, setting
> `A′ = G′ ⊓ A` and `B′ = G′ ⊓ B`, we have `φ(A′) = B′`, then
> `Γ′ = ⟨G′, t⟩ = G′ ∗_{φ′} t` with `φ′` the restriction, and moreover
> `Γ′ ⊓ G = G′`, `Γ′ ⊓ A = A′`, `Γ′ ⊓ B = B′`.

Status in this repository:

* the hypothesis `φ(A′) = B′` **is** `Higman.HNNDescent.Stable`
  (`Higman/HNNDescent.lean:182`) --- the two implications `fwd`/`bwd` are its
  two inclusions;
* the conclusion `Γ′ ⊓ G = G′` **is** `Higman.HNNDescent.closure_inf_range`
  (`:410`), already proved;
* the conclusion "`Γ′` is itself an HNN extension of `G′`" is **not in the
  repository in any form.**  This is the one genuinely new lemma the lane
  needs, and it is what licenses `Ω′ ↪ Ω`.

Two ways forward, in order of preference:

1. **Prove the structural half of 2.4 once**, as
   `Algebra/HNNSubextension.lean`: build `G′ ∗_{φ′} t → Γ` by
   `HNNExtension.lift`, and get injectivity from `closure_inf_range` plus a
   length/Britton argument on `HNNExtension.NormalWord.ReducedWord`.  It is
   reusable --- Higman's §4 uses the same move in the `ρ`, `τ` and `θ` clauses
   too, so a sibling lane pays for it as well.
2. **Avoid it**, by running the normal-form analysis directly in Ω.  This
   trades one clean lemma for a scan against relation lists that are no longer
   complete (the benign witnesses `K` and `M` are opaque finitely presented
   groups), which is why the source does not do it.  Not recommended.

---

## 5.  Landing order

Each step is independently landable and each has a green predecessor.

1. `OmegaTowerStages.lean` --- stage 1 as an iterated `Higman.CentHNN`, with
   finite presentation, torsion-freeness, injectivity of the base embedding,
   and the `commute_row` relation.  *Written; awaiting the same build as
   `OmegaTower.lean`.*
2. `Algebra/HNNSubextension.lean` --- the structural half of Lemma 2.4 (§4c).
   Independent of everything else on this lane; hand it out in parallel.
3. `B₀ₘ` benign in `⟨b,c⟩` (§3c(i)).  Also parallel.
4. Example 3.11/3.12: `L = Z_{ℰ_m}` benign in `Σ` (§3c(ii)).  Blocked on
   reading Example 3.11.
5. Stages 2 and 3, the `Omega.Tower` instance, and `conj_gen` / `conj_stable`.
   Blocked on 1.
6. `TowerClosure.descent` (§4b) --- blocked on 1, 2, 5.
7. `TowerClosure.benign` --- blocked on 3, 4, 5.

Steps 6 and 7 together inhabit `Omega.OmegaTowerInput`, and
`Omega.omegaInput_of` (`OmegaTower.lean:638`) then gives `Omega.OmegaInput`,
hence `ζ`, `π`, `ω` via `Omega.zeta_pi_omega_closures` and `θ`'s
`A_{oddZero}` via `Omega.benignTF_ASub_evenSupport` --- four of the seven
`Higman.OperationClosures` fields.
