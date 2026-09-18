---
rg: 2
id: higman-clapham-towers-leave-the-seed-form-at-three-steps
kind: claim
title: Read at source, Clapham's embedding supplies the decidability premise (DB) but uses infinitely generated steps, and the Aanderaa-Cohen tower leaves the finitely generated free/free-abelian seed form at exactly three steps - the input as a vertex group, one infinite-rank rope HNN indexed by a regular set, and one HNN along a subgroup encoding the halting set
requires:
  - higman-clapham-envelopes-are-hnn-over-machine-times-input
  - relative-seeds-glue-graphs-of-groups-into-class-c
  - decidable-free-subshifts-pass-to-graphs-of-groups
distinct_from:
  higman-clapham-envelopes-are-hnn-over-machine-times-input: that isolates the envelope's last splitting and states premise (DB) unverified; this reads Clapham 1967 and Cohen 1989 at source, confirms (DB) from Clapham's own proof, and lists every step of both towers against the seed-tower form.
  relative-seeds-glue-graphs-of-groups-into-class-c: that glues rigid relative seeds along graphs of groups and puts graphs of free and free abelian groups in class C; this identifies which steps of the Higman-Clapham towers are covered by it and which need new relative seeds.
---

**ESTABLISHED** as a reading of the sources (lane bh-invent-14, 2026-09-18).
- **Read at source** (PDFs fetched on MSI):
  - C. R. J. Clapham, *An embedding theorem for finitely generated groups*, Proc. London Math. Soc. (3) **17** (1967) 419–430 (Wiley);
  - D. E. Cohen, *Combinatorial Group Theory: a topological approach*, LMS Student Texts 14, CUP 1989, Chapter 9, §9.4 (pp. 265–268) and §9.6 (pp. 279–281) (Cambridge Core).
  - Cohen's §9.6 is the modular-machine proof of Higman's theorem due to Aanderaa and Cohen.
- **Not read:** S. Aanderaa, D. E. Cohen, *Modular machines and the Higman–Clapham–Valiev embedding theorem*, Word Problems II (1980) 17–28, doi 10.1016/s0049-237x(08)71328-4. It is behind the Elsevier wall from MSI.
- The seed-form verdicts in §3 are this lane's analysis, not the sources'.

## 1. Clapham 1967

- **The envelope** (Theorem 6, pp. 428–429).
  - `G = F/R`, and `R` is strongly benign in `F` (Lemma 11.2).
  - So the double `H = {F_1, F_2; r_1 = r_2, r ∈ R}` embeds in a finitely presented `K` with
    soluble word problem, and "`{F_1, F_2}` in `K` [is] soluble".
  - The envelope is `{K × G, t; t^{-1}(f_1,1)t = (f_1, fR), t^{-1}(f_2,1)t = (f_2,1)}`.
  - This is the splitting of `higman-clapham-envelopes-are-hnn-over-machine-times-input`, with the
    double `F_1 *_R F_2` in place of the `t`-conjugate there.
- **Clapham proves (DB).** On p. 429 he shows: "`(k,g) ∈ H` iff `k ∈ H` and `g = 1`", and
  "`(k,g) ∈ {(f_1,fR),(f_2,1)}` iff `k ∈ H` and `g = k*`".
  - These are the two membership problems for `H × 1` and for the **graph of `π`**. So premise
    (DB) holds, verbatim from his proof, in the degree-0 case ("𝒜-soluble" = soluble).
- **Every stage is decidable.**
  - Theorem 4 (p. 423) builds `R` through a sequence of 𝒜-recursive r.e. sets `X_1, …, X_n`.
  - The proof of Theorem 3 checks at each operation that "the resulting set `ζX_j, πX_j` or
    `θX_j` is 𝒜-recursive" (p. 421).
  - So in the decidable case every intermediate set is recursive. That is the "decider tower" of
    41501ac60 §4, confirmed.
- **But the steps are not finitely generated.**
  - Lemma 9.2 (p. 424) uses HNN extensions `{G, t_1, t_2, …; t_i^{-1} a_i t_i = φ_i(a_i)}` with
    *countably many* stable letters.
  - Lemma 11.2 (p. 427) amalgamates the infinite-rank free group `{a,b,f,g,c_w (all w)}` with
    `{c,d,e}` along the infinitely generated subgroup `c_w = w̄^{-1} c w̄`.
  - Only after that does it take an HNN by `s, t` over finitely generated subgroups, which gives
    the finitely presented `L`.

## 2. The Aanderaa–Cohen tower (Cohen §§9.4, 9.6)

| step | group | pieces and associated subgroups | seed form? |
|---|---|---|---|
| 0 | `K = ⟨x,y,t; xy=yx⟩ = Z^2 * Z` (also the HNN of `F(x,t)` over `⟨x⟩`) | free abelian and free | yes |
| 1 | `K_M`: HNN of `K`, stable letters `r_i`, `l_j` | `⟨t(a,b), x^m, y^m⟩ → ⟨t(c,0), x^{m^2}, y⟩`, finitely generated and `≅ K` | yes (see below) |
| 2 | `H_1 = K_M * (C × ⟨b_1,…,b_n⟩) * ⟨d⟩` | the **input `C`** enters in a vertex group | **no** |
| 3 | `H_2`: HNN of `H_1` by `p`, with `p^{-1} t_α p = t_α w_α(b) d` for all `α ∈ I` | `⟨t_α : α ∈ I⟩` and `⟨t_α w_α(b) d⟩`, free of **infinite rank** (bases, p. 280) | **no** (not finitely generated) |
| 4 | `H_3`: HNN of `H_2` by `a_i` (`A → A_i`) and `k` (`A_+ → A_-`) | `A = ⟨t,x,d,b_j,p⟩`, `A_i = ⟨t_i,x^m,b_id,b_j,p⟩`, `A_+ = ⟨U,d,b_j,p⟩`, `A_- = ⟨U,d,b_jc_j,p⟩`, all finitely generated | finitely generated, but the relative seeds are **hard** |

`H_3` is finitely presented and contains `C` (pp. 280–281).

**Notes on the table.**
- **Step 1 is in class 𝒞.** `⟨t(a,b), x^m, y^m⟩` is conjugate by `x^a y^b` to `⟨x^m,y^m⟩ * ⟨t⟩`.
  By Kurosh, that is a free factor of the index-`m^2` kernel of `K → (Z/m)^2`. Relative seeds
  exist by gluing plus finite-index induction (items 1 and 2 of
  `relative-seeds-glue-graphs-of-groups-into-class-c`). The other side works the same way with
  `Z/m^2`.
- **Step 3 is indexed by a regular set.** `I` is the set of `α` whose `m`-ary digits all lie in
  `{1, …, 2n}` (p. 279). So `⟨t_α : α ∈ I⟩` is the free factor of the free group
  `T = ⟨t(i,j)⟩` spanned by a regular set of basis letters. Its membership problem is decidable.
- **Step 4 carries the machine and the coupling.**
  - `U ∩ K = ⟨t(α,β) : (α,β) ∈ H_0(M)⟩` (p. 280), so membership in `A_±` encodes the halting set
    `H_0(M)`.
  - `A_-` contains `b_j c_j`, which couples the free letters to the input's generators. This is the
    Aanderaa–Cohen form of `graph(π)`.
- **Decidability.** Cohen's Proposition 20 gives only one direction: if `G_M` has solvable word
  problem then `H_0(M)` is recursive. Premise (DB) needs a machine whose halting set is recursive
  over *all* configurations, not only over valid inputs. Whether a decider compiles to such an `M`
  is the Higman–Clapham–Valiev refinement in the unread 1980 chapter.
  Clapham 1967 (§1) supplies (DB) by a different route.

## 3. Verdict for the seed tower

The seed form, as in `relative-seeds-glue-graphs-of-groups-into-class-c`, is: finitely many HNN
and amalgam steps over free or free abelian pieces, with finitely generated associated subgroups
of decidable membership, each of which needs a rigid relative seed. Against it:

1. **The input as a vertex group** (Clapham's `K × G`; Aanderaa–Cohen step 2, `C × F_n`).
   - This step is **necessary** for (FA) inputs, by the (FA) lemma of
     `decidable-free-subshifts-pass-to-graphs-of-groups`: an (FA) subgroup of a tower lies in a
     terminal piece.
   - So no Higman-type tower over free and free abelian pieces alone contains a nontrivial (FA)
     group. The seed tower must take `seed(C)`, or a relative seed on `C × F_n`, as an input.
     That is SYNTHESIS v6 gate 2, and it cannot be removed.
2. **The rope** (Clapham's Lemmas 9.2 and 11.2; Aanderaa–Cohen step 3).
   - The associated subgroups are infinitely generated.
   - In Aanderaa–Cohen they are free factors spanned by a *regular* set of basis letters. The
     first test for the team is `(H_1, ⟨t_α : α ∈ I⟩) ∈ 𝓡`. The relative-seed definition does
     not require `C` to be finitely generated, and a finite-state base-`m` digit marking is the
     natural candidate.
3. **The halting HNN** (Aanderaa–Cohen step 4).
   - The associated subgroups are finitely generated, but by item 3 of the relative-seed node the
     forced point of a rigid relative seed for `(H_2, A_+)` computes `H_0(M)`.
   - This is CAP, rung 1c. The coupling `A_-` is the seed form of "can local rules write
     `graph(π)`?".

Every other step (0, 1, and the finitely generated parts of 4) is covered by the relative-seed
gluing theorem.

## Lesson for general BH

**A Higman tower has exactly three non-free ingredients.**
- **The input as a vertex.** (FA) forces this, so the input's own seed is irreducible.
- **One infinite-rank rope.** It is indexed by a regular set of machine codes, so it should be
  finite-state.
- **One HNN along the machine's halting set.** This is CAP.

Clapham's proof shows that decidability is never the obstruction: every stage is recursive when
the input is decidable. The whole seed question is therefore whether *locally forced*
configurations can realize the third ingredient.
