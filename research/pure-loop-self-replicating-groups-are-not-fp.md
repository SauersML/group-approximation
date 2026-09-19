---
rg: 2
id: pure-loop-self-replicating-groups-are-not-fp
kind: claim
title: A fully self-replicating group G is finitely presented iff it is a retract of F/<<Q>> along the section-at-1^k map for a finite section-closed Q in K; then no free splitting of F into two factors of proper image can carry Q, so unit-weight recursions whose weight-preserving section cycles are pure loops (a finite screen) are never finitely presented; this kills R°, the separated-loop host R' and the decorated-loop host R_gamma with their Tits hosts
artifacts:
  - experiments/stable-retract-criterion-2026-09-18/pure_stable_part_checks.py
  - experiments/stable-retract-criterion-2026-09-18/pure_stable_part_checks.out
distinct_from:
  m11-balanced-loop-host-is-not-finitely-presented: that proves the stable-relator lemma and kills R° by one explicit relation family with a fixed twisted section; this turns the lemma into a retraction of the stable presentation onto G and a Kurosh obstruction, which needs no relation family, gives a finite screen for a whole class, and decides R' and R_gamma, where no fixed-section family was known.
  m11-balanced-loop-host-has-exact-finite-l-presentation: that reduces finite presentation of R° to one relator inclusion; this gives a criterion (retract along T_k) valid for every fully self-replicating group with finite section closures, and an obstruction that does not compute any inclusion.
  fp-self-similar-groups-have-fp-ray-loop-subgroups: that constrains finitely presented groups through loop subgroups at periodic rays, which are C_55, Z or 1 here and so are silent; this constrains them through free splittings of the stable presentation.
  self-wreathing-groups-are-not-fp-infinity: that obstruction is homological and needs a nonzero low-degree homology of the local group; this one is not homological and works for superperfect M_11.
  fully-self-replicating-fp-infinity-groups-are-acyclic: that is about FP_infinity and homology; this is about finite presentation, and about which relators a presentation can have.
---

**ESTABLISHED (unreviewed).** Proof: `pure-loop-self-replicating-groups-are-not-fp-proof`.
Items 1–3 are proved by hand. Item 4 checks finite conditions, which the script decides
exactly (its points are coded `0..10`). Infinite orders are imported from the cited nodes
or proved by a finite orbit argument.

**Setting.** Let `G = F/K` be self-similar on a finite alphabet `X`, with `|X| ≥ 2`. `F` is
free on a finite set `S`, and each letter `s` has root permutation `π_s` and letter sections
`s|_x` that are words over `S`. Sections of free words are computed letterwise and then
freely reduced. Assume the section closure of every finite set of words is finite (SF).

`G` is *fully self-replicating*: `G = G^X ⋊ P`, where `P` is the root image. So each
`ι_x : g ↦ g@x` is an endomorphism of `G`. Fix words `σ(s)` representing `s@1`, and let
`σ` be the induced endomorphism of `F`.

For a finite `R` with `⟨⟨R⟩⟩ = K`, let `Q` be its section closure and `Q^∞` its stable
part (`m11-balanced-loop-host-is-not-finitely-presented`, item 1). Put `Γ = F/⟨⟨Q^∞⟩⟩`,
with quotient map `ρ : Γ ↠ G`.

**Theorem.**

1. **Retract criterion.** `T_k(w) = σ^k(w)|_{1^k}` is an endomorphism of `F`, and `T_k(w)`
   represents `w` in `G`. `G` is finitely presented if and only if, for some finite
   section-closed `Q ⊆ K` and some `k`, `T_k(K) ⊆ ⟨⟨Q⟩⟩`.
   - In that case `T_k` induces `τ : G → F/⟨⟨Q⟩⟩` with `ρτ = id`, so `G` is a retract of a
     finitely presented group.
   - Conversely, if `G = F/⟨⟨R⟩⟩` is finitely presented, this holds for `Q^∞` and every
     `k ≥ k_0`.
2. **Free-splitting obstruction.** `G` is one-ended. Suppose `S = S_1 ⊔ S_2`, and every word
   of `Q^∞` is conjugate into `F(S_1)` or `F(S_2)`. Then `ρ(F(S_i)) = G` for some `i`.
   So if both `⟨S_1⟩` and `⟨S_2⟩` are proper subgroups of `G`, then `G` is not finitely
   presented.
3. **Pure-loop class (finite screen).** Call `s|_x` *weight-preserving* if it contains a state
   letter, and *cycle-capable* if moreover it lies on a directed cycle of the graph `s → t`
   of weight-preserving letter sections. Here state letters are those with some nontrivial
   section, and rooted letters are the rest. `G` is not finitely presented if all of the
   following hold:
   - (U) every letter section contains at most one state letter;
   - (A') the root permutations of the state letters generate `P_st ≠ P`;
   - (B') every cycle-capable letter section is a single state letter;
   - (C'') at each point `x` at most one state letter `s` has a cycle-capable section at `x`,
     and `π_s` fixes `x`;
   - (D) for each cycle-capable `s` of finite order `o`, every iterated section of the word
     `s^o` is pure, that is, it uses only state letters or only rooted letters.

   Under these conditions every stable relator is pure, so `Γ = Γ_st * Γ_rt`. But
   `ρ(Γ_st)` has root image `P_st ≠ P`, and `ρ(Γ_rt)` is finite.
4. **Instances over `M_11`.** In the notation of the cited nodes, with a free basis
   `{α, β, …}`:
   - `R° = ⟨M_11, b, C⟩` is not finitely presented. This is a second proof, and it uses no
     relation family.
   - **New:** the separated-loop host `R' = ⟨M_11, b, c'⟩`, with `c' = (1,1,1,c',bα,1,…)`,
     is not finitely presented. This was left open by `m11-separated-loop-host-has-b1-one`,
     where `b_1 = 1` passed the homology bound.
   - **New:** the decorated-loop host `R_γ = ⟨M_11, b_g, C⟩` is fully self-replicating and
     not finitely presented. Here `b_g = (γb_g, α, β, 1, …)`, `γ = αβ^{−1}` and
     `ord(b_g) = 220`. The screen applies after the Nielsen move `g = γ b_g`: `g` has root
     permutation `γ`, which fixes `1, 2, 3`, and the loop `g|_1 = g` becomes pure.
   - `R'' = ⟨M_11, b, c⟩` fails (C'') at the point `1` (both `b` and `c` loop there). Its
     non-finite presentation comes from `m11-odometer-free-host-is-not-finitely-presented`.
   - Hence the simple Tits hosts `(G ≀ M_12) *_{G×G} (G ≀ M_12)` of `R'` and `R_γ` are
     finitely generated and simple, and **not finitely presented**
     (`tits-hosts-for-transitive-local-actions`).
5. **Design rule for the Tits route.** A finitely presented candidate needs relators that
   mix state letters with state letters of a different root image, or state letters with
   rooted letters. Mixing is required on the stable cycles in every free basis, so that no
   free splitting of `F` into two factors of proper image carries `Q^∞`. `Γ` also contains
   `τ(G)`, and hence the infinite locally finite group of finitary `P`-automorphisms. So
   `Γ` is not hyperbolic, not virtually torsion-free, and not linear in characteristic 0.
   For example, small-cancellation power relators are ruled out.

**What this does not do.** A finitely presented example of this kind would be a finitely
presented branch group, since `G` is regular branch over itself. Whether one exists is the
open Bartholdi–Grigorchuk–Šunić question. So the construction requested on this route is
at least as hard as that question. The screen only kills classes; it does not produce
examples.
