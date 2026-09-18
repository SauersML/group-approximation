---
rg: 2
id: finite-seed-telescope-hosts-contracting-rsg-proof
kind: route
title: Proof that N_H is a finite nucleus of injections for finite seed groups H, so the one-chain telescope host lies in a finitely presented full contracting RSG, and that infinite seeds force an infinite nucleus
target: finite-seed-telescope-hosts-are-full-contracting-rsgs
requires:
  - telescope-fixed-points-are-singular-on-a-parse-shift
  - contracting-rsgs-embed-in-fp-simple-groups
  - hyperbolic-groups-lie-in-the-permutational-class
---

Notation as on the claim. The BBMZ statements are quoted from the arXiv TeX of 2309.06224v3
(local copy `$GQ/src/bh-free-03/bbmz2-2309.06224.tex`). The graph has one node with two loops, so
`Σ_Γ = C`, the core is the whole graph, and it is irreducible.
- **Local actions.** `f(αω) = f̄(α)·f|_α(ω)`, where `f̄(α)` is the smallest cone containing `f(C_α)`.
- `lem:restrict_twice`: `(f|_α)|_β = f|_{αβ}`.
- `lem:restrict_composition`: `(f∘g)|_α = (f|_{ḡ(α)} ∘ g|_α)|_ε`.
- `lem:finite_to_one`: `f̄^{-1}(β)` is finite.

**Step 0: parse states and local actions of θ_h and φ_h.** Read a finite word `α` with the
two-state parse automaton:
- from `B` (block start), letter `1` terminates and letter `0` goes to `I`;
- from `I` (inside a block), letter `0` stays in `I` and letter `1` returns to `B`.

`θ_h` starts in `B`, `φ_h` starts in `I`, and both copy letters until termination, then apply `h`
to the suffix. So for a word `α`:
- if the run from the start state has not terminated, `θ̄_h(α) = α`, and `θ_h|_α` is `θ_h` (current
  state `B`) or `φ_h` (current state `I`). The same holds for `φ_h`;
- if it terminated after the prefix `u` and `α = uβ`, then `θ̄_h(α) = u·h̄(β)` and `θ_h|_α = h|_β`.

In particular every local action of `θ_h` or `φ_h` lies in `N_H`. `θ_h` and `φ_h` occur infinitely
often (along `(01)^n` and `(01)^n 0`). Each `h|_β` occurs infinitely often, at `uβ` for all `u ∈ U`.
So `Nuc_{θ_h} = Nuc_{φ_h} = {θ_h, φ_h} ∪ {h|_β : β}`, which contains `id`, because `h ∈ V` acts by
canonical similarities on deep cones.

**Two synchronization facts.** The runs from `B` and from `I` on a word starting with `0` are both
in state `I` after one letter, and agree from then on. On a word starting with `1`, the run from
`B` terminates, while the run from `I` moves to `B`.

**Step 1: N_H is a nucleus of injections when H is finite.** BBMZ's six conditions:
- **(MapNuc)** Every element is a map `C → C`. Maps `h|_β` may be non-surjective; BBMZ allow this
  (their line 844).
- **(IdNuc)** `id ∈ N_H`.
- **(LocNuc)** By Step 0 for `θ_h` and `φ_h`, and by `lem:restrict_twice` for `h|_β`.
- **(RecurNuc)** Every element of `N_H` lies in `Nuc_{θ_h}` for some `h` (Step 0).
- **(InvNuc)** All elements are injective open maps.
  - `θ_h^{-1} = θ_{h^{-1}}` and `φ_h^{-1} = φ_{h^{-1}}`, whose nuclei lie in `N_H` because `H` is a group.
  - For `p = h|_β`, the local actions of `p^{-1}` at deep cones are restrictions of `h^{-1}`,
    exactly as in BBMZ's proof of InvNuc, so `Nuc_{p^{-1}} ⊆ {h^{-1}|_γ} ∪ {id} ⊆ N_H`.
- **(ProdNuc)** For `p, q ∈ N_H` we need `Nuc_{pq} ⊆ N_H`. By `lem:restrict_composition`,
  `(pq)|_α = (p|_{q̄(α)} ∘ q|_α)|_ε`. Cases:
  - *`p, q` both of type θ or φ, with the same start state* (`θ_hθ_k` or `φ_hφ_k`). The runs are
    synchronized. So `(pq)|_α` is `θ_{hk}` or `φ_{hk}` before termination, and after termination at
    `u` with suffix `β` it is `(h|_{k̄(β)} ∘ k|_β)|_ε = (hk)|_β`. All of these lie in `N_H`.
  - *`θ_h φ_k`.* On `α = 0γ` the runs synchronize after one letter, as in the previous case.
    On `α = 1γ`, `φ_k` moves to `B`, so `φ̄_k(1γ) = 1·θ̄_k(γ)`, `φ_k|_{1γ} = θ_k|_γ`, and `θ_h` has
    terminated, so `θ_h|_{1δ} = h|_δ`. Hence `(θ_hφ_k)|_{1γ} = (h|_{θ̄_k(γ)} ∘ θ_k|_γ)|_ε`.
    - `h ∈ V` has non-identity local actions only on a finite set `B_h` of words.
    - By `lem:finite_to_one`, only finitely many `γ` have `θ̄_k(γ) ∈ B_h`.
    - For every other `γ` the local action is `θ_k|_γ ∈ N_H`.
  - *`φ_h θ_k`.* On `0γ` the runs synchronize. On `1γ`, `θ_k` terminates and `φ_h` moves to `B`,
    so `(φ_hθ_k)|_{1γ} = (θ_h|_{k̄(γ)} ∘ k|_γ)|_ε`. For all but finitely many `γ`, `k|_γ = id`, so
    this equals `θ_h|_{k̄(γ)} ∈ N_H`.
  - *One factor is `h|_β`.*
    - If `q = h|_β`, then `q|_α = id` for all but finitely many `α`, and there `(pq)|_α = p|_{q̄(α)}`,
      which lies in `N_H` by LocNuc.
    - If `p = h|_β`, then `p|_{q̄(α)} = id` except when `q̄(α)` lies in a finite set, which by
      `lem:finite_to_one` happens for only finitely many `α`. There `(pq)|_α = q|_α ∈ N_H`.
  - *Both factors of the form `h|_β`.* The composite has identity local actions on deep cones.

  So `N_H` is a nucleus of injections, and it is finite: `H` is finite and each `h ∈ V` has only
  finitely many local actions (it is rational).

**Step 2: the host.**
- By `thrm:RSGCharacterization` (BBMZ l. 770), `𝕋_H = {f ∈ R_2 : Nuc_f ⊆ N_H}` is a full RSG with
  nucleus `N_H`. Its proof shows `V ≤ 𝕋_H`.
- By Step 0, `Nuc_{θ_s}, Nuc_{φ_s} ⊆ N_H`, so `θ_s, φ_s ∈ 𝕋_H`, and `⟨V, θ_S⟩ ≤ 𝕋_H`.
- `𝕋_H` is contracting: the core is irreducible and `N_H` is finite (Definition `def:contracting`).
- So it is finitely presented by `thrm:fin_pres` (l. 840), and it embeds in a finitely presented
  simple group by `prop:contr_to_simple` (l. 1752).
- It is a type (A) actor by the BBMZ Prop 5.1 read-off in `hyperbolic-groups-lie-in-the-permutational-class`,
  whose hypotheses are "full, contracting RSG".
- The full closure `[[⟨V, θ_S⟩]]` is contained in the full group `𝕋_H`. It is itself a full RSG,
  since it contains `V`, and its nucleus is contained in `N_H`. So it is contracting, and finitely
  presented by the same theorem.

**Step 3: infinite seeds.** Let `G'` be any RSG containing `⟨V, θ_S⟩`, so `θ_h ∈ G'` for every
`h ∈ H`. Then `Nuc_{G'} ⊇ Nuc_{θ_h} ∋ θ_h` by Step 0, and `h ↦ θ_h` is injective (item 1 of
`telescope-fixed-points-are-singular-on-a-parse-shift`). So `|Nuc_{G'}| ≥ |H| = ∞`, and `G'` is not
contracting.

**Step 4: singular set.** This is item 3 of `telescope-fixed-points-are-singular-on-a-parse-shift`.
For `h ≠ 1`, `θ_h` agrees with no prefix replacement near any point of `Y`.

**Trust surface.** The five BBMZ statements above were read at source (TeX). The rest is
elementary. The type (A) conclusion inherits the lane-proof status of
`hyperbolic-groups-lie-in-the-permutational-class`, which both referees passed.

**Lesson for general BH.** The finite-nucleus condition is the one-chain form of a locally unique
parse with finitely many parse states, and it absorbs an uncountable SFT of singular points at no
cost. What self-simulation cannot supply is an infinite seed. The input must enter through a
finitely presented acting group, which is exactly the part of Conjecture SS that is still open (P2′).
