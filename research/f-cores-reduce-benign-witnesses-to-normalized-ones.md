---
rg: 2
id: f-cores-reduce-benign-witnesses-to-normalized-ones
kind: claim
title: "The F-core of any benign witness is an F-normalized witness with the same quotient, so the passage to normalized witnesses is exactly a finiteness question on the core; in a torsion-free witness for N_U (or V, or Z/2 wr Z) the core has infinitely generated homology and U acts on it with homologically trivial part of bounded rank; every commensurated witness with open orbit closure, finitely many F-conjugates of Sigma, or a cut-out whose F-closure is open dies"
distinct_from:
  normalized-benign-witnesses-give-the-semidirect-join: That leaves open the passage from an arbitrary witness to a normalized one; this shows the passage always exists at the level of groups (the F-core) and is exactly the finiteness type of the core, so root => normalized witness is equivalent to root with an F_m core.
  type-f-weyl-groups-have-bounded-elementary-abelian-ranks: That applies Browder to a normalized witness whose Sigma has finitely generated homology; this applies it to the canonical normalized core of every witness, commensurated or not, and turns the conclusion into a homological lower bound on the core.
  commensurated-witnesses-survive-browder-but-die-when-linear: That uses Q-cores of finite subgroups, one Q at a time, with Q-dependent Sigma_Q; this uses the single F-core for all of P at once and identifies when it is of finite index.
  haagerup-cut-out-completions-force-haagerup-quotients: That reduces discrete completions to a finite-index normal core; this gets the same reduction whenever the closure of rho(F) is open, with no discreteness, and kills lattice-type witnesses in G_1 x G_2.
  commensurated-quotients-coarsely-embed-in-hecke-graphs: That shows the Hecke graph must coarsely contain U; this adds a rigidity condition on the same graph (the compact open stabilizer must act on the F-orbit of the base vertex with infinite image).
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Setting as in
`commensurated-witnesses-survive-browder-but-die-when-linear`: `F` free,
`N ⊴ F`, `P = F/N`, a witness `Σ ≤ Λ ⊇ F` with `Σ ∩ F = N`. No
finiteness type or commensuration is assumed unless stated. The **F-core**
of the witness is

`S = core_F(Σ) = ∩_{f ∈ F} fΣf^{-1}`.

**Theorem.**

1. **Every witness contains a normalized one.** `S` is normalized by `F`,
   `S ∩ F = N`, and `E = FS` has `E/S ≅ P`. The conjugate `fΣf^{-1}` depends
   only on the image of `f` in `P/P_Σ`, where `P_Σ = N_F(Σ)/N`. Hence:
   `N` has an `F`-normalized `F_m`-witness if and only if it has a witness
   with `Λ` of type `F_m` whose `F`-core is of type `F_m`.
2. **Browder at the core.** Let `Λ` be torsion-free and `n = cd Σ < ∞`.
   Let `W ⊴ P` be the kernel of the action of `P = E/S` on
   `⊕_{i ≥ 1} H_i(S; Z)`. Then every elementary abelian `p`-subgroup of `W`
   has rank `≤ 2n`, for every prime `p`. So for every elementary abelian
   `A ≤ P`, the image of `A` in `P/W ↪ ∏_{i=1}^{n} Aut H_i(S; Z)` has rank
   `≥ rk A - 2n`.
3. **The core of a witness for `U` has infinitely generated homology.**
   Under the hypotheses of item 2, if every `H_i(S; Z)` is finitely
   generated, then `rk_p A ≤ 2n + Σ_i rk_p Aut H_i(S; Z)` for all elementary
   abelian `A ≤ P`. So for `P` equal to `U`, `V`, `Z/2 ≀ Z`, Grigorchuk's
   group, or any group with unbounded finite-subgroup `p`-rank, **every**
   torsion-free finite-`cd` witness, of any finiteness type and commensurated
   or not, has an `F`-core `S` with some `H_i(S; Z)` not finitely generated.
   In particular `S` is not of type `FP_∞`.
4. **Commensurated witnesses that die.** Let `Σ` be of type `F`, `Λ` torsion-free and `Σ` commensurated by
   `F`. The following each imply `[Σ : S] < ∞`, so `S` is
   of type `F`, and then item 3 bounds the ranks of `P`:
   - (a) `P_Σ` has finite index in `P`, i.e. `F` has finitely many
     conjugates of `Σ` (always true for finite `P`);
   - (b) **open closure:** there are a subgroup `C ≤ Λ` containing `F`, a
     homomorphism `ρ : C -> H` to a totally disconnected locally compact
     group and a compact open `K ≤ H` such that `Σ' = ρ^{-1}(K)` has finite
     index in `Σ` and `Σ' ∩ F = N`, and the closure `F̂` of `ρ(F)` is
     **open** in `H`;
   - (c) the relative Schlichting completion `G` of `(⟨F, Σ⟩, Σ)` has the
     closure of `F` open. Equivalently, the Hecke closure of `N` in `Σ` has
     finite index. Discrete `G` is a special case;
   - (d) **lattice type:** `Λ` is a lattice in `G_1 × G_2` with `G_2`
     totally disconnected, `Σ = Λ ∩ (G_1 × K)`, and the closure of
     `pr_2(F)` is open in `G_2`, for example `F` projecting densely.
   In each case `(Λ, S)` is a type `F` `F`-normalized witness for `N`.
   So `U`, `V`, `Z/2 ≀ Z` and Grigorchuk's group have no such witness.
5. **Exact form of what survives.** For a commensurated witness let `o` be
   the base vertex `Σ` of the Hecke graph `Hk` of
   `commensurated-quotients-coarsely-embed-in-hecke-graphs`, `K` its
   stabilizer in `G`, and `F·o = φ(P)` the orbit. Then
   `S = Σ ∩ ρ^{-1}(Fix_K(F·o))`. `S` has finite index in `Σ` if and only
   if `Fix_K(F·o)` is open, i.e. `K` acts on the orbit `F·o` through a
   finite quotient; then `[Σ : S] = [K : Fix_K(F·o)]`. So a torsion-free
   type `F` commensurated witness for `N_U` must satisfy all of:
   - `Hk` coarsely contains `U` (the earlier gate);
   - `K` acts on `φ(U)` with **infinite** image, i.e. the pointwise
     stabilizer of the orbit is not open;
   - in every cut-out presentation, `F̂` is a **non-open** closed subgroup
     of `H`, with `M = F̂ ∩ K` of infinite (uncountable) index in `K`;
   - the core `S = Σ ∩ Fix(φ(U))` has some `H_i(S; Z)`, `1 ≤ i ≤ cd Σ`, not
     finitely generated, and `U` acts on `H_*(S; Z)` with homologically
     trivial part of elementary abelian rank `≤ 2 cd Σ`.

**Sharpness.** The surviving regime is not empty. In `BS(1,2) = ⟨a, t⟩`
with `Σ = ⟨a⟩` and `F = ⟨t⟩`, the witness is torsion-free, type `F` and
commensurated, `N = 1`, and `S = ∩_k ⟨a^{2^k}⟩ = 1` has infinite index in
`Σ`. The closure of `F` in `Q_2 ⋊ Z` is the discrete subgroup `Z`, which is
not open. Here `P = Z` is torsion-free, so the example shows only that the
gate is not vacuous.

**Consequence for the brief.** The step "find a torsion-free type `F`
commensurated pair whose Hecke graph coarsely contains `U`" is sharpened. The
pair must also be **non-rigid along `U`**, as in item 5. For `Z/2 ≀ Z`, the
finiteness type of `(Λ, Σ)` excludes it exactly when it forces the core to
have finite index or finitely generated homology (items 3 and 4). What
survives is a witness whose core has infinite index. Whether some type `F`
commensurated witness for `Z/2 ≀ Z` has an infinite-index core is **open**.
It is the first test case of the surviving regime.

Proof: route `f-cores-reduce-benign-witnesses-to-normalized-ones-proof`.

## Attempts

- 2026-09-18 (w14-117): proved items 1–5. Proposed-established. Open: a
  torsion-free type `F` commensurated witness for `Z/2 ≀ Z` with
  `[Σ : S] = ∞`, or a proof that none exists.
