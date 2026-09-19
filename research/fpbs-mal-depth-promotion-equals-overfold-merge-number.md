---
rg: 2
id: fpbs-mal-depth-promotion-equals-overfold-merge-number
kind: claim
title: At every depth j, the promotion cost Q_j of an essentially free profinite action equals the density of the least number of same-fibre merges of the folded L_{j+1}-graph that collapse its kernel onto the folded L_j-graph, and the L_j-labelled promotion cost is the fold seed density of the phi^j-twisted levels
distinct_from:
  fpbs-profinite-relcost-equals-fold-seed-density: that is the depth-0 case, where the target graph is the Schreier graph and every same-fibre merge is lawful; this is every depth j, where the target is the folded L_j-graph Gamma_j(Q) and merges that are not in the kernel of Gamma_{j+1}(Q) -> Gamma_j(Q) (overfold merges) are allowed.
  fpbs-word-chords-are-dominated-by-merges: that is the domination lemma for arcs attached to one folded graph, applied at depth 0; this applies it at depth j and adds the surjectivity of Gamma_{j+1}(Q) -> Gamma_j(Q), which forces every t_j-reading to stay inside the image of Gamma_{j+1}(Q).
  fpbs-mal-bernoulli-single-stage-floor: that is the open target, whose remaining half is (D1), a floor on Q_j uniform in j; this gives an exact finite formula for Q_j on profinite actions and proves no floor.
  fpbs-mal-promotion-cost-monotone-under-weak-containment: that reduces (D1) to per-depth free witnesses and computes nothing; this computes Q_j exactly on every essentially free profinite witness.
  fpbs-mal-overfold-merges-never-help: that is the open finite statement deep_j = law_j; this is the proved exact formula on which that statement acts.
artifacts:
  - experiments/fpbs-depth-overfolding-2026-09-17/foldlib.py
  - experiments/fpbs-depth-overfolding-2026-09-17/pair_automaton.py
  - experiments/fpbs-depth-overfolding-2026-09-17/seedtypes.py
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_search.py
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n6_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n4_j2.txt
---

**ESTABLISHED** through `fpbs-mal-depth-promotion-equals-overfold-merge-number-proof`.

**Setting.**
- `L = F(a, b)` acts on the right. `φ(a) = a` and `φ(b) = b a b^{-2}`.
- `t_j = φ^j(b)` and `L_j = φ^j(L) = <a, t_j>`. Then `t_0 = b`,
  `t_{j+1} = t_j a t_j^{-1} t_j^{-1}`, and `K = L_1`.
- `Q_j(X)` is the least cost of a graphing `Ψ` inside `E_{X|L}`, with labels
  anywhere in `L`, such that `E_{X|L_{j+1}} ∨ Ψ ⊇ E_{X|L_j}`.
  `Q_j^law(X)` is the same infimum with labels restricted to `L_j`.
- For a finite `L`-set `Q`, `Γ_j(Q)` is the fold of this graph:
  - real vertices `Q`;
  - an `a`-edge `p → p·a` for each `p`;
  - a path labelled `t_j` from each `p` to `p·t_j`.

  So `Γ_0(Q)` is the Schreier graph. `ψ : Γ_j(Q) → Q` sends each vertex to
  the point under it.
- `cl(P)` is the fold-closure of a set `P` of vertex pairs, as in
  [[fpbs-word-chords-are-dominated-by-merges]].
- `Q^{(j)}` is the set `Q` with `a` acting as `a` and `b` acting as `t_j`.
  `r(·)` is the 2-of-3 percolation number of
  [[fpbs-mal-profinite-fold-density-is-finite-percolation]].

**Claim.**

1. **(Surjectivity.)** There is a unique morphism
   `m : Γ_{j+1}(Q) → Γ_j(Q)` fixing the real vertices. It is onto on both
   vertices and edges, so `Γ_j(Q) = Γ_{j+1}(Q) / ker(m)`.
2. **(Merge numbers.)** Define:
   - `deep_j(Q)` is the least `|P|`, over sets `P` of pairs of vertices of
     `Γ_{j+1}(Q)` lying over the same point, with `cl(P) ⊇ ker(m)`;
   - `law_j(Q)` is the same minimum over `P ⊆ ker(m)`. For such `P`,
     `cl(P) ⊆ ker(m)` holds automatically, so the condition is
     `cl(P) = ker(m)`.

   Pairs in `P \ ker(m)` are *overfold merges*. Then
   `deep_j(Q) ≤ law_j(Q) = r(Q^{(j)})`. At `j = 0`, `Γ_0(Q)` has one vertex
   over each point, so every same-fibre pair is lawful and
   `deep_0 = law_0 = r`.
3. **(Chords.)** A chord `(p, w)` attaches a path labelled `w ∈ L` from `p`
   to `p·w`. Let `X` be an essentially free action with factor `Q`, and let
   `Φ` be a finite set of level-`Q` chords. Then
   `E_{X|L_{j+1}} ∨ Φ ⊇ E_{X|L_j}` iff
   `F(Φ) = fold(Γ_{j+1}(Q) ∪ chord paths)` admits a morphism from
   `Γ_j(Q)` fixing the real vertices. The least such `|Φ|` is `deep_j(Q)`.
   With labels restricted to `L_j`, it is `law_j(Q)`.
4. **(Profinite exactness.)** Let `X = lim Q_m` be an essentially free
   profinite action of `L` with transitive levels. Then

   ```text
   Q_j(X)      =  inf_m  deep_j(Q_m) / |Q_m| ,
   Q_j^law(X)  =  inf_m  law_j(Q_m)  / |Q_m|  =  inf_m r(Q_m^{(j)}) / |Q_m| .
   ```

**Reading.**
- The w15 obstruction to (D1) was that `t_j`-readings might pass through
  the Δ-part of the fold. Item 1 removes it. Any morphism
  `Γ_j(Q) → F(Φ)` fixing the reals composes with `m` to the canonical map
  of `Γ_{j+1}(Q)`. So its image is the image of `Γ_{j+1}(Q)`, and chords
  act on the finite graph `Γ_{j+1}(Q)` only through vertex merges.
- By Theorem M and Abért–Weiss, `Q_j(ρ) ≥ Q_j(X)` for every free `X`. So
  (D1) follows from two finite statements:
  - (O) `deep_j = law_j`, which is
    [[fpbs-mal-overfold-merges-never-help]];
  - (W) a uniform lower bound on `r(Q_m^{(j)}) / |Q_m|`, which is
    [[fpbs-mal-twisted-level-seed-density-uniform-witness]].

  The route is `fpbs-mal-depth-floor-from-overfold-domination`.
