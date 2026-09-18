---
rg: 2
id: gl-n-q-explicit-natural-fp-overgroup
kind: claim
root: true
title: For every n >= 2 some explicit and natural finitely presented group contains GL_n(Q)
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that asks for a finitely presented SIMPLE overgroup of GL_n(Q), with no explicitness requirement; this asks for an explicit and natural finitely presented overgroup, simple or not. A natural simple host would answer both.
  gl-n-q-in-permutational-boone-higman-class: that asks for a finitely presented overgroup with a type (A) action, the route to a simple host; this asks for any explicit natural finitely presented overgroup.
  lifts-add-no-unipotent-divisibility: that is an obstruction to one family of candidate hosts (central and covering lifts); this is the construction problem itself.
artifacts:
  - research/artifacts/gq-gq-lit-arxiv-priority.md
---

**OPEN.** For every `n >= 2`, give an explicit and natural finitely presented
group `Γ_n` together with an embedding `GL_n(Q) -> Γ_n`.

"Natural" is informal. Here a construction counts when `Γ_n` is described
uniformly: a group of transformations of a named space, or a matrix or
automorphism group over a named ring or group, and not by running an embedding
algorithm on a presentation of `GL_n(Q)`.

## Source

- Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3, Problem 2.7: "For n >= 2,
  find an explicit and natural example of a finitely presented group that
  contains GL_n(Q)." Just before it the survey says that Bridson and de la Harpe
  also asked about `GL_n(Q)` and that "this part of their question remains open".
- Kourovka notebook, Problem 14.10 (Bridson--de la Harpe, 1999). Mikaelian
  (arXiv:2507.04347, §1.4) numbers the `GL_n` part 14.10(c) in the current
  edition and quotes it as: "Find an explicit and "natural" finitely presented
  group Γ_n and an embedding of GL(n,Q) in Γ_n." The entry and its comments in
  the 21st edition (arXiv:1401.0300v46) have not been read here.

## Known

- **Existence without explicitness.** `GL_n(Q)` is computably presented, so
  Higman's embedding theorem, through the two-generator overgroup of
  Higman--Neumann--Neumann, puts it in some finitely presented group (survey
  Corollary 2.4).
- **Explicit, not natural (announced).** Mikaelian, arXiv:2507.04347v8
  (2026-06-03), §1.4: "We would like to announce that, as another application
  of Algorithm 1.1, an explicit embedding of GL(n,Q) into some finitely
  presented Γ_n reflecting this question is suggested. Moreover, that group Γ_n
  can even be 2-generator [41]." No construction is given in that paper, and
  [41] was not found on arXiv on 2026-09-17. The method is an explicit run of
  Higman's construction, so it does not address naturality.
- **n = 1 and the additive part.** Belk--Hyde--Matucci answer Kourovka 14.10(a)
  naturally: `(Q,+) <= T-bar`, the lifts of Thompson's `T` to the real line
  (arXiv:2005.02036, Bull. AMS 59, 2022). `GL_1(Q) = Q^x` is countable abelian,
  so it lies in the finitely presented simple group `VA` (survey Theorem 4.11).

## Necessary features of any host

Each item follows from a subgroup of `GL_2(Q)` or `GL_3(Q)` and passes to every
overgroup.
1. **Not residually finite** (root obstruction O1): `(Q,+) <= GL_n(Q)` is
   divisible.
2. **Exponentially distorted cyclic subgroups** (root obstruction O4):
   `BS(1,2) = <x -> x+1, x -> 2x> <= GL_2(Q)`. More strongly, `a : x -> x+1` has
   an `m`-th root and is conjugate to `a^m` for every `m >= 1`. So a finitely
   generated host has an element conjugate to each of its positive powers and
   divisible by every integer.
3. **For n >= 3, not a-T-menable.** `SL_3(Z) <= GL_3(Q)` is infinite with
   property (T). The Haagerup property passes to subgroups, so no a-T-menable
   group (for example `V`, by Farley) can be the host. The Heisenberg group
   `U_3(Z) <= GL_3(Q)` also forces a quadratically distorted central element.

## Host classes: status

| Class | Status | Reason |
|---|---|---|
| Residually finite groups (f.g. linear, self-similar, tree groups) | dead | item 1 |
| `VA` and its subgroups `V`, `T`, `T-bar`, Brin's `A` | dead for `n >= 2` | O4 of the root (Burillo--Felipe, arXiv:2605.09763v1) |
| Central or covering lifts of groups without `(Q,+)` | dead | `lifts-add-no-unipotent-divisibility` |
| F.g. groups of finitely-piecewise maps whose pieces lie in a linear group `L` over a commutative ring, with `GL_n(Q)` acting through `L` | dead | the pieces generate a f.g. linear, hence residually finite, subgroup of `L` that contains every element that is globally in `L` (identity principle plus Mal'cev) |
| Finitary `SL_X(Q)` extended by weighted permutations, `SL_X(Q) <= Γ <= SL_X(Q)·Mon(X)` | dead if split; otherwise constrained | split ones are never finitely presented (`split-finitary-sl-q-extensions-are-not-fp`, since `K_2(Q)` is not f.g.). Finitely presented ones need `Γ/SL_X(Q)` with infinitely generated `H_3` (`fp-linear-hosts-of-sl-q-have-wild-h3-quotients`). F.g. ones need point stabilizers with non-f.g. weight characters (`weighted-monomial-hosts-of-sl-q-need-wild-stabilizers`) |
| Brin--Thompson `nV` and twisted Brin--Thompson groups | open | `(Q,+) <= nV` for `n >= 2` (Kojima--Sheng, arXiv:2603.18410v3, Thm. 4.2). Whether `BS(1,2)` or `SL_3(Z)` embeds in `nV` is not settled here; see `heisenberg-in-nv-forces-drift-free-central-element` |
| `E_N` or unit groups of natural noncommutative rings containing `Q` (e.g. Leavitt-type rings, where `M_n(L) ≅ L`) | open | the piece argument needs commutative coefficients |
| Germ extensions whose germ groups are not those of `VA` | open | the `VA` obstruction is specific to its germs |
| Automorphism groups and abstract commensurators of finitely presented groups | open | `GL_n(Q)` is the abstract commensurator of `Z^n`; untested |

## Attempts

1. **Brin's `A` by germs at infinity (second argument, source check pending).**
   This is independent of Burillo--Felipe. It assumes Brin's description of
   `A` (Publ. IHES 84, 1996): the orientation-preserving homeomorphisms of `R`
   that are piecewise linear with a discrete set of dyadic breakpoints, slopes
   powers of 2, preserve `Z[1/2]`, and commute with `x -> x+1` near `+infinity`
   and near `-infinity`. That description has not been re-read at the source.
   The argument:
   - **Germ homomorphisms.** Periodic extension of the germs gives a
     homomorphism `A -> T-bar x T-bar`. Its kernel `K` is the group of
     compactly supported elements.
   - **K has no copy of `(Q,+)`.** Let `g` in `K` be nontrivial and `a` the
     left end of its support. If `r^k = g`, then `r` fixes `a`. Comparing
     right slopes at `a` (`2^s` for `g`, with `s ≠ 0`) shows `k | s`, so only
     finitely many roots exist.
   - **Aff_+(Q).** Let `H = Q x| P` with `P <= Q^x` containing all squares
     (for example `H = Aff_+(Q)`). Then `Z(H) = 1`, and every nontrivial normal
     subgroup `N` contains the translations `Q`:
     - if `n : x -> ax+b` lies in `N` with `a ≠ 1`, then `[n, τ_c] = τ_{(a-1)c}`
       lies in `N`, so `N` contains a nontrivial translation `τ_d`;
     - conjugating `τ_d` by the squares in `P` gives `τ_{q^2 d}`;
     - every rational is a difference of two squares, so these generate all
       of `Q`.
   - **Conclusion.** Suppose `H <= A`. Then `H ∩ K = 1`. The two germ kernels
     meet trivially, so one of them is trivial and `H` embeds in `T-bar`. Also
     `H ∩ <x -> x+1> = 1`, because that subgroup is central and infinite
     cyclic. So `H` embeds in `T <= V`, which contains no `(Q,+)` (survey
     Theorem 4.4).
   - **Consequence for Aut(F).** `A` has index 2 in `Aut(F)`, so `Aff(Q) ∩ A`
     would be some `Q x| P` with `P ⊇ (Q^x)^2`. So `Aff(Q)`, and hence
     `GL_n(Q)` for `n >= 2`, is not a subgroup of `Aut(F)`. `SL_2(Q)` is
     perfect, so inside `Aut(F)` it would lie in `A`. But `A` acts faithfully
     by increasing homeomorphisms of `R`, so it is torsion-free, while `-I` has
     order 2.
2. **Candidates not yet tested:**
   - `Comm(G)` for finitely presented `G` containing `Z^n` rigidly;
   - `E_N(L)` for Leavitt-type rings over a finitely presented ring containing
     `Q`;
   - `nV` for `n >= 3`, with `SL_3(Z)` as the first test.
3. **Automorphism groups and abstract commensurators (lane gq-explicit-2,
   2026-09-17): dead except for automorphism groups of non-residually-finite
   groups and commensurators of branch-type groups.** Lane proofs, not
   independently reviewed. Details in
   `research/artifacts/gq-gq-explicit-2-aut-comm-hosts.md`.
   - `fg-automorphism-hosts-contain-no-divisible-subgroup`: `Aut(Γ)` for
     finitely generated residually finite `Γ` is residually finite, and so is
     every finitely generated group of automorphisms of a separated scheme of
     finite type over a field. So neither contains `(Q,+)`, under any embedding.
     This kills `Aut(F_k)`, `Aut(π_1 Σ_g)`, `Aut(RAAG)`, and polynomial and
     variety automorphism groups.
   - `fg-cremona-subgroups-have-arithmetic-linear-part`: in a finitely
     generated subgroup of `Bir(P^m_Q)`, the linear elements lie in
     `PGL_{m+1}(Z[1/N])`. So the natural linear `GL_n(Q)`, and every
     linearizable `(Q,+)`, lies in no finitely generated Cremona subgroup. A
     non-linearizable copy would give a non-residually-finite finitely
     generated Cremona subgroup, a negative answer to a question attributed to
     Cantat.
   - `comm-of-z-n-times-torsion-group-splits`:
     `Comm(Z^n x B) = GL_n(Q) x Comm(B)` for torsion `B` with trivial FC-centre,
     for example `B` = Grigorchuk's group, whose commensurator is Röver's group.
     Such commensurators are never finitely generated. `Comm(Z^n)`,
     `Comm(SL_n(Z))` (`n >= 3`) and `com(F)` (Burillo--Cleary--Röver) are not
     finitely generated either.
   - Still open in this row:
     - `Aut(V)`, `Aut(nV)`, `Aut(SV_G)` (normalizers of simple groups in Cantor
       homeomorphism groups, by Rubin), starting with whether `(Q,+) <= Aut(V)`;
     - finitely generated commensurators of branch or self-replicating groups
       containing `GL_n(Q)`.
