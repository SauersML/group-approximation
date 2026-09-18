---
rg: 2
id: finite-commutator-wachter-weiss-groups-are-not-fp-proof
kind: route
title: Restrict to the encoding subtree; the kernel is a power of the finite commutator group; the reduction group sees only the adder there, so Bieri–Strebel applies to it
target: finite-commutator-wachter-weiss-groups-are-not-fp
requires: []
---

Notation as in the claim. `W = {■0, ■1}`. Line references are to `gq/src/ww/pspace.tex`
(arXiv:1906.03424v3).

**Corrected 2026-09-18.** The first version asserted `ρ(G_R) = <c>`. It overlooked the
intermediate check-mark states, which are generators of `G_R`. Step 1 below now
computes `ρ(G_R)` and `ρ(H_R)` separately; steps 2 and 3 are unchanged in substance.

## Facts from the construction

- **(W1) Which states change letters** (l. 1313 and the figures of
  `prop:TMmode`).
  - In `T'`, the symbols `#`, `$` and `γ ∈ Γ` are never changed, and digits are
    either kept or toggled.
  - The only toggling transitions of `T'` are in the check-mark automaton
    (Figure `fig:checkmarkingAutomaton`, l. 955–963): `checksub` (`0/1`, `1/0`) and
    `S4` (`1/0`, `0/1`).
  - The other check-mark states `S2`, `S3`, `skip` and all checker states have only
    `0/0`, `1/1` digit transitions (checked in the figures, l. 900–1100). The other
    toggles in the file are the adding-machine example (l. 345), the encoding
    description (l. 1351) and the automata for `R` (l. 1482, 1688).
  - The copies `checksub{g}` act identically before the first `$`, and after it pass to
    `g`.
  - `T_2` reads encodings over `W` and never outputs a letter outside `W` on
    `W`-input.
- **(W2) Letters outside `W`.** On a letter `a ∈ Σ̃`, every TM-mode state and every
  delayed-`R` state outputs `a` and passes to `id`.
  - This is the missing-transition convention of `T'` (an implicit `a/a` transition to
    `id`, proof of `prop:TMmode`), which the encodings `T_2` and `R_0` (l. 1768ff.)
    inherit.
  - Fact `fct:malformedWords` (l. 1417) records the result for the checking
    sequences.
  - The copies `T_{2,r}` replace the place-holder `r` by the `R`-state `r` (l. 1766).
- **(W3) The commutator mode.** `R` acts on the first letter only, by a permutation of
  `Σ̃` fixing `W`, and passes to `id`.

## 1. The restriction to W^* and its kernel

- **`W^*` is invariant.** By (W1)–(W3), every state maps `W`-letters to `W`-letters.
  So `W^*` is invariant, and restriction gives `ρ: G_R -> Aut(W^*)`.
- **What each state does on `W^*`.**
  - The `R`-states, the `R_0` states and all checker states act trivially: the checker
    states output their input by (W1), and `R` fixes `W`.
  - The check-mark states and their encoding states act, in every copy, as the
    corresponding states of the encoded check-mark automaton with `g` read as `id`. The
    `R`-state `g` reached after `$` fixes `W`-letters.
  - Hence `ρ(G_R) = C`, the automaton group of that automaton, and
    `ρ(H_R) = <ρ(checksub)> = <c>`.
- **`c` has infinite order.** On the encoded one-configuration words `0^k γ`, `c` acts as
  the binary adding machine on the `k`-digit block. So it has orbits of size `2^k` for
  every `k`.
- **`C` is not cyclic.**
  - `skip ∈ C` is nontrivial: on `γ # 0 γ'` it increments the second block.
  - `skip` fixes every word containing no `#`. On such words it reads `Γ ∪ {0}` by the
    identity, sends `1` to `id`, and after `$` meets an `R`-state or `id`, which fix
    `W`-letters.
  - If `C = <t>`, write `c = t^m` and `skip = t^n` with `m, n != 0`. Then
    `skip^m = c^n`. But `c^n` moves some `0^k γ` with `2^k > |n|`, and `skip^m` fixes it.
    This is a contradiction.
- **The kernel is a power of `R`.**
  - Let `K = ker ρ`, take `g ∈ K`, and write a point not in `W^N` as `u a v` with
    `u ∈ W^*` and `a ∈ Σ̃`. Then `g(u a v) = u · g|_u(a v)`.
  - By (W2) and (W3), each state in the product `g|_u` outputs on `a` a letter in the
    `R`-orbit of `a` and passes to `id`. So `g|_u(a v) = π_u(g)(a) v` for some
    `π_u(g) ∈ R`.
  - Because `g` fixes `u`, `(gh)|_u = g|_u h|_u` for `g, h ∈ K`. So
    `g ↦ (π_u(g))_{u ∈ W^*}` is a homomorphism `K -> R^{W^*}`. It is injective, because
    `g` fixes `W^N` and every other point has the form `u a v`.
- **`K` is locally finite.** The unrestricted power of a finite group lies in the
  variety it generates, which is locally finite.

## 2. The kernel of the reduction group is infinite

Let `z` be the encoded format-checking state of `T'`, in the copy where `r` is an
`R`-state `ρ_0 != 1`. It loops on `0/0`, on `id_Γ` and on `#` (through its second
state), sends every `1` to `id`, and passes to `r` after `$`. Let `e = checksub{id}`.
Both are initial states, so they lie in `H_R`.

- **`z` lies in the kernel.** `z ∈ K ∩ H_R`. Also `π_w(z) = ρ_0` exactly for
  `w = u$` with `u` well formed and all digit blocks zero; otherwise `π_w(z) = 1`.
- **Conjugating by powers of `e`.** Every section of every power of `e` is a TM-mode
  state or `id`, and these output each `Σ̃`-letter unchanged and pass to `id`. The copy
  `checksub{r}` would be unsuitable, since it passes to an `R`-state after `$`.
  - So for `h = e^n` and `w ∈ W^*`, `h^{-1}(w a v) = h^{-1}(w) a v`.
  - Hence `π_w(h z h^{-1}) = π_{h^{-1} w}(z)`, and the support of `e^n z e^{-n}` is
    `e^n(supp z)`.
- **The supports differ.** Fix `γ ∈ Γ` and `k`.
  - On the `e`-invariant set of encoded single-block words `x γ $` with `k` digits, `e`
    acts as the adding machine on `x`.
  - The only element of that set in `supp z` is `0^k γ $`.
  - So `e^n(supp z)` meets the set exactly in `revbin_k(n) γ $`.
- **Conclusion.** The conjugates `e^n z e^{-n}`, `0 <= n < 2^k`, have pairwise distinct
  supports, so they are pairwise distinct. As `k` is arbitrary, `K ∩ H_R` is infinite.

## 3. The reduction group is not finitely presented

- **Setup.** Suppose `G` is finitely presented, with `χ: G ->> Z` and `ker χ` locally
  finite. By the Bieri--Strebel theorem (cited: Bieri--Strebel 1978; see also Brown's
  account through Σ-invariants), `G` is an HNN extension `<B, t | t A t^-1 = A'>`
  with `B` finitely generated and `A, A' <= B <= ker χ`.
- **The base is finite.** `B` is finitely generated and locally finite, so it is
  finite, and `|A| = |A'|`.
- **Case `A = B`.** Then `A' = B`, and `G = B ⋊ <t>` is virtually `Z`.
- **Case `A != B`.** The Bass--Serre tree is locally finite, of degree
  `[B:A] + [B:A'] >= 4`. The stabilizers are finite and the action is cocompact, so
  `G` is virtually free of rank at least 2 and contains `F_2`. That is impossible,
  since `G` is locally-finite-by-`Z` and hence amenable.
- **Conclusion.** So `G` is virtually cyclic. Apply this to `H_R` with
  `χ = ρ|_{H_R}`, whose kernel `K ∩ H_R` is locally finite (step 1) and infinite
  (step 2). The result is a contradiction, so `H_R` is not finitely presented.

## 4. Hardness of H_R

Wächter--Weiß's reduction outputs the balanced iterated commutator `q` of the checking
sequences `p_{i,r}` and of the delayed `R_0`-elements. All of these are words in the
initial states (proof of `thm:nonuniformPSPACE`, l. 1760–1960). So `q ∈ H_R`, and the
PSPACE-hardness of `WP(G_R)` on these inputs is PSPACE-hardness of `WP(H_R)`. The upper
bound is the `PSPACE` bound for automaton groups. `∎`
