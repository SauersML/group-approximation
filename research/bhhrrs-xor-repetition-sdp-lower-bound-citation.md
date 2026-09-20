---
rg: 2
id: bhhrrs-xor-repetition-sdp-lower-bound-citation
kind: route
title: Import Theorems 1.2 and 4.10 and Figure 1 of Barak--Hardt--Haviv--Rao--Regev--Steurer, Rounding Parallel Repetitions of Unique Games (FOCS 2008)
target: bhhrrs-xor-repetition-sdp-lower-bound
requires: []
---

This is a literature import, and credit is the authors' in full. The quotations
are from text extracted with `pypdf` on 2026-09-19 from
`dsteurer.org/paper/roundpar.pdf` (the 6-page FOCS 2008 version). Line breaks
are undone and symbols transcribed.

* **Abstract.** "we prove that for every ℓ ∈ N, if sdpval(G) > 1 − δ, then
  val(G^ℓ) > 1 − √(sℓδ). Here, G^ℓ denotes the ℓ-fold parallel repetition of
  G, and s = O(log(k/δ)), where k denotes the alphabet size of the game. For
  the special case where G is an XOR game (i.e., k = 2), we obtain the same
  bound but with s as an absolute constant."
* **Theorem 1.2.** "For every ℓ ∈ N and every XOR game G with
  sdpval(G) > 1 − δ, we have val(G^ℓ) > 1 − 4√(ℓδ)."
* **Theorem 4.10.** "For every ℓ ∈ N and every unique game G with
  sdpval(G) > 1 − δ, we have val(G^ℓ) > 1 − 2√(2sℓδ), where … s = 2 if G is
  an XOR game (i.e., k = 2)". Its proof for XOR games applies Lemma 4.7:
  "Let k = 2 and let {u_i} be a feasible solution of the SDP in Figure 1.
  Then, there exists a distributional strategy {X_u} such that for every triple
  (u, v, π), H²(π.X_u, X_v) ≤ 2 · Σ_i ½‖u_i − u_π(i)‖²."
* **Figure 1.** "Maximize E_(u,v,π)∼G Σ_(i∈[k]) ⟨u_i, u_π(i)⟩ (4) Subject to
  Σ_(i∈[k]) ‖u_i‖²₂ = 1 (u ∈ V) (5) ⟨u_i, u_j⟩ = 0 (u ∈ V, i ≠ j ∈ [k])
  (6)". The second vector in (4) is the one attached to `v`; the caption reads
  "the objective function can be equivalently written as
  1 − ½ E_(u,v,π)∼G Σ_(i∈[k]) ‖u_i − u_π(i)‖²₂".
* **Games (Section 3.1).** "We represent a unique game G as a distribution
  over triples (u, v, π) … We say that a game is a two-prover game if the
  supports of the first and second component are disjoint. Our results all
  hold for general (not necessary two-prover) unique games". The ℓ-fold
  repetition "corresponds to the ℓ-fold product of the distribution G".

**Reading.** The target uses Theorem 1.2 verbatim, with Figure 1 as the
definition of `sdpval`. The "standard feasible point" in the target is checked
directly. `<u_1, u_2> = (1 − ||x_u||²)/4 = 0`, `||u_1||² + ||u_2||² = 1`, and
`Σ_i <u_i, v_π(i)>` equals `(1 + <x_u, x_v>)/2` for the identity and
`(1 − <x_u, x_v>)/2` for the swap. Theorem 1.3 of the paper, the asymptotic
bound `val∞ ≥ 1 − 2δ`, is proved only in the full version and is **not**
imported.
