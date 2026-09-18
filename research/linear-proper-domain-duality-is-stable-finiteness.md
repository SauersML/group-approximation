---
rg: 2
id: linear-proper-domain-duality-is-stable-finiteness
kind: claim
title: The linear sector of the proper-domain dual claim is exactly stable finiteness of the modular group algebras
distinct_from:
  proper-sft-domains-admit-no-dual-failures: that is the full nonlinear claim on strongly irreducible SFT domains; this settles its linear sector (group subshifts over a finite field with linear automata) in both directions, by stable finiteness of F_q[G].
  capobianco-kari-taati-dual-surjunctivity-toolkit: that shows linear decoders of one-sided inverses are post-surjective on the full shift; this works on proper linear subshifts, shows no linear post-surjective map from a proper one exists under stable finiteness, and builds a proper strongly irreducible SFT counterexample from any one-sided inverse.
  stable-finiteness-failure-is-algebraic-bernoulli-absorption: that turns a Kaplansky failure into an absorption of the full shift; this turns it into a failure of the proper-domain claim on the idempotent-image SFT, and proves the converse for linear data.
---

**ESTABLISHED (elementary; no novelty claimed for the individual steps)** by
[[linear-proper-domain-duality-is-stable-finiteness-proof]].

**Setting.** `G` is a group, `F = F_q` a finite field, `k ≥ 1`, and `A = F^k`. The shift is
`(g.x)(h) = x(g^{-1}h)`. Row vectors `u ∈ F[G]^k` are the finitely supported configurations. A `k × k` matrix
`M` over `F[G]` acts on configurations by right convolution, `(xM)_j(g) = Σ_{i,h} x_i(g h^{-1}) M_{ij}(h)`.
A *linear subshift* is a closed, shift-invariant `F`-subspace `X ⊆ A^G`. A *linear automaton* `X → A^G` is a
continuous, equivariant, `F`-linear map. Strong post-surjectivity (lifts in `X`) and pre-injectivity are as
in `strict-pairs-give-dual-failures-on-bounded-defect-domains`.

**Theorem.** For every group `G` and finite field `F`, the following are equivalent.
1. `F[G]` is stably finite: for every `k` and `k × k` matrices `M, N` over `F[G]`, `NM = I` implies `MN = I`.
2. For every `k`, no proper linear subshift `X ⊊ (F^k)^G` carries a post-surjective linear automaton
   `X → (F^k)^G`. Here post-surjective is the weak form: no bound on lifts, and no strong irreducibility or
   finite type is assumed of `X`.
3. For every `k`, every proper strongly irreducible linear SFT `X ⊊ (F^k)^G` and every linear automaton
   `X → (F^k)^G` that is strongly post-surjective with lifts in `X`, that automaton is pre-injective.
   (Vacuously, by 2.)

**The counterexample in (3) ⇒ (1).** If `NM = I ≠ MN`, put `E = MN`, an idempotent `≠ I`.
- The domain is `X = {x : x(I − E) = 0} = (A^G)E`. It is a proper, strongly irreducible linear SFT.
- The automaton is `x ↦ xM²`.
- It is strongly post-surjective, with lift `x ↦ x + (z − xM²)N²`.
- It is not pre-injective: the finitely supported `u = w(I − MN)N ≠ 0` lies in `X` and has `uM² = 0`.

**What this changes for the route `gottschalk-via-proper-domain-duality`.**
- **Linear sector.** In its linear sector, `proper-sft-domains-admit-no-dual-failures` holds for `G` exactly
  when Kaplansky's stable finiteness holds for `F_q[G]` for every `q`. That is an open problem for general
  groups. It is known for sofic groups, and for free-by-sofic groups (`free-kernel-extensions-keep-modular-stable-finiteness`).
- **Where every linear kill-test dies.** On any group with `F_q[G]` stably finite, linear test domains cannot
  refute the claim. They die at one step: post-surjectivity at the zero point forces `X_fin M ⊇ F[G]^k`, and
  hence `X = A^G`.
  - The invariant is the rank of the finitely supported module, `X_fin` inside `F[G]^k`.
  - Strong irreducibility and finite type play no role in this step.
- **Where a counterexample must live.** A counterexample to the full claim on a group with stably finite
  modular group algebras, for instance any sofic group, must be genuinely nonlinear. Arrow-type and
  bounded-defect domains are nonlinear, so they remain the only candidates.
- **The hole is at least Kaplansky-hard.** Any proof of `proper-sft-domains-admit-no-dual-failures` for all
  groups proves stable finiteness of `F_q[G]` for all groups, through (3) ⇒ (1) directly. This does not go
  through surjunctivity.
