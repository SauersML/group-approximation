---
rg: 2
id: finitary-perturbations-give-isolated-quotients
kind: claim
title: Finitary perturbations of a faithful action of a torsion-free group never produce a new quotient, but finitary perturbations of a highly transitive finitely presented quotient produce isolated quotients as close to the group as that quotient
requires:
  - finitary-symmetric-extensions-of-oligomorphic-actions-are-fp
  - fp-groups-with-a-locally-moving-simple-subgroup-are-isolated
  - limits-of-isolated-groups-basic-closure
distinct_from:
  finitary-symmetric-extensions-of-oligomorphic-actions-are-fp: that proves FSym(S) semidirect P is finitely presented; this uses it to manufacture isolated QUOTIENTS of a given group, as needed for Cornulier--Guyot--Pitsch Question 1.
  fp-groups-with-a-locally-moving-simple-subgroup-are-isolated: that is the isolatedness criterion; this is a construction of groups meeting it that are quotients of a prescribed input.
  every-decidable-group-is-a-limit-of-isolated-groups: that is the open question; this is a mechanism for proving it at a given input, with its rigidity limit.
---

**ESTABLISHED** (lane proof below, elementary modulo the two landed nodes it cites, not reviewed;
no priority claimed).

Notation: `Sym(S)` all permutations of an infinite set `S`, `FSym(S)` the finitary ones,
`π: Sym(S) → Sym(S)/FSym(S)`. Let `G = ⟨s_1, …, s_d⟩`.

**1. Rigidity.** Let `ρ: G → Sym(S)` be an action with `ρ(G) ∩ FSym(S) = 1` and `ρ` injective (for
example `ρ` faithful and `G` torsion-free, since `ρ(G) ∩ FSym(S)` is locally finite). Let
`σ_1, …, σ_d ∈ FSym(S)` be such that `s_i ↦ σ_i ρ(s_i)` extends to a homomorphism `ψ: G → Sym(S)`.
Then `ψ` is injective and `ψ(G) ∩ FSym(S) = 1`. So finitary perturbation of such an action gives
back `G`: it never produces a proper quotient, and never produces a finitary element.

**2. Construction.** Let `G` be finitely presented and `P = G/M` a finitely presented quotient
(`M` finitely normally generated), with an action `ρ: P → Sym(S)` such that
- (a) `P` has finitely many orbits on injective 4-tuples of `S`;
- (b) the setwise stabilizers `P_{{x,y}}` are finitely generated;
- (c) every nontrivial element of `P` moves infinitely many points.

Let `σ_1, …, σ_d ∈ FSym(S)` be such that `s_i ↦ σ_i ρ(s̄_i)` defines a homomorphism
`ψ: G → Sym(S)` whose image `Q` contains `Alt_fin(S)`. Then:
- (i) `Q` is an isolated quotient of `G`;
- (ii) every word in the `s_i` that is nontrivial in `P` is nontrivial in `Q`, and every word
  trivial in `G` is trivial in `Q`. So `Q` is at least as close to `G` in the space of marked
  groups as `P` is;
- (iii) consequently, if such data exist with `P` arbitrarily close to `G`, then `G` is a limit of
  isolated groups.

Sufficient condition for `Q ⊇ Alt_fin(S)`: `Q` primitive on `S` and `ψ(M) ≠ 1`. This is
Wielandt's theorem that an infinite primitive permutation group containing a nonidentity finitary
permutation contains `Alt_fin(S)` (classical; cited, not re-read here). By item 1, `ψ(M) ≠ 1` can
only happen because `P` is a proper quotient: the finitary part `Q ∩ FSym(S)` is exactly `ψ(M)`.

**Proof.**
1. `π∘ψ` and `π∘ρ` agree on the generators, hence on `G`. `ker(π∘ρ) = ρ^{-1}(FSym(S)) = 1`, so
   `π∘ψ` is injective. Hence `ψ` is injective and `ψ(G) ∩ FSym(S) ≤ ψ(ker(π∘ψ)) = 1`.
2. Every generator `σ_i ρ(s̄_i)` lies in the subgroup `H = FSym(S)·ρ(P)` (`FSym(S)` is normal in
   `Sym(S)`), so `Q ≤ H`. By (c), `ρ` is faithful and `ρ(P) ∩ FSym(S) = 1`, so `H ≅ FSym(S) ⋊ P`,
   which is finitely presented by `finitary-symmetric-extensions-of-oligomorphic-actions-are-fp`
   (hypotheses (a), (b), and `P` finitely presented). Since `π(Q) = π(ρ(P))`, `Q·FSym(S) = H`, so
   `[H : Q] = [FSym(S) : Q ∩ FSym(S)] ≤ [FSym(S) : Alt_fin(S)] = 2`. A finite-index subgroup of a
   finitely presented group is finitely presented, so `Q` is. `Q ≤ Sym(S)` acts faithfully and
   contains `Alt_fin(S)`, so `Q` is isolated by
   `fp-groups-with-a-locally-moving-simple-subgroup-are-isolated` (case (fin)). This is (i); `Q`
   is a quotient of `G` because `ψ` is a homomorphism defined on `G`.
   For (ii): if `w(s̄) ≠ 1` in `P`, then `π(ψ(w)) = π(ρ(w(s̄)))`, and `ρ(w(s̄))` moves infinitely
   many points by (c), so it is not finitary and `ψ(w) ≠ 1`. Words trivial in `G` are trivial in its
   quotient `Q`. Item (iii) is item 4 of `limits-of-isolated-groups-basic-closure`.
3. For the sufficient condition: `Q ∩ FSym(S) = ψ(ker(G → P)) = ψ(M)` because
   `π∘ψ` factors through `P` injectively (as in 1, with `ρ` on `P`). If `ψ(M) ≠ 1` and `Q` is
   primitive, Wielandt's theorem gives `Alt_fin(S) ≤ Q`.

**Use for `BS(2,3)`.** By item 1, no faithful action of `BS(2,3)` (torsion-free) can be perturbed
into an isolated quotient. The construction needs a finitely presented proper quotient `P` of
`BS(2,3)`, close to it, with an action satisfying (a)--(c) (in particular finitely many orbits on
pairs, a type (A)-like action of `P`), and a finitary cocycle `σ` realizing the relation
`τ α^2 τ^{-1} = α^3` exactly while making a relator of `M` act as a nonidentity finitary
permutation. A simple way to keep the relation: `σ_a = 1` and `σ_t` a finitary permutation commuting
with `ρ(ā)^3`, for example `ρ(ā)^3` restricted to one finite cycle of `ρ(ā)^3`. Whether such `P` exist
is open; it is recorded on `every-decidable-group-is-a-limit-of-isolated-groups`.
