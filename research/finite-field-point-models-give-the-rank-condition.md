---
rg: 2
id: finite-field-point-models-give-the-rank-condition
kind: claim
title: A skew group ring over a commutative ring has the rank condition when its coefficients admit approximately equivariant finite-field point models, so Möbius and projective linear substitutions and Bernoulli fields over sofic groups give no rank failure, and bi-orderable groups give none with any twist
distinct_from:
  field-crossed-product-rank-condition-survival-cases: that uses Følner counts, finite Galois quotients, or an invariant measure on complex embeddings; this evaluates coefficients at points over finite fields along finite or sofic permutation models, which exist for Möbius substitutions (no invariant complex measure) and in characteristic p (no trace).
  rank-condition-rings-have-weakly-finite-images: that characterizes the rank condition abstractly by weakly finite images; this builds explicit rank-metric matrix models over finite fields from point evaluations.
  char-zero-steinberg-stably-finite-iff-invariant-measure: there the coefficients are locally constant functions and approximately equivariant points would push the counting measure to an invariant measure; here the points live over finite fields of growing size and no measure on complex points is produced.
---

Let `K` be a commutative ring, `σ: G -> Aut(K)` an action, and `R = K ⋊ G` the skew group ring (`α = 1`).

**Definition (finite-field point model).** Fix finite `E ⊆ K`, finite `W ⊆ G` containing `e`, and `ε > 0`. A
point model consists of:
- a finite set `V`, a finite field `F` and a map `σ: W -> Sym(V)`;
- for each `w ∈ V` a subring `O_w ⊆ K` and a unital ring homomorphism `e_w: O_w -> F` (possibly undefined, that
  is `O_w = ∅`, for some `w`);
- a set `V_good ⊆ V` with `|V_good| >= (1-ε)|V|` such that for all `v ∈ V_good`, `h, h' ∈ W`, `b ∈ E`:
  - (P1) `E ⊆ O_(σ(h)^(-1)v)` and `σ_h(E) ⊆ O_v`;
  - (P2) `e_(σ(h)^(-1)v)(b) = e_v(σ_h b)`;
  - (P3) `σ(h')^(-1) σ(h)^(-1) v = σ(hh')^(-1) v` whenever `hh' ∈ W`, and `σ(e)v = v`.

`K` has **finite-field point models over `G`** if point models exist for every `E`, `W`, `ε`.

**ESTABLISHED 2026-09-17** by [[finite-field-point-models-give-the-rank-condition-proof]].

**(A) Rank certificate.** If `K` has finite-field point models over `G`, then `K ⋊ G` has the rank condition:
`AB = I_d` with `A` of size `d x r` and `B` of size `r x d` forces `r >= d`. The rank condition passes to unital
subrings, so it also holds for `K' ⋊ G` for every `G`-stable subring `K' ⊆ K`.

**(B) Examples with point models.**
1. **Bernoulli fields over sofic groups, any characteristic.** For `G` sofic, any field `k` and any index set `I`,
   `K = k(x_(g,i) : g ∈ G, i ∈ I)` with `h·x_(g,i) = x_(hg,i)`. The models evaluate `x_(g,i)` at random values
   of a large finite field along a sofic approximation.
2. **Projective linear substitutions, any group.** For any field `k`, any `n` and any `G` acting on
   `k(x_1..x_n)` through `PGL_(n+1)(k)`, points of `P^n(F_Q)` on no low-degree hypersurface over the residue
   field form an exact finite model. This includes every action on `k(x)` by `k`-automorphisms, in particular
   `Q(x) ⋊ PSL_2(Z)` by Möbius substitutions.

**(C) Bi-orderable groups, any twist.** If `G` is bi-orderable, every crossed product `K*G` over a commutative
field, with any `σ` and cocycle `α`, has the rank condition. It embeds in a Malcev–Neumann series division ring
(imported). Examples are free groups, surface groups, right-angled Artin groups and torsion-free nilpotent groups.

**Consequences for `some-field-crossed-product-fails-the-rank-condition`.**
- The Möbius test case `Q(x) ⋊ PSL_2(Z)`, and every action on `k(x)` by `k`-automorphisms, has the rank condition.
- The test case `F_p(x_g) ⋊ G` has the rank condition for sofic `G`.
- No crossed product over a bi-orderable group is a witness. With
  `twisted-linear-profile-deficits-are-rank-condition-failures`, twisted linear profiles give no Rokhlin deficit
  over `F_2`. So a small-`Phi` profile over `F_2` must be nonlinear.
- A witness now needs a nonamenable, non-bi-orderable group, and either a nontrivial cocycle or a coefficient
  `G`-ring with no finite-field point models. The latter holds, for example, for Bernoulli fields over a nonsofic
  group. The ternary Leavitt route (`α = ±1`) is untouched.

**Calibration.**
- A paradoxical boundary action `F_2 ↷ X` makes the Steinberg algebra `LC(X,k) ⋊ F_2` fail the rank condition
  (`char-zero-steinberg-stably-finite-iff-invariant-measure`), so (A) forbids point models there. The definition
  fails for the right reason.
- Point homomorphisms `LC(X,k) -> F` are evaluations at points `x_w ∈ X`, and (P2) on the indicators of a
  paradoxical decomposition says the counting measure on `w ↦ x_w` is `ε`-invariant on those clopens.
- The same counting contradicts the paradox exactly as in the Følner case.
- For fields, the points `e_w` take values in finite fields. No measure on `Emb(K_0, C)` is ever produced, which
  is why the Möbius case escapes survival case (c) but not (A).
