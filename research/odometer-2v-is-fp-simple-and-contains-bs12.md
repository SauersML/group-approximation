---
rg: 2
id: odometer-2v-is-fp-simple-and-contains-bs12
kind: claim
title: The topological full group 2V_tau of the Katsura odometer on a product 2-graph is an F_infinity simple group containing BS(1,2) and Brin's 2V
distinct_from:
  bs12-embeds-in-brin-thompson-2v: that asks for BS(1,2) inside some nV; this puts BS(1,2) inside 2V_tau, a strictly larger Katsura-Exel-Pardo host that contains 2V, and says nothing about nV.
  renormalizable-thompson-elements-give-baumslag-solitar: that needs a renormalizable element already inside kV; here the renormalizable element is the odometer itself, native to the Katsura groupoid, and the conjugator is the baker map of 2V.
  odometer-factor-witnesses-mix-coordinates: that says an odometer-factor witness inside kV must mix coordinates; here the odometer is adjoined to 2V as a new generator, so no element of kV is claimed.
artifacts:
  - research/artifacts/gq-affq-kep-odometer-host.md
---

**ESTABLISHED** through `odometer-2v-is-fp-simple-and-contains-bs12-proof`. Lane proof, not independently
reviewed. Its inputs are verbatim theorems of X. Li (arXiv:2110.04505v2, Example ex:ZS (III)) and H. Matui
(arXiv:1210.5800v3, Theorem simple2), quoted with line numbers in the artifact. No priority is claimed: the
finiteness is an application of Li's theorem, which he states covers self-similar actions on higher-rank graphs.

**Setting.**
- `C = {0,1}^N`, `X = C × C`, and `τ` is the binary odometer: `τ(0w) = 1w`, `τ(1w) = 0τ(w)`. This is the
  Katsura–Exel–Pardo triple `A = (2)`, `B = (1)` (Exel–Pardo arXiv:1409.1107, l.577).
- `Λ` is the one-vertex 2-graph with two edges of each colour, so `Λ = F_2^+ × F_2^+` and its infinite-path space
  is `X`.
- `Z = ⟨a⟩` acts self-similarly on `Λ`: by `τ` on colour-1 edges, and on colour-2 edges by fixing each edge with
  restriction `a`. On `X` the generator acts as `τ × id`.
- `2V_τ` is the topological full group of the groupoid `I_l(Λ ⋈ Z) ⋉ X`. Concretely (proof, step B), it is the
  group of homeomorphisms of `X` which, on the rectangles `C(p_i) × C(w_i)` of some finite partition, have the form
  `(p_i x, w_i y) ↦ (p'_i τ^{n_i}(x), w'_i y)` with `n_i ∈ Z`.

**Statement.**
1. **Hosts.** Brin's `2V` (all `n_i = 0`) and `s = τ × id` lie in `2V_τ`, and `2V_τ = ⟨2V, s⟩`.
2. **Finiteness.** `2V_τ` is of type `F_∞`.
3. **Simplicity.** `2V_τ` is perfect, and it is simple.
4. **`BS(1,2)`.** Let `u(x, y_0 y) = (y_0 x, y)`. This `u` is the inverse baker map, an element of `2V`. Then
   `u s u^{-1} = s^2`, and `⟨s, u⟩ ≅ BS(1,2)`.
5. **`Q` alongside.** `(Q,+) ≤ 2V ≤ 2V_τ` (`rationals-embed-in-brin-thompson-group-2v`). Moreover `s` itself is
   infinitely divisible in `2V_τ`. The mixed-radix root tower of that node, run with base `τ` in the first
   coordinate, gives `Q_τ ≅ Q` containing `s`, and its first root is `s_1 = u^{-1} s u`.

So there is an explicit, finitely presented, simple group of Cantor-set homeomorphisms containing
`BS(1,2)`, `(Q,+)` and `2V` together. The Baumslag–Solitar gate of `aff-q-embeds-in-fp-simple-group` (H2, and H5
for `nV`) is therefore passed inside this Katsura–Exel–Pardo host.

**How the easy obstruction is avoided.** In the 1D Katsura groupoid, `τ^2` restricted to `C(0)` is conjugate to `τ`
only by the non-global bisection `0w ↦ w`: this is the Katsura relation `φ(a^2, e_0) = a`. No homeomorphism
conjugates the minimal `τ` to `τ^2`. The element `s = τ × id` has a Cantor set of minimal fibres, `s^2` has the
half-fibres, and `u ∈ 2V` matches the two families. The artifact also tests the construction against
`renormalization-return-times-tend-to-zero-adically` and `crossing-move-hierarchies-have-odd-branching`.

**Not claimed.** This does not settle `bs12-embeds-in-brin-thompson-2v`: it is not known whether `2V_τ` embeds in
any `nV`. It gives no copy of `Q ⋊ ⟨2⟩` or of `Aff(Q)`: `u` is not shown to normalize `Q_τ`.
