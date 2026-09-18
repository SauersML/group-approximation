---
rg: 2
id: depth-disjoint-spinal-hosts-have-wreath-germ-groups
kind: claim
title: With depth-disjoint binary codes, the annular host of a Bishop–Schesler branch group has germ group (G × Alt(6)) ≀ Z, so it is never finitely presented
requires:
  - bishop-schesler-branch-groups-are-annular-hosts-over-v
  - fp-germ-extensions-of-locally-moving-bases-have-fp-germ-groups
distinct_from:
  annular-hosts-with-free-zoom-germs-are-not-finitely-presented: that kills hosts whose germ group is (input) * ⟨t⟩, via the window lemma; here different depths commute, the germ group is the restricted wreath product H ≀ Z, and the kill is Baumslag's wreath-product theorem plus germ localization.
  rf-groups-have-free-product-germs-over-v: that places finite quotients in ping-pong position (germ group G * Z); this places them depth-disjointly (germ group H ≀ Z), the opposite extreme.
---

**ESTABLISHED** (lane proof, elementary given the cited inputs; not reviewed; no priority claimed).

**Setting.** Notation of `bishop-schesler-branch-groups-are-annular-hosts-over-v`, with
`H = G × A` and `G` infinite. Refine the residual chain so that `|Q_{n+1}| ≥ 2n + 1`.
In annulus coordinates `A_n = 0^n 1 C`, write `c_{n+1}(d) = 1 c'_{n+1}(d)` for `d ≠ x_{n+1}`,
and choose the codes to be **depth-disjoint**:
- `c'_{n+1}(y_{n+1}) = 1^{2n} 0 0` and `c'_{n+1}(z_{n+1}) = 1^{2n} 0 1`;
- the remaining `|Q_{n+1}| + 2` letters fill the `2n + 1` cones `1^j 0 C` (`j < 2n`) and `1^{2n+1} C`
  by a complete prefix code. This is possible by the size assumption.

**Theorem.** The germ group of `E_G = ⟨V, κΓκ^{-1}⟩` at `p = 0^∞` is isomorphic to the restricted
wreath product `H ≀ Z`, with `t` generating `Z`. Hence `E_G`, and its full closure, are not
finitely presented.

**Proof.**
- `r_m(h)` is supported in `U_m := 1^{2m} 0 C ⊂ C`, and the `U_m` are pairwise disjoint.
  `t^δ ĥ t^{-δ}` acts on `A_n` by `r_{n+δ}(h)`, supported in `U_{n+δ}`. So conjugates with
  different `δ` commute. The map `⊕_{δ∈Z} H → ∏_n V / ⊕_n V`, `(h_δ) ↦ (∏_δ r_{n+δ}(h_δ))_n`,
  is a homomorphism equivariant for the shift.
- It is injective. If `h_δ = (g,σ) ≠ 1`, then `ψ(σ) ≠ 1` at every depth, or `φ_{n+δ+2}(g) ≠ 1`
  for all large `n` since the chain is residual. Disjoint supports prevent cancellation.
- So `⟨t, Ĥ⟩ ≅ (⊕_Z H) ⋊ ⟨t⟩ = H ≀ Z`. By item 4 of the parent node, this is the whole germ
  group.
- Baumslag (Math. Z. 75, 1961, cited, not re-read): a restricted wreath product `H ≀ K` with
  `H ≠ 1` is finitely presented only if `K` is finite. So `H ≀ Z` is not finitely presented.
- `E_G ⊇ V`, and each element has finitely many singular points. If `E_G` were finitely
  presented, `fp-germ-extensions-of-locally-moving-bases-have-fp-germ-groups` (base `V`)
  would make its germ groups finitely presented. Contradiction. The same argument applies to
  the full closure, which has the same germ group.

## Lesson for general BH

Storing a residual chain one finite quotient per depth is exactly a lamp at each depth. With
disjoint supports the germ group is the lamplighter `H ≀ Z`, which is never finitely presented.
With interleaved supports it is `H * Z`-like, and `annular-hosts-with-free-zoom-germs-are-not-finitely-presented`
kills it. Neither extreme can host a Bishop–Schesler group. A finitely presented host must
supply a genuine **cross-depth transport**: some depth-`n+1` data must be a fixed V-word in
depth-`n` data. `fp-annular-germ-groups-are-hnn-recursive` makes this precise.
