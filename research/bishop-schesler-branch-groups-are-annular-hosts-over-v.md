---
rg: 2
id: bishop-schesler-branch-groups-are-annular-hosts-over-v
kind: claim
title: Every Bishop–Schesler branch group embeds in a one-orbit finite germ extension of Thompson's V, as an annular host whose germ group at the spinal point contains G × Alt(6) faithfully
requires:
  - efrf-groups-frattini-embed-in-efrf-branch-groups
distinct_from:
  efrf-groups-frattini-embed-in-efrf-branch-groups: that imports the branch host Γ_G on a spherically homogeneous tree with growing alphabets; this recodes that tree into the binary Cantor set and identifies ⟨V, Γ_G⟩ as an annular host at one rational point.
  rf-groups-have-free-product-germs-over-v: that builds annular hosts directly from finite quotients in ping-pong position; this shows the Bishop–Schesler groups themselves are annular hosts, with the tree's spinal data as annular data.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed). Source: Bishop–Schesler,
arXiv:2509.12161v2, TeX `arxiv_v2.tex` (sha256 prefix 941f1e1a112d3ad6), §3–4, read at source.

**Setting (theirs).** `G` fg, `(N_n)` a residual chain, `Q_n = G/N_n`,
`X_n = Q_n ⊔ {x_n, y_n, z_n, p_n, q_n}`, `H = G × A` with `A = Alt(6)`.
`Γ = ⟨H̃, B_0⟩ ≤ Aut(T_X)`, where `B_0` is the rooted `Alt(X_1)` and each `h̃ = (g,σ)~`
fixes level 1, has section `h̃^{[1]}` at `x_1`, the rooted `φ_2(g)` at `y_1`, the rooted
`ψ_2(σ)` at `z_1`, and the identity elsewhere (their l.467–485), recursively along the ray
`x^∞ = x_1 x_2 ⋯`.

**Theorem.** Choose complete binary prefix codes `c_n` of `X_n` with `c_n(x_n) = 0`, and let
`κ: ∂T_X → C = {0,1}^N` send `v_1 v_2 ⋯` to `c_1(v_1) c_2(v_2) ⋯`. Then:
1. `κ` is a homeomorphism with `κ(x^∞) = 0^∞ =: p`.
2. `κ B_0 κ^{-1} ⊂ V`, and every `κ h̃ κ^{-1}` fixes `p`, is V-local off `p`, and preserves each
   annulus `A_n = 0^n 1 C` (n ≥ 0), acting there by the element `r_n(h) ∈ V` that applies
   `φ_{n+2}(g)` (resp. `ψ_{n+2}(σ)`) to the next code block inside the cone of
   `c_{n+1}(y_{n+1})` (resp. `c_{n+1}(z_{n+1})`).
3. `E_G := ⟨V, κΓκ^{-1}⟩ = ⟨V, κH̃κ^{-1}⟩` is an annular host at `p` in the sense of
   `annular-hosts-with-free-zoom-germs-are-not-finitely-presented`, with annular data
   `r_n: H → V` factoring through `Q_{n+2} × A`, and a finite germ extension of `V` with one
   singular orbit `V·p`.
4. Its germ group at `p` is `⟨t, Ĥ⟩` (`t` the zoom germ), and `h ↦ ĥ` is injective. So
   `G × A` embeds in the germ group.

**Proof.**
1. Every infinite binary word parses uniquely, block by block, into code words of
   `c_1, c_2, …`. The parse is continuous both ways.
2. A level-`n` rooted automorphism becomes a prefix replacement `κ(v)u ↦ κ(σv)u`, because
   both cones carry the same tail code `c_{n+1}c_{n+2}⋯`. A point `q ≠ x^∞` lies in a cone
   `x^ℓ d` with `d ≠ x_{ℓ+1}`, on which `h̃` acts finitarily: at most one more code block is
   rewritten. So `h̃` is V-local at `κ(q)`. It preserves the cones `x^ℓ d`, i.e. the annuli.
3. This follows from items 1–2. The singular points of products lie in `V·p`.
4. Germs at `p` of words in `V ∪ κH̃κ^{-1}` are products of `V`-germs at orbit points
   (which conjugate back to powers of `t`) and `Ĥ`-germs at `p`. `ĥ` has trivial germ iff
   `φ_n(g) = 1` and `ψ_n(σ) = 1` for all large `n`, iff `g ∈ ⋂N_n = 1` and `σ = 1`.
   (`φ_n(g) = 1` forces `λ_n(g) = 1` by their (def:phi_k).)

**Consequence.** The Bishop–Schesler reduction (BH for all `EFRF^+` groups, hence BBMZ 5.3(2),
(3), (7), (12), follows from BH for these branch groups) lands exactly on one-point annular
hosts over `V`. There the known theory applies:
- `annular-hosts-with-free-zoom-germs-are-not-finitely-presented`: window lemma and local
  rigidity;
- `fp-germ-extensions-of-locally-moving-bases-have-fp-germ-groups`: fp host ⇒ fp germ group;
- `dynamically-v-separated-groups-satisfy-boone-higman`: the positive ascending case.

## Lesson for general BH

Growing alphabets buy nothing against Thompson-type hosts. A binary recoding with
`c_n(x_n) = 0` turns any spinal branch group into an annular host at one rational point. Its
spinal data becomes annular data, so the whole question moves to the germ group at `p`. The
branch route and the one-point germ route are the same problem. See
`depth-disjoint-spinal-hosts-have-wreath-germ-groups` and `fp-annular-germ-groups-are-hnn-recursive`.
