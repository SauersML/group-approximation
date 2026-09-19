---
rg: 2
id: branch-host-v-recodings-need-recurrent-residual-chains
kind: claim
title: The binary recoding of a Bishop–Schesler branch group is an annular germ host over V whose alternating scaffold commutes with the zoom, so finite presentation depends only on cross-depth recurrences among the input's residual-chain actions; free recurrences kill it, and one-step recurrences are exactly virtual endomorphisms
distinct_from:
  annular-hosts-with-free-zoom-germs-are-not-finitely-presented: that treats annular hosts whose germ group is exactly (input germs) * ⟨t⟩; this shows the Bishop–Schesler branch host recodes into an annular host whose germ group is (G-germs with t) × Alt(6), extends the kill to that shape, and identifies what a cross-depth relation means for a residual chain.
  rf-groups-have-free-product-germs-over-v: that builds annular hosts from ping-pong copies of finite quotients; this derives the annular host from the branch group itself, so the branch reduction and the annular method meet in one object.
---

**ESTABLISHED** by `branch-host-v-recoding-proof` (lane proof, elementary given the two annular
nodes of bh-free-22; not reviewed; no priority claimed). Items 1–5 are established; the open continuation (multi-depth recurrences and sufficiency) is
`residual-chains-with-finite-recurrences-give-fp-branch-hosts`.

**Setting.** `G`, `(N_n)`, `Q_n`, `X_n`, `φ_n`, `ψ_n`, `H = G × A` with `A = Alt(6)`, and
`Γ = ⟨H̃^[0], B_0⟩` are as in Bishop–Schesler (arXiv:2509.12161v2 §3). Drop finitely many levels
so that `|Q_n| ≥ 2`.

**The recoding.** Code `x, y, z, o, p, q` at every level by the fixed words
`0, 100, 101, 1100, 1101, 1110`. Code `Q_n ∖ {o}` by `1111·D_n`, for an arbitrary complete binary
prefix code `D_n` with `|Q_n| − 1` words. Concatenating codewords gives a homeomorphism
`Φ: ∂T_X → C = {0,1}^N`, which sends the spine `x_1x_2…` to `p = 0^∞`.

**Theorem.**
1. **Annular host.** `ΦΓΦ^(-1) ≤ Γ_ρ = ⟨V, ĥ : h ∈ S_H⟩`. Here `ĥ` fixes `p` and acts on the
   annulus `A_ℓ = 0^ℓ 1 C` by the element `ρ_ℓ(h) ∈ V`. On `A_ℓ ≅ C`, `ρ_ℓ(h)` permutes the
   `C_(ℓ+2)`-cylinders of `Y = 00C` by `φ_(ℓ+2)(g)` and those of `Z = 01C` by `ψ_(ℓ+2)(σ)`. The
   rooted group `B_0` lands in `V`. So `Γ_ρ` is an annular host in the sense of
   `annular-hosts-with-free-zoom-germs-are-not-finitely-presented`, V-local off the single orbit
   `V·p`.
2. **The scaffold is self-similar for free.** `ρ_ℓ((1,σ)) = e(σ)` does not depend on `ℓ`, and
   `h ↦ ĥ_p` is injective. The germ group at `p` is `(Γ_ρ)_p = ⟨Ĝ_p, t⟩ × Â_p`, with `Â_p ≅ Alt(6)`
   central and `Ĝ_p ≅ G`. Here `t` is the germ of the zoom `0w ↦ 00w`. All the depth data that
   matters is the action of `G` on its chain quotients, `ρ_ℓ(g) = φ_(ℓ+2)(g)`.
3. **Free recurrences kill finite presentation.** If `⟨Ĝ_p, t⟩ = Ĝ_p * ⟨t⟩`, then `Γ_ρ` is not
   finitely presented.
4. **Finite presentation needs a finite recurrence.** If `Γ_ρ` is finitely presented, there are
   `B` and finitely many words `u_1, …, u_r` of total `t`-exponent 0 in the `ĝ`'s and `t`, each
   with trivial germ, that pin down the chain data. Explicitly, every family of homomorphisms
   `ρ'_n: G → V_Y` agreeing with `ρ_n|_G` for `n ≤ 2B + 1` and satisfying the *recurrences*
   `ev_n(u_j; ρ') = ∏_i ρ'_(n+δ_i)(g_i) = 1` for all `n ≥ B + 2` equals `ρ|_G`.
5. **One-step recurrences are virtual endomorphisms.** Suppose some finite-index `G_1 ≤ G` and
   some `δ ≥ 1` satisfy `t^(-δ) ĝ_p t^δ ∈ Ĝ_p` for every `g ∈ G_1`. Then `ψ(g) := ` the element
   with `ψ(g)^_p = t^(-δ) ĝ_p t^δ` is an injective homomorphism `G_1 → G`, and there is `m_0` with
   `N_(m+δ) ∩ G_1 = ψ^(-1)(N_m)` for all `m ≥ m_0`. So the tail of the residual chain is generated
   by one virtual endomorphism, which is Nekrashevych's self-similar setting. This holds for every
   choice of the codes `D_n`.

**What this says.** Over Thompson-like annular hosts, the Bishop–Schesler branch reduction does
not escape the self-similar problem; it relocates it.
- The growing alphabets cost nothing, because `V` holds every finite group.
- The `Alt(6)` scaffold commutes with the zoom automatically.
- The one thing to transport across depths is the input's own residual chain.
- A finite presentation needs a finite nonabelian recurrence among the chain actions `φ_n` (item
  4). Its simplest form is a virtual endomorphism (item 5), which is exactly what the regular-tree
  route `fp-rf-boone-higman-via-fp-self-similar-overgroups` needs.
- The only room beyond self-similarity is multi-depth recurrences, where `φ_(n+2)` is built from
  `φ_(n+1)` and `φ_n` of other elements. That is the open node
  `residual-chains-with-finite-recurrences-give-fp-branch-hosts`.

**Lesson for general BH.** For the residually finite sector (BBMZ 5.3(2), (3), (7), (12)) the
branch reduction turns host design into one question about the input's residual chains: does some
chain of `G` satisfy a finite recurrence that pins its level actions down? That is a "machine-like
virtual endomorphism", with depth `n + δ` computed from depths `n, …, n + δ − 1` by a fixed finite
word. It is the residual-chain form of bh-free-22's locality principle, and of the master route's
local rigidity principle (`board/SYNTHESIS.md`). Growing alphabets, branch scaffolding and
Frattini embeddings all come free. The recurrence is the whole problem.
