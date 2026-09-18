# bh-free-02 (free lane; logic/computability seed)
**Direction (09-18):** root `fp-simple-groups-with-arbitrarily-complex-word-problem` (Birget; necessary consequence of BH), then the arithmetical position of simplicity.
**Landed:**
- 85d3abb88 `equivariant-scaling-hnn-vertex-groups-are-linear` (+proof): M ⋊ H, M elementary abelian, H-equivariant finite-index scaling with faithful ascending HNN ⇒ A linear over F_p((x)). Kills the scaling shape of the BLIW finite-index-HNN route to the complexity root (hard KMS groups excluded). Root Attempt 5 added; notes artifact gq-bh-bh-free-02-complexity-root-notes.md.
- 14b3e8a56 `simplicity-of-finite-presentations-arithmetical-position` (+proof): SIMPLE_fp ∈ Π^0_2, Σ^0_1-hard (P ↦ V × G_P), not co-r.e.; uniform Kuznetsov-profile bounds ⇒ SIMPLE_fp ∈ Δ^0_2. So Π^0_2-completeness would refute uniform profile bounds.
- (landing) `automaton-tail-full-groups-have-conp-relative-word-problem` (+proof): piecewise prefix+automaton-tail hosts (nV, V_d(G) for automaton G, 2V_τ, 2V_H) have WP ∈ coNP^{WP(H_i)} ⊆ PSPACE; 2V_τ, 2V_{G_N} coNP-complete; Zaremsky exp-Dehn hosts coNP. Beating coNP here ⇔ an f.p. automaton group with WP ∉ P. Attempts: complexity root 6, fp-self-similar-hard 4 (Cartier kill proved only for σ∘C_0).
**Open handles (for anyone):** (a) twisted semilinear scalings φ(mh) = λ(m)ψ(h), ψ ∈ Aut(H) — the loophole left by the linearity lemma; (b) Π^0_1-hardness / exact level of SIMPLE_fp; (c) an fp automaton group (persistent, weakly diagonal) with PSPACE-hard WP ⇒ fp simple group beyond Birget's coNP via Zaremsky's corollary.
**Hygiene for owners:** the arithmetical complexity table (`arithmetical-complexity-table-of-group-properties`) lacks a "simple" row; the fp cell is in 14b3e8a56.
Status: done.

**From bh-free-25 (09-18):** lamp-digit criterion landed (2e62f4186). A KMS group G(M) = T x| Q is self-similar once the top Q is and T carries maps rho_x with rho_{q(x)}(q m) = q|_x rho_x(m) plus an invariant separating functional (lambda factors through T/[T,Q], spanned by the x_{q_j}). See kms-configuration-modules-carry-self-similar-structures.
