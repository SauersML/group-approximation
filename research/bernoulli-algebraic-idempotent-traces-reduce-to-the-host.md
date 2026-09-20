---
rg: 2
id: bernoulli-algebraic-idempotent-traces-reduce-to-the-host
kind: claim
title: Over every torsion-free host, the trace of an algebraic idempotent over C[F_p wr_G G] is the host trace of its lamp-augmentation plus the cylinder trace of its rank expansion, so algebraic trace witnesses at the Bernoulli coefficient are exactly the host's
distinct_from:
  kun-thom-actor-algebraic-idempotents-pass-trace-test: that bounds traces of algebraic idempotents over the Kun--Thom actors by pushing to congruence quotients; this handles the lamplighter F_p wr_G G over an arbitrary torsion-free host, with no residual finiteness, by rank counting on finite-support configurations.
  bernoulli-bc-splits-into-host-and-cylinder-comparison: that supplies the trace detector Z[1/p]; this shows that the detector never fires on classes coming from algebraic K_0 of the group ring beyond the host part.
  delocalized-gapped-bernoulli-kernels-vanish-at-marked-expanders: that kills one C*-construction (gapped kernels delocalized on marked expanders); this kills every algebraic construction at once, for every invariant measure, and leaves only non-algebraic C*-classes.
  bernoulli-pattern-expansions-are-finite: that proves locality of ranks of C*-classes by Combes--Thomas; this needs no analysis, because algebraic diagonals are exact window functions, and it computes traces, not ranks.
---

**ESTABLISHED** by `bernoulli-algebraic-idempotent-traces-reduce-to-the-host-proof` (unreviewed).

**Setting.**
- `G` is countable and torsion-free, `Λ = Z/p`, `X = Λ^G`, `H = F_p wr_G G = (⊕_G F_p) ⋊ G`.
- Fourier transform identifies `C[⊕_G F_p]` with the algebra `C_lc(X)` of functions depending on finitely many
  coordinates, so `C[H] = C_lc(X) ⋊_alg G` and `C*_r H = C(X) ⋊_r G`. The canonical trace of `C*_r H` is
  `τ(b) = ∫_X tr E(b) dμ` with `μ` the Haar (uniform Bernoulli) measure.
- `ev_0 ⋊ G : C[H] -> C[G]` is the quotient by the lamp augmentation ideal, with splitting `s : C[G] -> C[H]`.
- For a `G`-invariant Borel probability measure `ν` on `X`, `τ_ν(b) = ∫ tr E(b) dν` is a trace on `C(X) ⋊_r G`.
- Ranks `r_x`, pattern coefficients `n(y)` and the comparison `T_r` are those of
  `bernoulli-assembly-injective-beyond-the-host` (RF).

**Theorem.** Let `e ∈ M_k(C[H])` be an idempotent and `e_0 = (ev_0 ⋊ G)(e) ∈ M_k(C[G])`. Put
`y = [e] - [s(e_0)] ∈ K_0(C_0(X \ {0}) ⋊_r G)`.
1. **Exact window.** `F = tr E(e) - tr E(s(e_0))` depends only on `x|_W` for a finite `W ⊆ G`, and `F(0) = 0`.
2. **Traces are determined by ranks.** `n(y)` is finitely supported and, for every invariant probability measure `ν`,
   `τ_ν(y) = Σ_([s]) n_([s])(y) ν(C_s) = τ_ν(T_r(n(y)))`.
3. **Haar trace.** `τ(e) = τ_G(e_0) + Σ_([s]) n_([s])(y) p^(-|F_s|)`. So `τ(e) ∈ Z[1/p]` iff `τ_G(e_0) ∈ Z[1/p]`.
4. **Reduction (both directions).** `τ(K_0(C[H])) ⊆ Z[1/p]` holds iff `τ_G(K_0(C[G]) ) ⊆ Z[1/p]`. The direction
   `=>` is restriction along `C[G] ⊆ C[H]`; `<=` is item 3.
5. **Rank-invisible algebraic classes are trace-invisible.** If all ranks of `y` vanish then `τ_ν(y) = 0` for every
   invariant `ν`.

**What it decides for the root.**
- **Dead: algebraic trace witnesses at the Bernoulli coefficient beyond the host.** Any idempotent matrix over the
  group ring `C[F_p wr_G G]`, for any torsion-free host (large-girth monsters included), has trace outside `Z[1/p]`
  only if its augmentation already has a non-`Z[1/p]` trace over `C[G]`. That includes every spectral projection of a
  finite-spectrum self-adjoint element of `M_k(C[H])`.
- **September 20 extension to all analytic classes, for iid product measures.**
  `bernoulli-product-traces-have-finite-cylinder-form` proves the same finite
  trace formula for all reduced K-classes. In the regular full shift a new
  Haar-trace witness beyond the host is excluded, including nonalgebraic
  spectral projections. The algebraic theorem above still has the distinct
  advantage of covering every invariant measure, including correlated ones.

**Model tests.**
- Cylinder `1_(C_s)`: `F = 1_(C_s)`, `n = δ_([s])`, trace `p^(-|F_s|)`.
- Conjugates `u_g 1_(C_s) u_g^*` have window `gF_s` and the same orbit coefficient, as they must.
- Non-selfadjoint idempotents `q + q b (1 - q)` with `q = 1_(C_s)` and `b` supported off `e` have the same diagonal as
  `q`, and item 2 gives the same trace.
- `G = Z`: all classes are cylinder combinations (Pimsner--Voiculescu), consistent with item 2.

**Scope.**
- Torsion-free hosts, the lamplighter alphabet `Z/p` for item 3, any finite alphabet and any invariant measure for item
  2. Only algebraic (group-ring) idempotents.
- Context import: for idempotents `P, Q` on a Hilbert space with `P - Q` of finite rank, the class `[P] - [Q] ∈ K_0(K)`
  is `Tr(P - Q)`.
- Bounded novelty check: the graph has the Kun--Thom congruence argument only; Farrell--Linnell (Whitehead groups and
  the Bass conjecture) not re-read for lamplighters over arbitrary hosts. No web search.

**2026-09-20 superseding trace boundary.** The stronger statement
`bernoulli-product-traces-kill-rank-invisible-k0` excludes a Haar-trace
defect even on rank-invisible virtual classes of the regular full shift.
`prime-lamp-wreath-trace-range-is-host-plus-z-inverted-p` computes the
entire trace range for infinite torsion-free hosts. Earlier descriptions
of a rank-invisible Haar candidate are historical; such a detector is
now ruled out. The narrower theorem in this node remains valid.
