---
rg: 2
id: measure-free-steinberg-el-n-reduced-cstar-not-mf-proof
kind: route
title: Reduced and maximal algebras of measure-free elementary groups are not MF, via the MF residual calculus lemma
target: measure-free-steinberg-el-n-reduced-cstar-not-mf
requires:
  - no-invariant-measure-steinberg-elementary-no-mf-quotient
  - boundary-action-elementary-simple-kazhdan-not-mf
  - bkko-reduced-traces-concentrate-on-amenable-radical
artifacts:
  - research/artifacts/un-reduced-cstar-2026-09-13-part1.md
---

Full derivation in the artifact, §1 (Theorem 1 and Corollaries 2–3).

1. **No MF quotient passes to quotients.** By `no-invariant-measure-steinberg-elementary-no-mf-quotient` item 2,
   every homomorphism `EL_N(R) → M` with `M` MF is trivial for `N ≥ 2n`. For a quotient `q: EL_N(R) → Q`, any
   `f: Q → M` gives `f∘q` trivial, hence `f` trivial. `Q ≠ 1`, so `Q` is not MF.
2. **Algebras.** Manuscript Lemma `prop:mf-residual-calculus` (`non_mf_groups_exist.tex` l.361) says that if `A` is
   unital, `π: G → U(A)` is injective and `A` embeds in a norm matrix corona, then `G` is MF. It explicitly covers
   `C*_max(G)` and `C*_r(G)`. With `G = Q` and step 1, neither algebra is MF.
3. **Separable and stably finite.** `Q` is countable, since `k` is countable and `𝒢` second countable. The
   canonical trace on `C*_r(Q)` is faithful, which gives stable finiteness, as in manuscript Cor l.1038.
4. **Boundary corollary.** `boundary-action-elementary-simple-kazhdan-not-mf` gives `S_∂` infinite, simple and
   Kazhdan, hence non-amenable, so its amenable radical is trivial. `bkko-reduced-traces-concentrate-on-amenable-radical`
   (BKKO Thm 4.1) forces every tracial state to vanish on `λ_s` for `s ≠ e`, so the trace is unique. Items 1–3 apply
   with `n = 1`.
5. **Necessity.** Items 1–2 with `Q = EL_N(R)` are the contrapositive of the necessity corollary.
