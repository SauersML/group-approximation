# sk-deligne-sofic: plan (2026-09-14, wave 12)

Lane sk-deligne-sofic. Problem: Alekseev–Thom Open problem 6.1 (arXiv:2608.05362, `main_final.tex` l.1732): "Are there
examples of finitely presented sofic groups with Kazhdan's property (T) that are not residually finite?" The candidate
is Deligne's triple cover `1 -> C_3 -> E_3 -> Sp_4(Z) -> 1`: finitely presented, Kazhdan, with finite residual `C_3`.
Everything here is a plan; there are no claims yet.

## What main already has (read, not re-derived)
- **Open nodes.** `deligne-triple-cover-is-sofic`, fed into 6.1 by `fp-sofic-kazhdan-non-rf-via-deligne-triple-cover`
  (PASS as an implication). The sofic radical is `1` or `C_3`.
- **Dead constructions.**
  - Truncations of one exact monomial twisted module (`deligne-monomial-twisted-modules-have-no-folner-truncations`,
    ESTABLISHED).
  - Monomial models over exact finite quotients carry a detecting-cycle floor `4 nu / A_0(N)` and a rank count
    `[Gamma:N] <= m A_0(N)` (both ESTABLISHED, unreviewed). Neither is dimension-free, since `A_0(N)` grows with the
    systole.
- **Soficity through Bernoulli.** Theorem S, `weakly-bernoulli-liftable-action-makes-extension-sofic`: a liftable free
  action weakly contained in Bernoulli gives torsor sofic approximations over every sofic approximation of the base.
- **The cosystole question.** `deligne-class-congruence-cosystole-bounded-below` (OPEN condition C) excludes weakly
  Bernoulli lifts. Recorded attempts: (T) controls dimension 1 only; cycle packing gives only `(log m)^-2`; Popa plus
  compactness reaches bounded complexity; local patching is heuristic support for C.
- **Gohla–Thom imports** (arXiv:2403.09582): the class norm drops under weak containment, vanishes on quotients of free
  actions of the extension, and is bounded below on finite actions over cosystolic bases. A stable base forces a
  nonsofic extension (`gohla-thom-stable-base-nonsofic-extension`).
- **Credit locator to fix.** Bowen–Burton "Flexible stability and nonsoficity" is arXiv:1906.02172 (checked on
  arxiv.org 09-14). `research/artifacts/un-stability-nonsofic-2026-09-13-part1.md` l.54 says 1906.02034, which is an
  unrelated physics paper.

## Plan
1. **Finite-action criterion, the sofic direction (target: an ESTABLISHED node).** For a finitely presented `Gamma`, a
   finite abelian `A`, and a class `alpha`, suppose some asymptotically free sequence of finite `Gamma`-sets has
   normalized Hamming norm of `alpha` tending to 0. Then the extension `Gamma~` is sofic, with torsor approximations
   on `V_n x A`. This is the finite-action counterpart of Theorem S. It uses no Bernoulli input and no weak
   containment, only a small representative cochain and the van Kampen radius argument (freeness of the central
   part). Check first whether Gohla–Thom state it.
2. **Converse under flexible stability.** If `Gamma` is flexibly P-stable, `Gamma~` sofic implies the same sequence
   exists: project torsor approximations to the base, correct them to exact actions, and transport the cochain. So
   for flexibly stable bases, soficity of the extension is exactly the vanishing of the finite-action norm. Compare with
   Gohla–Thom's stable-base nonsofic theorem, which is one direction with a uniform lower bound; this adds the
   dichotomy form.
3. **The E_3 instance.**
   - A route into `deligne-triple-cover-is-sofic` from a new OPEN claim: asymptotically free finite `Sp_4(Z)`-actions on
     which the Deligne class has Hamming norm → 0. By the congruence subgroup property, transitive finite actions are
     `Gamma/Lambda` with `Lambda ⊇ Gamma(m)`, so the claim is about finite-index subgroups `Lambda` along the profinite
     topology, not only normal chains. That is strictly weaker than refuting condition C along one congruence chain.
   - A firewall for the other direction: if `Sp_4(Z)` is flexibly P-stable and the norm is bounded below on every
     asymptotically free finite action, then `E_3` is not sofic, and 6.1 needs another candidate.
4. **Attack on the new open claim.** Non-normal `Lambda`, for example the stabilizers of partial flags mod `m`, give
   Schreier complexes with more room than congruence covers. Test whether the Maslov-cocycle representative of `alpha`
   mod 3 admits a Hamming-small correction on flag-variety actions. Local compute is off-limits (RAM rule), so small
   explicit tests run on MSI only if a concrete finite model is small enough; otherwise stay theoretical and record
   attempts.

## Review and landing
- Claims queue in `$SK2/queue/verify.txt`.
- Artifacts: `research/artifacts/sk-deligne-sofic-2026-09-14[-partK].md`.
