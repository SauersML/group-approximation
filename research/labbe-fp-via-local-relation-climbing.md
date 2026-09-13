---
rg: 2
id: labbe-fp-via-local-relation-climbing
kind: route
title: A local presentation plus climbing of local relations makes Labbé's derived full group finitely presented
target: labbe-shift-derived-full-group-is-finitely-presented
requires:
  - minimal-aperiodic-wang-shift-exists
  - zd-subshift-derived-full-group-local-presentation
  - labbe-full-group-local-relations-climb
artifacts:
  - research/artifacts/fp-simple-relation-climbing-2026-09-13.md
---

Let `G = D([[Z^2 ~ Omega_U]])`.

1. **Hypotheses of the local presentation.** `Omega_U` is a minimal subshift with a free
   `Z^2`-action (`minimal-aperiodic-wang-shift-exists`). So
   `zd-subshift-derived-full-group-local-presentation` applies. It gives `k_0, ℓ_0` with
   `G ≅ <𝒥 | all (k_0, ℓ_0)-local relations>`.
2. **Climbing.** Apply `labbe-full-group-local-relations-climb` to these `k_0, ℓ_0`. It gives
   `k, ℓ, m_1` and words `w_t` in `𝒥_(<= m_1)` with `w_t = t` in `G` for every `t ∈ 𝒥`.
3. **Tietze.**
   - Remove every generator `t ∈ 𝒥 \ 𝒥_(<= m_1)` together with its defining relation
     `t = w_t`. That relation holds in `G` but need not be `(k_0, ℓ_0)`-local; add it first. This
     does not change the group, since it is a consequence of the presentation in step 1.
   - The remaining presentation has generators `𝒥_(<= m_1)` and relations the substituted
     `(k_0, ℓ_0)`-local relations.
4. **Finitely many relations suffice.** By step 2 each substituted relation is a consequence of
   the `(k, ℓ)`-local relations among `𝒥_(<= m_1)`. These are relations of `G`, and there are
   finitely many, since `𝒥_(<= m_1)` is finite and lengths are bounded.
5. **Conclusion.** `G = <𝒥_(<= m_1) | (k, ℓ)-local relations>`, a finite presentation.
