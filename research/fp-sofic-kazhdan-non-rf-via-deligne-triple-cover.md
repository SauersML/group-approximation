---
rg: 2
id: fp-sofic-kazhdan-non-rf-via-deligne-triple-cover
kind: route
title: A sofic Deligne triple cover is a finitely presented sofic Kazhdan group that is not residually finite
target: fp-sofic-kazhdan-group-not-residually-finite
requires:
  - deligne-triple-cover-is-sofic
  - deligne-covers-of-sp2g-z-have-finite-residual-2z
artifacts:
  - research/artifacts/sk-verify-14-2026-09-13-part6.md
---

Let `E_3` be the preimage of `Sp_4(Z)` in the connected triple cover of `Sp_4(R)`, a central
extension `1 → C_3 → E_3 → Sp_4(Z) → 1`.

- **Finitely presented.** `Sp_4(Z)` is finitely presented (an arithmetic lattice), and an extension
  of a finitely presented group by a finite group is finitely presented.
- **Kazhdan.** `Sp_4(Z)` is a lattice in `Sp_4(R)`, which is simple of real rank two, so it has (T).
  An extension of a Kazhdan group by a finite group has (T).
- **Not residually finite.** By `deligne-covers-of-sp2g-z-have-finite-residual-2z` with `g = 2`,
  `n = 3`, `Res_fin(E_3) = ⟨z^2⟩`, which is all of `C_3 ≠ 1`.
- **Sofic.** This is the required claim `deligne-triple-cover-is-sofic`.

So `E_3` witnesses the target.

**Review (sk-verify-14, 2026-09-13): PASS as a one-step implication.** Finite presentation and property (T) of `E_3` are standard; non-residual-finiteness comes from the required node. Soficity is the open required claim. See `research/artifacts/sk-verify-14-2026-09-13-part6.md` §2.
