---
rg: 2
id: fp-sofic-kazhdan-non-rf-via-km-246-lattice
kind: route
title: A sofic (2,4,6) Kac-Moody lattice is a finitely presented sofic Kazhdan group that is not residually finite
target: fp-sofic-kazhdan-group-not-residually-finite
requires:
  - km-246-lattice-is-sofic
  - km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4
artifacts:
  - research/artifacts/sk-verify-14-2026-09-13-part6.md
---

By `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`, for `q >= 4` the group
`S_q = Lambda_q/Z` is finitely presented, infinite, simple and Kazhdan. An infinite simple group
has no nontrivial finite quotient, so `S_q` is not residually finite. By `km-246-lattice-is-sofic`,
some `S_q` is sofic, and it witnesses the target.

**Review (sk-verify-14, 2026-09-13): PASS as a one-step implication.** An infinite simple group has no nontrivial finite quotients. Soficity is the open required claim. See `research/artifacts/sk-verify-14-2026-09-13-part6.md` §2.
