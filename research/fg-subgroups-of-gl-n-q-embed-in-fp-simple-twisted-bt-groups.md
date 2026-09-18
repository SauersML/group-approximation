---
rg: 2
id: fg-subgroups-of-gl-n-q-embed-in-fp-simple-twisted-bt-groups
kind: claim
title: Every finitely generated subgroup of GL_n(Q) embeds in a finitely presented simple twisted Brin--Thompson group, which also contains 2V and so Q
distinct_from:
  fp-self-similar-subgroups-satisfy-permutational-boone-higman: that puts finitely generated linear groups over number fields in the class B_A; this names the host, a finitely presented simple twisted Brin--Thompson group SV_G, and records that it also contains nV for n <= |S|.
  rational-linear-groups-satisfy-boone-higman: that is Zaremsky's Theorem 1.2, whose host is a Rover--Nekrashevych commutator subgroup; this is the twisted Brin--Thompson host.
  gl-n-q-in-permutational-boone-higman-class: that is the open statement for the whole countable group GL_n(Q); this is the established statement for each finitely generated subgroup separately.
  rational-stepping-stones-in-nv-need-bs12-or-heisenberg: that says which open nV questions an untwisted nV host of GL_n(Q) must answer; this says the twisted hosts face no such finitary question.
artifacts:
  - research/artifacts/gq-gq-nv-obstruct-verdict.md
---

**ESTABLISHED (2026-09-17)** through
`fg-subgroups-of-gl-n-q-in-twisted-bt-proof`. Lane proof assembling
established nodes. Not independently reviewed.

**Statement.** Let `n >= 1` and let `H <= GL_n(Q)` be finitely generated.
1. There are a finitely presented group `Γ >= H`, a faithful action of `Γ` on a
   set `S` of type (A), and hence an embedding of `H` in the finitely presented
   simple twisted Brin--Thompson group `SV_Γ`.
2. Whenever `|S| >= k`, the group `SV_Γ` contains the Brin--Thompson group `kV`.
   If `H` is infinite then `S` is infinite, so `SV_Γ` contains every `kV`, hence
   `(Q,+)` (`rationals-embed-in-brin-thompson-group-2v`) and every countable
   virtually abelian group (`countable-virtually-abelian-groups-embed-in-2v`).

In particular, for all `n, m >= 1` each of `GL_n(Z[1/m])`, `SL_3(Z)`,
`BS(1,2) <= GL_2(Z[1/2])` and `H_3(Z) <= SL_3(Z)` embeds in a finitely presented
simple twisted Brin--Thompson group. The host depends on the subgroup.

**What this says about the root** (`gl-n-q-embeds-in-fp-simple-group`).
- O2 has no analogue for twisted Brin--Thompson hosts. `SL_3(Z)` excludes `V`
  and `VA`, and it is exactly the gate for untwisted `nV`
  (`rational-stepping-stones-in-nv-need-bs12-or-heisenberg`, item 3). But it lies
  in many finitely presented simple `SV_Γ`.
- The same holds for the gates `BS(1,2)` and `H_3(Z)` of the untwisted family,
  for the distortion obstruction O4 (these hosts contain `BS(1,2)`), and for O3
  (they contain `2V`, hence `Q`).
- So any proof that `GL_n(Q)` embeds in no finitely presented simple twisted
  Brin--Thompson group must use the whole countable group. No finitely generated
  subgroup, and no countable virtually abelian subgroup, witnesses it. The
  positive question for this family is exactly
  `gl-n-q-in-permutational-boone-higman-class`, through the route
  `gl-n-q-bh-via-permutational-class`.

**Credit.** Known in substance: BFFHZ arXiv:2503.21882v2 (Remark 3.5, Theorem C)
and Zaremsky arXiv:2405.18354 (Theorem A). Item 2 is an elementary observation
from the definition of `SV_Γ`. No priority is claimed.
