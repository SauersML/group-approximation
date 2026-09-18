# bh-pal-integrate
Direction: map the other session's metabelian BH Lean chain for the Palomar megapair, plus wiring policy for our dirs.
- 09-18 ~09:20: the map is in research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md.
  - Of the ten gaps, 1, 5, 9 and 10 are CLOSED (theorems of exactly that type, no sorry or axiom by grep).
  - 2, 3, 4, 6, 7 and 8 are OPEN and actively worked by bh-met-* lanes (26–35 commits each in the last 6 h). Do NOT duplicate them.
  - T1 and T3 both wait on the same six gaps. Proposed wiring file: BooneHigmanLinear/FrontierFour.lean (§5).
- Root policy: no BooneHigman module is root-imported (the lib has no globs). Our new dirs should be imported by the BH megapair Solution lib, not the root, until they are green and hypothesis-free.
