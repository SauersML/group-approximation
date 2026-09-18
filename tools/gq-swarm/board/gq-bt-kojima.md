# gq-bt-kojima board (lane finished)
**Approach:** Brin–Thompson / twisted BT hosts; "extend Kojima–Sheng Q <= 2V"; mechanism = fractional-part register + overflow into one fixed element (artifact gq-bt-kojima-mechanism.md).
**Established (landed):**
- dc7ed0ea3: countable-virtually-abelian-groups-embed-in-2v; twisted-bt-point-fixing-actor-elements-are-divisible (register roots in every SV_G; type (A) survives adding fixed points); rational-stepping-stones-in-nv-need-bs12-or-heisenberg.
- d86605259: root attempt 11.
- 2d0a728bd: scaled-rationals-in-nv-need-aperiodic-core-elements — a copy of Q in nV scaled by a != ±1 has only zero-exponent, open-periodic, aperiodic-core elements (log table length for integer a); the odometer copy (base t x id, fixed point exponent (1,0)) is scaled by NOTHING. So Q x|_3 Z in 2V needs a new copy of Q built on aperiodic-core elements.
**Landed 0e1d94444:** renormalizable-thompson-elements-are-odometer-codes (renormalization ⟺ bounded odometer of a brick code ⇒ Z_m factor, no periodic points, zero drift); hole some-brin-thompson-element-factors-onto-an-odometer (OPEN, necessary for the renormalization route); bs12 attempt 5. bs12 NOT settled.
**Needs:** BS(1,2) <= nV (bs12-embeds-in-brin-thompson-2v, OPEN): the gate. For n >= 3 also SL_3(Z) <= nV (infinite Kazhdan subgroup, OPEN).
**Dead:** odometer/Kojima–Sheng-type copies on V x id bases as unipotent parts; register roots give no Steinberg/Heisenberg relations (localized commutators).
**Sparks:** (1) registers on a SMART/RTM base — TAKEN: gq-affq landed three-v-contains-aperiodic-rationals and renormalizable-thompson-elements-give-baumslag-solitar (81066618e); (2) coordinatize Ẑ_odd so x2 is a coordinate permutation while +1/M_n stays bounded.
