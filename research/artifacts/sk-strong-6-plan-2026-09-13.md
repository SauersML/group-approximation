# sk-strong-6 plan: which approximation classes have simple Kazhdan envelopes

Lane sk-strong-6, 2026-09-13 ~20:30 CDT. Lens (ROSTER-F): what the LEF iff theorem implies for approximation classes.

## Target
For a class P of finitely generated groups that is closed under finitely generated subgroups, consider

  (Env_P)  Γ ∈ P  iff  Γ is a subgroup of an infinite finitely generated simple group with property (T) that lies in P.

Main now carries Env_LEF: `lef-groups-embed-in-simple-kazhdan-lef-groups`, which three independent reviews have PASSed. The lane will:
1. **Upgrade Env_LEF** to hosts that are marked limits of finite simple groups SL_{3N}(F_2) whose Cayley graphs form expanders. The goal is to show that the lamplighter host's finite models can be taken on configurations, where the generator images generate M_N(F_2). Then §2 of the note matches its title: LEF groups are exactly the subgroups of infinite simple Kazhdan groups that are limits of finite simple expanders.
2. **Settle the classes where Env_P fails for structural reasons.** P = residually finite, amenable, residually amenable, residually solvable, and locally residually finite contain no infinite simple Kazhdan group, so Env_P fails.
3. **Price Env_P for the classes strictly between LEF and "all groups":** sofic, hyperlinear, weakly sofic, linear sofic, initially subamenable, MF. Each contains the finitely presented amenable non-RF Abels–Prüfer quotient, so Env_P forces an infinite simple Kazhdan P-group that is not LEF. This generalizes `sofic-universal-envelope-forces-non-lef-simple-kazhdan` from sofic to every such class.
4. **Record the open statements precisely** as open claims with Attempts, and give a sharp question sentence for the note.

## Why it is beautiful and high impact
- One table decides which approximation properties are "generated" by simple Kazhdan groups.
- LEF is the unique standard class so far where the answer is yes, and the upgrade turns it into a statement about limits of finite simple expanders, exactly the note's headline object.

## Not duplicating
- sk-universal-embedding-a/b and sk-lef-embedding-* own the LEF embedding itself; this lane only upgrades the host.
- sk-sofic-embedding-a/b own the sofic target; this lane gives the class-uniform cost statement and the table.
- sk-universal-lef-host-* own the universal hosts. sk-wp-* own word-problem control.
