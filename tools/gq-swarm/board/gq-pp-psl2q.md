# gq-pp-psl2q board — DONE
**Approach:** family piecewise-projective / obstruction. Signature: "germ-trivial divisible subgroups act freely".
**Established (both referees PASS: gq-referee-a 1c4d03cb4, gq-referee-b 595ca31dd; fixes 0c649c0cd; gq-calibrator T6(c)):**
- `pp-circle-divisible-subgroups-act-freely` (+ `-proof`), landed d65ff92ff. Pieces in Λ ≤ PSL_2(R) or Aff_+(R)
  with no divisible abelian subgroup (true for every f.g. host: Λ_0 = <pieces of generators> is f.g. linear, RF),
  finitely many breakpoints: every divisible abelian D ≤ Γ acts FREELY (common fixed point ⇒ germ hom D → Λ,
  divisible in RF ⇒ trivial ⇒ contradiction on a gap), rot|_D injective, N(D)=C(D), D ∩ [A,A]=1 for amenable A;
  rational rotation numbers (T, Calegari's PL class) ⇒ D torsion.
- `pp-circle-and-lift-hosts-miss-gl-n-q` (+ `-proof`), landed d65ff92ff: same for lifts Γ~ via translation number;
  so T, T-bar, Lodha's S, Lodha–Moore, f.g. subgroups of Monod H(A), Stein/irrational-slope PL groups and lifts
  contain none of GL_n(Q), SL_n(Q), P(G/S)L_n(Q) (n≥2), Aff(Q), B_2(Q), U_3(Q), Q ⋊_r Z (r≠1).
  Sharp: T-bar ⊇ Q; its divisible abelian subgroups are 1 or ≅ Q (no Q^2).
- Root Attempts item 10, landed 7d64b9412.
**Needs:** —
**Dead:** 1-dim piecewise-projective / PL hosts (finitely many breakpoints) and their lifts, for G and stepping
  stones, every embedding. Natural-embedding kill is gq-solenoid's `piecewise-commutative-linear-hosts-miss-linear-gl-n-q`.
**Sparks (not pursued):** (1) does a f.g. piecewise-projective circle group contain (Q,+) at all? By the theorem it
  must act freely with some irrational rotation number, hence (Denjoy, bounded-variation derivative) be topologically
  conjugate to a dense rotation group. (2) Same germ argument on Cantor hosts: at a common fixed point of D whose
  germ group is RF (e.g. V-germs), D's germs die — may give the analogue for germ extensions whose singular germ
  groups have no divisible abelian subgroups (for gq-germ-necessary).
