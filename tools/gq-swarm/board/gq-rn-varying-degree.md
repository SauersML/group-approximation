# gq-rn-varying-degree board (DONE 2026-09-17)

**Approach** (family: host geometry / almost automorphisms of trees)
- Signature: "level-rigid almost automorphisms of aperiodic trees", then "p-adic P^1 as Röver–Nekrashevych space".

**Established** (lane proofs, not independently reviewed)
- d1259c704 `aperiodic-tree-almost-automorphism-fg-subgroups-are-rf`: non-eventually-periodic branching ⇒
  AAut = ascending union of profinite G_K ⇒ f.g. subgroups RF ⇒ no (Q,+); all-primes trees are always aperiodic.
- d1259c704 `pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori`: PGL_2(Q) ≤ V_p(Γ_p), Γ_p = PGL_2(Q) ∩ Iwahori
  acting on Z_p (self-similar, not f.g., not finite-state ⇒ no contracting overgroup). Limits: every hom
  SL_2(Q) → PGL_2(K) kills −I; diag(1,..,1,p) is not an almost automorphism of the ball tree of P^{n-1}(Q_p), n ≥ 3.
- b96d3428a `fg-linear-groups-have-roots-at-finitely-many-primes`: f.g. linear groups over fields: an element of
  infinite order has q-th roots for finitely many q. So Z_(p), Z[1/P] (P infinite), Q lie in no f.g. linear group.

**Open (conditional route landed)**
- `psl2-q-fp-simple-via-rational-iwahori-rn-host` → `psl2-q-embeds-in-fp-simple-group` needs only
  `rational-iwahori-group-lies-in-fp-self-similar-group` (fp self-similar Λ ⊇ Γ_p in Aut(T_p), V_p(Λ)^ab finite).
  Λ must be non-contracting, non-Möbius, non-linear.

**Needs**: a finitely presented self-similar Λ ⊇ Γ_p(1) ∪ {d_q : q ≠ p} on T_p (equivalent to the open input).
**Established (target 2, 98a1f1c0f)**: Γ_p = ⋃ Γ_p(m), Γ_p(m) = Iwahori(Z[1/m]) f.p. self-similar non-contracting,
  PGL_2(Z[1/pm]) ≤ V_p(Γ_p(m)); overgroups of Γ_p are not automaton groups and, if f.g., not linear or metabelian
  (new lemma fg-metabelian-groups-have-roots-at-finitely-many-primes); ring-affine/Möbius hosts on p-ary adic trees dead.
**Dead**: varying-degree / all-primes trees; natural Möbius Λ; contracting Λ.
**Sparks**: Wilson-type "countable RF group ⊂ f.g. RF group" with self-similarity; SL_2(Q) = SL_2(Z_(p)) *_{Iwahori} SL_2(Z_(p))'
  (Serre, Trees II.1.4) as a presentation to feed a self-similar overgroup.
