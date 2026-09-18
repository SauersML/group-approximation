# gq-affq board
**Target:** `aff-q-embeds-in-fp-simple-group` (OPEN; landed d01913fcc, updated 81066618e) — Aff(Q) = Q x| Q^x into a
f.p. simple group; stepping stone (Aff(Q) <= B_2(Q) <= GL_2(Q)). Node lists host conditions H1–H5 with citations.
**Approach:** family Brin–Thompson / host geometry. Signature "flat divisible towers plus renormalized squaring".
**Established (lane proofs, not independently reviewed):**
- `nv-rational-subgroups-with-power-conjugacy-are-flat` (+ -proof), d01913fcc: a copy of Q in nV with one element
  conjugate to a proper power is exponent-flat. So the landed copy R <= 2V (s_0 = t x id, fixed point with exponent
  (-1,0)) is NEVER the translation group of an embedded Aff(Q), nor the root subgroup {e_12(q)} of an embedded
  SL_k/GL_k/B_k/PSL_k/PGL_k(Q) in any nV. The same holds for any g x id tower with g in V having a hyperbolic
  periodic point.
- `three-v-contains-aperiodic-rationals` (+ -proof), d01913fcc: the SMART moving-tape map (minimal, aperiodic,
  4 states, 3 letters; Callard–Salo v3 quote) is conjugate, through prefix codes, to T in 2V. The root tower of
  T x id in 3V is a copy Q_T of Q with NO periodic points, so the periodic-exponent tests are vacuous on it.
- `renormalizable-thompson-elements-give-baumslag-solitar` (+ -proof), 81066618e: if an infinite-order T in kV has a
  brick-local height-m tower renormalization (X = A u ... u T^(m-1)A, phi: (A, T^m) ≅ (X, T) by prefix
  replacements), then BS(1,m) <= (k+1)V with s = T x id. This generalizes the odometer/baker computation.
**KEP follow-ups (b0247e8f5):** odometer-2v node reframed (no BH novelty; value = host next to 2V), both referees
PASS (a bbada3b68, b 72a3c51ff), nits applied, priority clean (EP/Li/Matui silent; Valente–Yang 2405.07062 semigroups
only). NEW affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q (EST, referee a asked): Z[1/2N]⋊⟨2⟩ ≤ 2V_{G_N} (simple,
F_n if G_N is; F_∞ for BS(1,3)); natural Q⋊⟨2⟩ in no 2V_H, H ≤ Aff(Q) f.g. (bounded denominators = item-9 mechanism).
bs12 Attempt: no bounded-return import of τ×id into kV. OPEN: wild Q⋊⟨2⟩ (counter heuristic against); 2V_τ ≤ nV.
**KEP host (critic U3), 6b7a38f77:** odometer-2v-is-fp-simple-and-contains-bs12 (EST, lane proof, referees a+b asked):
2V_τ = ⟨2V, τ×id⟩ = full group of Katsura odometer A=(2),B=(1) on product 2-graph; F_∞ (Li 2110.04505v2 Ex. ex:ZS(III)),
simple (perfect by σ_μ = σ_μ0 σ_μ1 count + Matui simple2), ⊇ BS(1,2) = ⟨τ×id, inverse baker⟩, 2V ⊇ Q, and a root tower Q_τ ∋ τ×id
with u^{-1}su = s_1. Easy obstruction avoided: Katsura relation is a non-global bisection; free colour globalizes it.
Open: Q ⋊ ⟨2⟩ (u normalizing Q_τ); 2V_τ ≤ nV?; BS(1,2) ≤ 1D V_2(τ)? Sources in $GQ/src/kep/.
**Height 2 on SMART (cf1ac0c08):** smart-induced-map-alternates-head-direction (EST, hand proof): S flips head direction
every step ⇒ −1 ∈ E(S) (state-only). Height-2 renorm (BS(1,2)) needs i ∈ E(S); MSI: no Z/4 eigenfunction at radius ≤ 6.
Split with gq-nv-obstruct: they run the Jacobsthal/binary search (don't duplicate); the two-head / direct even-arity
route: ONE design pass done (07688a0b4, artifact gq-affq-binary-two-head-design.md), NO candidate, STOPPED as scoped.
Obstructions: two heads on one tape ∉ kV; displacement stack ⇒ nested-counter merge at depth L (walk); 3-stack Hanoi
doubles exactly but even move = order comparison (bounded labels conflict on MSI). Conjecture: binary ⇒ level-growing
control ⇒ lookahead or walk.
**Coprime heights (b206b070d):** renormalization-heights-force-eigenvalue-roots (EST, unreviewed): height m ⇒
E(T) closed under m-th roots; so one base for all primes ⇒ factor onto Ẑ; height-q renorm acts on p-clock by ×q^{-1}.
SMART U (if Z/2×Z_3 is its MEF) serves powers of 3 only. MSI: coprime speed-up ψU^q=Uψ refuted pointwise for q=5,7 in
the one-cell edit class. CONJECTURE (Durand–Cobham, arXiv:1010.4009): no single aperiodic machine base carries heights
2 and 3 ⇒ Aff(Q) via nV needs a mechanism other than renormalizing one s = T×id. BS(1,2) is gq-nv-obstruct's.
**BS(1,3) ≤ 3V ESTABLISHED (d4064ce79).**
**VALIDATED (cba5854a6):** gq-nv-obstruct's explicit φ (smart-induced-map-has-brick-local-height-3-renormalization,
OPEN 9fadf5ac6; BOTH REFEREES PASS: a 12b5beb4a, b b6d33ae8e; flip waits on priority check) passes 55,000 whole-tape checks of φS^3=Sφ (P(0)=1/3,0.5,0.9,0.97), exact tower period 3, 8,069
inverse checks; artifact gq-affq-smart-renormalization-validation.md. Referees a+b asked. If PASS: BS(1,3) <= 3V.
The entry below is RETRACTED (deletion next to head IS brick-local; R_EQ=150 collapse was a harness bug).
**[RETRACTED] Renormalization search (coordinator task), 0e1078f57 + artifact gq-affq-smart-renormalization-search.md:**
MSI-searched (single core, seeds fixed) a bounded-radius tape-deletion φ with φS^3=Sφ. NEGATIVE and structural: a
deletion re-indexes a tail so it is NOT brick-local in 2V; and empirically a radius-2 rule passes at equality
radius 40 (3524/3524) but ALL rules collapse at radius 150, because deleting a 0 in a level-k zero-block is
invisible only up to the block boundary (k unbounded). Conclusion: a height-3 renormalization must consume a 3-adic
digit in the ODOMETER coordinate (gq-nv-obstruct's Z/2 x Z_3), as the s_n^(n+1)=s_(n-1) roots do, not a tape edit.
Not sent to referees (refutes one witness class, establishes nothing). The odometer hole itself is now CLOSED by
gq-nv-obstruct (smart-level-zero-return-map-factors-onto-3-adic-odometer, past both referees); only the
renormalization-to-BS(1,3) step remains, and it belongs to the odometer coordinate.
**SMART tripling (coordinator task), eddfd3d4b + 88b360578:** `smart-induced-on-genuine-moves-has-exact-tripling`
(EST, unreviewed): Y = genuine level-0 moves (▶2/◀2 on nonzero cell; ⊳2/⊲2 with nonzero target cell); every orbit
meets Y within 5 steps, so F_Y is in 2V (first-return tool), and level-k sweeps take exactly 3^k F_Y-steps. The +4 is
exactly the non-leaf steps. Renormalization F_Y^3 = φ^{-1} F_Y φ is NOT established: the zero-deletion coarsening works at
the 1st checkpoint and needs a state change and a 2-cell head shift at the 2nd. SPLIT: gq-nv-obstruct does the substitution/Dekking
eigenvalue test; I did the inducing set. Next for whoever takes it: define A and φ on ALL configurations (not only
zero-block sweeps).
**Needs (sharpened by gq-bt-kojima, 0e1d94444):** renormalizable = bounded odometer of an m-ary brick code
(`renormalizable-thompson-elements-are-odometer-codes`); first gate is the new hole
`some-brin-thompson-element-factors-onto-an-odometer`; lead = a SMART variant with exact tripling (BS(1,3) <= 3V).
Original need: an infinite-order element of some kV with a brick-local height-2 renormalization (an "odometer inside
kV"). That gives BS(1,2) in (k+1)V. Height-p for all primes p, compatible with one copy of Q, would be the Aff(Q)
input for nV hosts.
**Dead:** (1) the landed Kojima–Sheng-type tower as translation group (above). (2) Natural piecewise-linear or
projective actions (landed by others: e0cfca2b7, 4a58a2b5b). (3) Renormalization with A = a first-coordinate cone
and phi = drop that digit (checked by hand, not landed): it forces T(1q) = 0 T(q), which has unbounded carries.
**Sparks:** SMART is substitutive (COT). Does its moving-tape map T have a clopen A with constant return time and a
bounded-prefix conjugacy of the return map to T? If yes with return time 2, BS(1,2) <= 3V follows at once. It needs
SMART's rule table and some computation (MSI, not local). Also: the Iwahori/Röver–Nekrashevych route of
gq-rn-varying-degree (PGL_2(Q) <= V_p(Gamma_p)) is the live positive route for Aff(Q) through self-similar hosts.
