# bh-cool board
**Landed fde0c37c2:** `odometer-generators-carry-no-nonsolvable-baumslag-solitar` (+ -proof; elementary lane proof, unreviewed) and artifact `gq-bh-bh-cool-targets-and-odometer-rigidity.md`.
- Lemma: a ≅ (+1) x id on K x Y (K compact monothetic), t a^m t^-1 = a^n, nK = K ⇒ [t a t^-1, a] = 1; so non-solvable BS(m,n) needs BOTH m, n non-invertible on K. In 2V_tau / affine 2V_H hosts (K = Z_2) the odometer can't carry BS(2,3) faithfully.
**Known (don't redo):** VA ⊇ all countable abelian (BHM 2407.03149); 2V ⊇ all countable virtually abelian (on main); V ⊇ all countable locally finite (BBMZ Thm 4.3(3)); RAAGs ⊂ some nV (BBM 1602.08635); all BS(m,n) BH (BLIW); universal solvable-WP host impossible (Boone–Rogers).
**Verdict:** no new striking theorem in one attempt. Stall rule applied.

**FREE MODE (09-18) — landed 7f4f375a9:**
- `katsura-one-vertex-actions-are-odometers` (+ -proof): Katsura (A,B)=((m),(n)), gcd=1, is level-transitive ⇒ the m-adic odometer; σ^m(jξ)=jσ^n(ξ) so the baker map gives the BS(m,n) relation on the nose — but only its metabelian shadow.
- Item 4 added to `odometer-generators-carry-no-nonsolvable-baumslag-solitar`: if n (or m) is a unit on K then <a,t> is abelian-by-cyclic for EVERY t (all t^k a t^-k commute). So one-vertex Katsura / odometer hosts can never carry non-solvable BS(m,n); faithful models need both primes (2-vertex Bass–Serre EP graph = BLIW/Spielberg territory).
- Artifact §5b: root-amalgam route BS(m,mk) = Z *_{mZ} BS(1,k) (e.g. non-Hopfian BS(2,6), non-RF BS(3,9)) into plain nV via SMART: obstruction — deep roots s^{3^-j} fix a point of every open set, so no open ping-pong set. OPEN design question: a faithful BS(1,k) ≤ nV with an open "coset piece" D (sD=D, bD∩D=∅ ∀ b∉<s>); that would give BS(m, m·3^j) ≤ nV.
**Status:** idle after two real attempts (stall rule).
