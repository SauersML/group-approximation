---
rg: 2
id: pgl-2-q-embeds-in-the-rational-group
kind: claim
title: PGL_2(Q) acts on the Farey Cantor set by rational homeomorphisms, so Aff(Q) and PSL_2(Q) embed in the rational group R
distinct_from:
  pgl-n-q-acts-on-rational-polyhedral-cantor-set: that builds the action of PGL_n(Q) on the Stone space S_n, identifies S_2 with the standard Cantor set carrying standard V, and shows the action is singular everywhere; this proves that each element of PGL_2(Q) is a rational homeomorphism of S_2 (finitely many local actions), so the whole group lies in the asynchronous rational group.
  dyadic-affine-bs12-model-lies-in-no-finite-nucleus-rsg: that is one explicit rational copy of BS(1,2) and its exclusion from finite-nucleus RSGs; this is a rational copy of all of PGL_2(Q), containing Aff(Q) and BS(1,m) for every m.
  aff-q-embeds-in-fp-simple-group: that is the OPEN stepping stone asking for a finitely presented simple host of Aff(Q); this gives a simple host that is not finitely generated (R), and records why the natural copy lies in no contracting RSG.
  rsg-equicontinuity-program-cannot-exclude-gl-n-q: that shows one open test cannot exclude these groups from finite-nucleus RSGs; this shows they do lie in the full rational group, in non-contracting RSGs.
  aff-q-does-not-embed-in-aut-thompson-f: that excludes Aff(Q) from Aut(F); this puts Aff(Q) in the rational group and leaves Aut(V) open (aff-q-embeds-in-aut-v).
---

**ESTABLISHED** through `pgl-2-q-embeds-in-the-rational-group-proof` (lane proof, not
independently reviewed). The transducers are Raney's (G. N. Raney, *On continued fractions
and finite automata*, Math. Ann. 206 (1973) 265–284, not read at the source). The proof below
is self-contained, and no novelty is claimed.

**Setting.** `S_2` is `RP^1` with every point of `P^1(Q)` doubled into a left and a right
copy, the Stone space of `pgl-n-q-acts-on-rational-polyhedral-cantor-set` (item 3). Code it
as `{0,1}^N`: the first letter chooses the half `[0,∞]` or `[∞,0]`, and each later letter
chooses the left or right Farey child, splitting a Farey arc `[p/q, r/s]` at its mediant.
Each cone `C_w` has a chart `S_w ∈ SL_2(Z)` with `S_w([0,∞]) = C_w`: `S_0 = 1`,
`S_1 = [[0,-1],[1,0]]`, and the children are `S_w L`, `S_w R` with `L = [[1,0],[1,1]]`,
`R = [[1,1],[0,1]]`. Under Minkowski's question-mark function this is the standard binary
Cantor set, and the canonical similarities between cones are the maps `S_v S_w^-1`. So
Thompson's `V` acts in standard form, and `T` is the piecewise-`PSL_2(Z)` group.
`R = R_{Γ,E}` for the full binary shift is the rational group of Grigorchuk–Nekrashevych–
Sushchanskii. By Belk–Bleak–Matucci–Zaremsky, arXiv:2309.06224v3 (TeX line 363, recorded in
`research/artifacts/bh-rational-similarity-hosts-2026-09-12.md` §3), a homeomorphism is
rational if and only if it has finitely many distinct local actions `f|_α`, where
`f(α·ω) = f̄(α)·f|_α(ω)` and `C_{f̄(α)}` is the smallest cone containing `f(C_α)`.

**Statement.**
1. Every `M ∈ PGL_2(Q)` acts on `S_2` by a rational homeomorphism, and `M ↦ (M on S_2)` is an
   injective homomorphism `PGL_2(Q) → R`, landing in `Γ_2 = <V, PGL_2(Q)> ≤ R`. For deep cones
   the local actions of `M` are the reduced nonnegative integer matrices of determinant
   `±D(M)`, where `D(M)` is the determinant of a primitive integral representative. There are
   finitely many of these.
2. Hence `Aff(Q) ≅ {[[a,b],[0,1]]}`, `PSL_2(Q)`, `SL_2(Q)/{±1}` and `BS(1,m) ≤ Aff(Z[1/m])`
   (every `m ≥ 2`) embed in `R`. Since `R` is simple (Belk–Hyde–Matucci, arXiv:1711.01668,
   abstract: "simple and not finitely generated"), each of these groups embeds in a simple
   group that is not finitely generated.
3. **Not contracting.** In `Γ_2` the powers `x ↦ 2^k x` have deep local actions of primitive
   determinant `2^k`, so the nucleus of any RSG containing this copy of `Aff(Z[1/2])` is
   infinite. BBMZ's finite-presentation theorem for full contracting RSGs therefore does not
   apply to the natural copy.
4. **Finitely generated pieces.** Let `P` be a finite set of primes. Every element of
   `<V, PGL_2(Z[1/P])>` is piecewise `PGL_2(Z[1/P])` with finitely many arcs, and two Möbius
   maps that agree on an arc are equal. So every finitely generated subgroup of `Γ_2`
   meets `PGL_2(Q)` in a subgroup of some `PGL_2(Z[1/P])`, and contains no copy of `(Q,+)`
   from the natural action. This is the analytic-continuation obstruction of lane gq-pp-psl2q.
5. **Aut(V).** The natural copy does not normalize `V`. For `A = [[1,0],[1,1]] ∈ PSL_2(Z) ≤ T`
   and `M_2 = diag(2,1)`, the conjugate `M_2 A M_2^-1 = [[2,0],[1,2]]` has primitive
   determinant `4`, so it lies outside `PGL_2(Z)`. By item 4 of
   `pgl-n-q-acts-on-rational-polyhedral-cantor-set` it agrees with no element of `V` on any
   arc, so it is not in `V`. Whether `Aff(Q)` embeds in `Aut(V)` at all is the OPEN claim
   `aff-q-embeds-in-aut-v`.

**Verdict for the RSG route (n = 2).** The rational group itself is no obstruction:
`Aff(Q)` and `PSL_2(Q)` are in `R`. What remains open is a finitely presented subgroup,
equivalently (item 4) a finitely generated one with generators that are not piecewise
projective, containing some copy. Any contracting RSG would need a copy other than the
natural one (item 3).
