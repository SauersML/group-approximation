---
rg: 2
id: odd-roots-of-the-2v-tau-odometer-have-doubling-conjugators
kind: claim
title: For every odd q the 2V_tau odometer has an explicit q-th root r_q and a doubling element u_q with u_q r_q u_q^{-1} = r_q^2
distinct_from:
  lifted-odd-roots-of-the-odometer-doubled-by-the-baker-map: that is the OPEN target asking for ONE doubling element serving every odd q at once (Q semidirect <2>); this settles each odd q separately, with a doubling element that depends on q.
  odometer-2v-is-fp-simple-and-contains-bs12: that gives BS(1,2) = <s, u> on the odometer itself; this gives BS(1,2) = <r_q, u_q> on a q-th root of it.
---

**ESTABLISHED** (lane proof, bh-free-30, 09-18; elementary, every identity is checked below; not reviewed; no priority claimed).

## Setting

- 2V_τ acts on C × C, with s(x,y) = (x+1, y), where x ∈ Z_2 is read least significant digit first.
- The inverse baker map is u(x, y_0 y) = (y_0 + 2x, y), so u s u^{-1} = s² (`odometer-2v-is-fp-simple-and-contains-bs12`).
- For locally constant k, j: C → Z and ρ, g ∈ V, the maps (x + k(y), ρy) and (x + j(y), gy) lie in 2V_τ, the topological full group.

## Statement

Let q ≥ 3 be odd, and let C = A_0 ⊔ … ⊔ A_{q−1} be a partition into cones (words A_i). Put:
- ρ(A_i w) = A_{i+1} w, with indices mod q, a free element of V of order q;
- k = +1 on A_i for i < (q+1)/2, and k = −1 otherwise, so k is odd everywhere and its ρ-orbit sums are 1;
- g(A_i x w) = x A_{2i} w, for x ∈ {0,1}, an element of V;
- r = (x + k(y), ρy) and c = (x + j(y), gy), with j the locally constant solution of (J) below;
- u_q = u∘c.

Then:
- r^q = s;
- u_q s u_q^{-1} = s²;
- u_q r u_q^{-1} = r².

So ⟨r, u_q⟩ ≅ BS(1,2) is faithful, and 2V_τ contains (1/q)Z[1/2] ⋊ ⟨2⟩ with 1 ↦ s.

## Proof

1. **r^q = s.** r^q = (x + Σ_{i<q} k(ρ^i y), ρ^q y) = (x+1, y).
2. **c commutes with s,** since both act on the first coordinate by translation. So u_q s u_q^{-1} = u s u^{-1} = s².
3. **The conjugator g.** Let Φ(h)(z_0 z) = z_0 h(z). Then gρg^{-1} = Φ(ρ²):
   - gρg^{-1}(x A_{2i} w) = gρ(A_i x w) = g(A_{i+1} x w) = x A_{2i+2} w;
   - Φ(ρ²)(x A_{2i} w) = x A_{2i+2} w, the same.
   - Since i ↦ 2i is a bijection of Z/q, the cones x A_{2i} partition C.
4. **Solving for j.** c r c^{-1} = r̃ := (x + k̃(y), Φ(ρ²)y) exactly when
   (J) k̃(g y) = k(y) + j(ρy) − j(y).
   Take k̃(z_0 z) := (k(z) + k(ρz))/2. This is an integer, because k is odd everywhere. Its orbit sums over Φ(ρ²)-orbits are 1: the points are z_0 ρ^{2i} z, and Σ_i (k(ρ^{2i}z) + k(ρ^{2i+1}z))/2 = (1+1)/2.
   So k̃∘g − k has ρ-orbit sums 0. On the free action, fix j = 0 on the fundamental domain A_0 and solve (J) along the cycle. This gives a locally constant j.
5. **u r̃ u^{-1} = r².** Write z = z_0 + 2z'. Then u^{-1}(z, y) = (z', z_0 y), and r̃ maps this to (z' + k̃(z_0 y), z_0 ρ²y). Applying u gives (z + 2k̃(z_0 y), ρ²y) = (z + k(y) + k(ρy), ρ²y) = r²(z, y).
6. **Conclusion.** So u_q r u_q^{-1} = u r̃ u^{-1} = r². The relation map BS(1,2) → ⟨r, u_q⟩ is injective, because r has infinite order: a nontrivial kernel would meet the base Z[1/2], and every nonzero element of the base has a power in ⟨r⟩. ∎

## Remarks

- For q = 3 with A = (0, 10, 11), the conjugator is g(00w)=00w, g(100w)=011w, g(110w)=010w, g(01w)=10w, g(101w)=111w, g(111w)=110w, and j = −1 on 11C, 0 elsewhere.
- **Why the pure baker map u fails** (Attempt 1 on the target node): g = id forces ρ synchronous, hence finitary, hence trivial.
- **What is open:** a single u′ serving all odd q is the target `lifted-odd-roots-of-the-odometer-doubled-by-the-baker-map`. The g above lives at the level of the q-partition. The canonical level-q_n formulas for a tower q_1 | q_2 | … are not compatible, because they move different letters to the front.
