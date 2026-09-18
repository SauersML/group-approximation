---
rg: 2
id: bs-quotients-keeping-a-commutator-need-distortion
kind: claim
title: In a quotient of BS(m,n) (gcd(m,n) = 1, 2 ≤ |m| < |n|) that keeps [tat^-1, a], the image of a is a distorted element of infinite order; so no such quotient is torsion-by-(a group with undistorted cyclic subgroups) or torsion-by-PL, which excludes every Thompson-, Stein-, Houghton- and hyperbolic-type isolated host
requires:
  - bs-quotients-keeping-a-commutator-have-a-commensurated-core
  - coprime-baumslag-solitar-images-in-va-are-metabelian
  - char-p-linear-groups-have-no-distorted-cyclic-subgroups
distinct_from:
  coprime-baumslag-solitar-images-in-va-are-metabelian: that is the special case of a quotient inside VA; this allows a torsion normal subgroup below and any host whose cyclic subgroups are undistorted, and adds piecewise linear hosts by a derivative argument that uses no distortion theorem.
  bs-quotients-keeping-a-commutator-have-a-commensurated-core: that is the structure theorem for such quotients; this is the host exclusion it yields.
---

**ESTABLISHED** (lane proof below, elementary modulo the cited undistortion theorems, not
reviewed; no priority claimed).

**Setting.** `G = BS(m,n)`, `gcd(m,n) = 1`, `2 ≤ |m| < |n|`, `c = [tat^{-1}, a]`, `Q = G/N` with
`c ∉ N`, `α = aN`, `τ = tN`.

**Statement.**
1. **Forced distortion.** `α` has infinite order and `|α^{n^k}|_{α,τ} ≤ 2k + |m|^k` for all `k ≥ 0`.
   So `⟨α⟩` is distorted in `Q`, and in every finitely generated group containing `Q`.
2. **Undistorted hosts.** Let `L ⊴ Q` be a torsion subgroup. Then `Q/L` does not embed in any
   finitely generated group `H` whose infinite cyclic subgroups are all undistorted. Classes of such
   `H`, cited and not re-proved:
   - hyperbolic groups;
   - groups acting properly and cocompactly on CAT(0) spaces;
   - `VA`, and hence `F`, `T`, `V`, `T̄` and the Higman--Thompson groups `V_{d,r} ≤ V`
     (Burillo--Felipe, arXiv:2605.09763v1, unrefereed, as quoted in O4 of
     `gl-n-q-embeds-in-fp-simple-group`);
   - finitely generated linear groups over fields of positive characteristic
     (`char-p-linear-groups-have-no-distorted-cyclic-subgroups`);
   - finitely generated abelian groups.
3. **Piecewise linear hosts** (no distortion input; `m ≠ n` suffices on the interval, `|m| ≠ |n|` on the circle).
   - Every homomorphism from `BS(m,n)` to `PL_+([0,1])` kills `a`.
   - Every homomorphism to `PL_+(S^1)` sends `a` to an element of finite order.

   Here PL maps have finitely many breakpoints and arbitrary slopes. So `Q/L` (with `L` torsion as in
   item 2) is not a subgroup of either group. This covers the Stein--Thompson groups `F_{n_1,…,n_k}`,
   `T_{n_1,…,n_k}` (among them `F_{2,3}`, `T_{2,3}`, whose slopes `2^i3^j` are the natural home of the
   ratio `3/2`) and all Bieri--Strebel groups.
4. **Excluded isolated groups.** None of the following is a quotient of `BS(2,3)` in which `c`
   survives:
   - finitely presented subgroups of `V` containing a locally moving simple group;
   - `FSym(Ω) ⋊ V`;
   - Houghton's groups `H_n` (`FSym`-by-`Z^{n−1}`);
   - subgroups of Stein--Thompson groups;
   - any extension of a locally finite group by a group from items 2--3.

**Proof.**
1. Infinite order is item 1 of `bs-quotients-keeping-a-commutator-have-a-commensurated-core`. By
   induction, `t^k a^{m^k} t^{-k} = a^{n^k}`: the step is
   `t^{k+1} a^{m^{k+1}} t^{-k-1} = t (t^k a^{m^k} t^{-k})^m t^{-1} = t a^{m n^k} t^{-1}
   = (t a^m t^{-1})^{n^k} = a^{n^{k+1}}`. So `|α^{n^k}| ≤ 2k + |m|^k = o(|n|^k)`. In a finitely
   generated overgroup `H`, `|·|_H ≤ C|·|_Q`.
2. If the image `ᾱ` of `α` in `Q/L ≤ H` had infinite order, item 1 (applied in `Q/L`, where the same
   bound holds) would make `⟨ᾱ⟩` distorted in `H`. So `ᾱ^j = 1` for some `j ≥ 1`. Then `α^j ∈ L` is
   torsion and `α` has finite order, which contradicts item 1.
3. *Interval.* Let `ψ(a) = f`, `ψ(t) = g` in `PL_+([0,1])`.
   - For `k ≠ 0`, `Fix(f^k) = Fix(f)` (an increasing homeomorphism of an interval with `f(x) > x` has
     `f^k(x) > x`), so `supp f^m = supp f = supp f^n`.
   - `g` maps `supp f^m` onto `supp f^n`, so `g` permutes the finitely many components of `supp f`.
     Being increasing, it fixes each component and its endpoints.
   - Let `J = (p, q)` be a component, and let `λ > 0` be the right derivative of `f` at `p`. Since
     `f` is linear near `p⁺` and `J ⊆ supp f`, `λ ≠ 1`.
   - `g` fixes `p`, and one-sided derivatives obey the chain rule at a common fixed point. So
     `λ^m = (g f^m g^{-1})'(p⁺) = (f^n)'(p⁺) = λ^n`, and `λ = 1` because `m ≠ n`. This is a
     contradiction, so `supp f = ∅`.

   *Circle.* Rotation number is conjugation-invariant and `rot(f^k) = k·rot(f)` mod 1, so
   `(n − m)·rot(f) ∈ Z` and `rot(f)` is rational. Then some power `h = f^q` has a fixed point.
   - Again `Fix(h^k) = Fix(h)` for `k ≠ 0`, and `g h^m g^{-1} = h^n`.
   - `g` permutes the finitely many arcs of `supp h`, so some `g^r` fixes each arc and its endpoints.
   - `g^r h^{m^r} g^{-r} = h^{n^r}` (as in 1), and the derivative argument at an arc endpoint gives
     `λ^{m^r} = λ^{n^r}`, so `λ = 1`. This is a contradiction, so `h = 1` and `f` has finite order.

   With `L` torsion, `ᾱ` of finite order again forces `α` of finite order.
4. `V` and its subgroups lie in `VA`. `FSym(Ω) ⋊ V` and `H_n` are extensions of locally finite
   groups by `V` and by `Z^{n−1}`. Stein--Thompson groups are PL. Apply items 2 and 3.

**What remains.** An isolated group near `BS(2,3)` must contain distorted elements `α` with
`⟨α⟩` commensurated. By item 5 of `bs-quotients-keeping-a-commutator-have-a-commensurated-core`,
when its monolith is finitary, `α` is also locally periodic. Hosts not excluded here:
- Brin--Thompson `nV` (`n ≥ 2`, which contain distortion elements);
- piecewise projective groups (parabolic germs `x ↦ x + c` are conjugated to `x ↦ x + 3c/2` by
  `x ↦ 3x/2`);
- Röver--Nekrashevych groups over odometers sensitive to both 2 and 3
  (`odometer-generators-carry-no-nonsolvable-baumslag-solitar`);
- the rigid permutation groups of Bux--Llosa Isenrich--Wu, and the subgroup `RP^Δ` of Remark 1 of
  the structure node.
