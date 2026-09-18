---
rg: 2
id: contracting-rsgs-have-no-scaling-germs-at-periodic-tails
kind: claim
title: In a contracting RSG no element maps an eventually periodic point into its own tail class with depth scaling different from one, so nucleus cycles whose output tail returns to the input tail have zero lag; lag between different tail classes is not controlled, which is exactly what blocks the asynchronous extension of the conservativity lemma
requires:
  - fixed-point-free-rover-nekrashevych-elements-are-conservative
distinct_from:
  fixed-point-free-rover-nekrashevych-elements-are-conservative: that proves conservativity of fixed-point-free elements for synchronous (tree-automorphism) nuclei, and asks for a lower bound on the output lag of asynchronous nucleus maps; this proves the part of that bound forced by contraction (tail balance) and isolates the uncontrolled part.
---

**ESTABLISHED** (item 1, elementary lane proof, bh-invent-06b, 2026-09-18; not reviewed; no priority claimed). The
BBMZ notions (local action `f|_α`, `f̄(α)`, nucleus, contracting) are as in arXiv:2309.06224, read in TeX in
`finite-seed-telescope-hosts-contracting-rsg-proof`. Item 2 is a verified example (a hand computation of a five-element nucleus). Item 3 is a status report.

## Setting

- `G ≤ R_(Γ,E)` is a contracting RSG with nucleus `N` (finite).
- `x = α c^∞` is an eventually periodic point, with `c` a primitive cycle at `v = t(α)`.
- For `g ∈ G`, the local actions `g|_(αc^k)` are eventually periodic in `k`, because `x` is eventually periodic
  and `N` is finite. So the **asymptotic lag**
  `s_g(x) = lim_k ( |ḡ(αc^k)| − |α| − k|c| ) / k`
  exists. It equals the total lag, per period, of a cycle of the nucleus automaton.

## Statement

1. **Tail balance.** If `g(x)` is tail-equivalent to `x`, then `s_g(x) = 0`. Equivalently: if a nucleus map `p`
   has a cycle `p|_c = p` whose output `d = p̄(c)` satisfies `d^∞ ~ c^∞`, then `|d| = |c|`.
2. **Different tail classes are not constrained (verified example).** On the full 2-shift, let
   `p(01ω) = 0·p(ω)`, `p(1ω) = 10ω`, `p(00ω) = 11ω`. Then `p` is a homeomorphism: it maps `1C → 10C`,
   `00C → 11C` and `01C → 0C`.
   - **The nucleus.** `N = {id, p, r, q, s}` with
     - `r(0ω) = 11ω`, `r(1ω) = 0p(ω)`;
     - `q = p^(−1)`: `q(0ω) = 01q(ω)`, `q(10ω) = 1ω`, `q(11ω) = 00ω`;
     - `s(0ω) = 1ω`, `s(1ω) = 00ω`.
   - **The six BBMZ conditions** (definition before `thrm:RSGCharacterization`) hold for `N`.
     - *LocNuc:* the local actions are `p ↦ {p, r, id}` (at `01`, `0`, `1`), `r ↦ {id, p}`, `q ↦ {q, s, id}` and
       `s ↦ {id}`.
     - *RecurNuc:* `p` and `r` recur in `Nuc_p` (at `(01)^k` and `(01)^k 0`), and `q` and `s` in `Nuc_q`.
     - *InvNuc:* `Nuc_(r^(−1)) = {id, q, s}` since `r^(−1)(11ω) = 0ω` and `r^(−1)(0ω) = 1q(ω)`; `s^(−1)` is
       canonical.
     - *ProdNuc:* by direct computation, every product of two elements has its recurring local actions in `N`.
       - `p²`: `1ω→100ω`, `00ω→101ω`, `011ω→0r(ω)`, `0100ω→010ω`, `0101ω→11p(ω)`;
       - `pr`: `0ω→101ω`, `11ω→0r(ω)`, `100ω→010ω`, `101ω→11p(ω)`;
       - `rr`: `0ω→010ω`, `1ω→11p(ω)`;
       - `rq`: `0ω→111q(ω)`, `10ω→0p(ω)`, `11ω→110ω`;
       - `sp`: `1ω→000ω`, `00ω→001ω`, `01ω→1p(ω)`;
       - `qr`, `ps` and `ss` are canonical;
       - `q²`, `sq`, `qs`, `rs` and `sr` have local actions in `{q, s, p, id}`.

       The composites such as `rp` that appear at a first cone occur only finitely often, so they are not in the
       nuclei.
     - *MapNuc* and *IdNuc* are clear.
   - **Conclusion.** By `thrm:RSGCharacterization`, `{f ∈ R_2 : Nuc_f ⊆ N}` is a **full contracting RSG** containing
     `V` and `p`.
   - Along `(01)^∞`, `p|_(01) = p` with output `0`: a nucleus cycle of weight `−1` per period, which transfers the
     tail class `[(01)^∞]` to `[0^∞]`. So **contracting RSGs can have nucleus maps with unbounded negative output
     lag**, and tail balance (item 1) does not extend to cross-class cycles.
   - This is consistent with item 1: every tail-class loop has scaling 1. The only non-unit transitions are
     `[(01)^∞] → [0^∞]` (scaling `1/2`) and its inverse, and `q` has the fixed point `10^∞`.
3. **Status of the asynchronous conservativity lemma.**
   - The argument of `fixed-point-free-rover-nekrashevych-elements-are-conservative` needs the local maps along an
     orbit segment to have lag bounded independently of the segment length.
   - Item 1 provides this along tail-returning cycles only, and by item 2 no uniform bound holds in general. **The
     lag route is closed negatively.** An asynchronous extension must work with cross-class lag, for instance by
     restricting to hosts whose nucleus has no cross-class weight, as the inflation fault moves do: lag +1, then
     synchronous.
   - Even with all cycles balanced, a composite of `n` nucleus maps can accumulate lag `O(n)` through
     common-prefix stripping, so the extension also needs a composite-lag bound. **Not established.**
   - For the synchronous class (Röver–Nekrashevych) the stripping is trivial, and the lemma holds.

## Proof of 1

- Suppose `s = s_g(x) ≠ 0`, and put `μ = (|c| + s)/|c|`. Then `μ > 0`, since `|ḡ(αc^k)| → ∞` by continuity and
  injectivity, and `μ ≠ 1`.
- Write `g(x) = α′c^∞`. The prefixes `ḡ(αc^k)` of `α′c^∞` have length `|α′| + μ|c|k + O(1)`.
- Since `G` is an RSG, it contains `f` mapping `C_(α′c^j)` onto `C_(αc^j)` by the canonical similarity, for large
  `j`. Then `h = f∘g ∈ G` fixes `x`, and `s_h(x) = s`, because canonical similarities have slope 0.
- By induction, `h^n(C_(αc^k)) ⊆ C_(αc^(μ^n k + O_n(1)))`. So `s_(h^n)(x) = |c|(μ^n − 1)`.
- The local actions `q = h^n|_(αc^k)` are eventually periodic in `k`, so they recur and lie in
  `Nuc_(h^n) ⊆ N`.
- The prefix lengths satisfy `|\overline{h^n}(αc^(k+m))| = |\overline{h^n}(αc^k)| + |q̄(c^m)|`. So the asymptotic
  lag of `q` along `c^∞` is `|c|(μ^n − 1)`.
- These values are pairwise distinct for `n = 1, 2, …`, so `N` contains infinitely many maps. That contradicts
  contraction.
- **For the nucleus-cycle form,** realize `p` as `g|_β` for some `g ∈ G`, by `RecurNuc` and the construction in
  the proof of BBMZ `thrm:RSGCharacterization`. Then `g(βc^∞) = ḡ(β) d^∞`, which is tail-equivalent to `βc^∞`
  when `d^∞ ~ c^∞`, and `s = |d| − |c|`. ∎

## The rotation analogue (reported, not decided)

The open object of the conservativity node, a free group of conservative twisted-drift elements, was not
constructed, and no Hölder-type theorem was found.
- **The natural test family** is pairs of conjugates of the odometer `⟨a, a^f⟩ ≤ V_2(Z)`, with `f ∈ V`.
  - The drift of `a^f` is the coboundary of `δ_(f^(−1))`.
  - The drift of `a` is 0, and `a` is minimal, so a common potential would have to be constant. The pair's cocycle
    is therefore twisted unless `δ_(f^(−1))` is `a^f`-invariant up to a constant.
  - Whether some such pair is free and acts freely is open.
- **Interval-exchange-type constructions are not a cheap route.** A free action of `F_2` by (Cantor-coded)
  interval exchanges would in particular give `F_2 ≤ IET`. That is Katok's open question; Dahmani–Fujiwara–Guirardel
  showed free subgroups are rare (recalled, not re-read).

## Lesson for general BH

**Contraction forbids scaling germs.**
- A contracting host cannot contain an element that returns an eventually periodic tail to itself with a
  Hölder-type rescaling, since iterating it would produce infinitely many distinct nucleus maps.
- So the "exponent" of an element at a periodic tail is a trivial invariant. The lag budget of a finite nucleus is
  balanced wherever tails return.
- Lag can still be transferred between different tail classes, and a single homeomorphism of the 2-shift does
  exactly that. So the conservativity (no-ping-pong) obstruction to free actions is proved only for synchronous,
  Röver–Nekrashevych-type hosts.
- **For asynchronous hosts, such as the fault moves of inflation hosts, the missing input is a bound on composite
  lag along orbits.**
