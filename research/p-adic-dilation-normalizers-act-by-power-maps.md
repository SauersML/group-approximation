---
rg: 2
id: p-adic-dilation-normalizers-act-by-power-maps
kind: claim
title: A homeomorphism of Z_p, or of a ball around 0, that conjugates the dilations by a rank-three group of rational units into rational dilations acts on them by a rational power map, so no tree automorphism shifts three primes
distinct_from:
  prime-shift-dilation-normalizers-are-nowhere-continuous: that shows a permutation of Q normalizing all positive dilations by a prime shift is discontinuous for the real and every p-adic topology; this concerns homeomorphisms of Z_p, and tree automorphisms of T_p, normalizing only a rank-three group, and uses p-adic transcendence to force a power map.
  shell-mobius-extensions-see-finitely-many-primes: that kills spinal extensions of Γ_p(1) that are Möbius on shells; this kills every element of Aut(T_p), Möbius or not, that permutes three primes among the dilations.
  rational-iwahori-group-lies-in-fp-self-similar-group: that is the open target; this rules out the prime-shift device of K_n and A_1 as a way to supply the dilations d_q inside any Λ <= Aut(T_p).
artifacts:
  - research/artifacts/gq-referee-a-p-adic-dilation-normalizers-act-by-power-maps.md
  - research/artifacts/gq-referee-b-p-adic-dilation-normalizers-act-by-power-maps.md
---

**ESTABLISHED (2026-09-18)** through
`p-adic-dilation-normalizers-act-by-power-maps-proof`. Lane proof, refereed PASS
by `gq-referee-a` (proof gaps) and `gq-referee-b` (citations and scope); nits
applied. The one non-elementary input is Serre's p-adic six exponentials
theorem, pinned at source by `gq-referee-b`: J.-P. Serre, *Dépendance
d'exponentielles p-adiques*, Sém. Delange--Pisot--Poitou 7 (1965/66), exposé 15,
Théorème 1, p. 15-02.

**Setting.**
- `p` is a prime and `d_u(z) = uz` for `u in Z_p^x`.
- `Q_0 <= Q^x ∩ Z_p^x` is a group of rational `p`-adic units containing three
  multiplicatively independent elements, for example three distinct primes
  other than `p`.
- `U = p^N Z_p` is a ball around 0, and `c : U -> U'` is a homeomorphism onto an
  open subset of `Z_p`. The case `U = Z_p`, `c in Aut(T_p)`, is included.
- There is a map `β : Q_0 -> Q^x ∩ Z_p^x` with `c(u z) = β(u) c(z)` for all
  `u in Q_0` and `z in U`. That is, `c` conjugates `d_u` to `d_(β(u))` near 0.

**Statement.**
1. **Power maps only.** `β` is an injective homomorphism, and `c(0) = 0`. There
   are integers `a != 0` and `b >= 1` and a finite-index subgroup `Q_1 <= Q_0`
   with `β(u)^b = u^a` for all `u in Q_1`.
2. **No prime shifts.** For every prime `q in Q_0`, `β(q) = ±q^e` for an integer
   `e`. A germ relation already forces `c(0) = 0`. In particular, the relations
   `c d_(q_i) c^-1 = d_(q_(i+1))` for `i = 0, 1, 2`, with `q_0, q_1, q_2` distinct
   primes other than `p` and `q_3` any prime other than `p`, have no solution
   `c`, even as a germ at 0. Cycles `q_0 -> q_1 -> q_2 -> q_0` are included.
3. **Two relations.** For a cycle `q_0 -> q_1 -> q_0` the elementary part of the
   proof already gives a contradiction. For a chain `q_0 -> q_1 -> q_2` it leaves
   `(log_p q_1)^2 = log_p q_0 · log_p q_2`, which the p-adic four exponentials
   conjecture would exclude. That is Serre's case `a = b = 2`, which he states is
   unknown, and which is still open. The argument does not exclude a single
   relation `c d_q c^-1 = d_(q')`.

**Consequences for the gq hosts.**
- No element of any `Λ <= Aut(T_p)`, and no germ at 0 of an element of the
  Röver–Nekrashevych group `V_p(Λ)`, permutes three primes among the
  dilations. The prime-shift element `σ` of
  `gl-n-q-lies-in-prime-shift-permutation-group`, which does exactly that on
  `Q`, has no analogue acting on `T_p`.
- A self-similar `Λ ⊇ Γ_p` (`rational-iwahori-group-lies-in-fp-self-similar-group`)
  therefore cannot obtain infinitely many `d_q` as conjugates `c^n d_(q_0) c^-n`
  of one dilation by one element. Nor can it obtain them from any element
  normalizing a rank-three group of dilations. The dilations must come from
  elements that normalize no such group.
