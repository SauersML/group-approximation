---
rg: 2
id: free-shift-houghton-like-envelopes-are-not-fp
kind: claim
title: If P*<s> embeds as the near shift group then no Houghton-like envelope H_n(E_nu(P)) is finitely presented, although for n >= 2 its germ group is; finite presentation forces finitely many relations to pin nu down up to right translation
distinct_from:
  houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group: that proves the germ group of H_n(E_nu(P)) finitely presented for these enumerations (n >= 2); this proves the group itself is not, so finite presentation does not lift from germs.
  mz-envelope-fp-forces-two-sided-fg-near-index-kernel: that kills n = 1 for free-shift enumerations through the germ group (two-sided window); this kills every n >= 1 by a local-stability argument that does not look at germ groups.
  free-shift-shell-envelopes-are-not-finitely-presented: that is the same hypothesis for the Cantor shell envelope, proved by a presentation argument; this is the permutation envelope on n rays.
  houghton-like-envelopes-lift-finite-presentation-from-germs: that is the lifting claim; P = Z with a free-shift enumeration and n = 3 is a counterexample to it.
---

**ESTABLISHED** by `free-shift-houghton-envelopes-local-stability-proof`, a lane proof that is elementary and not
independently reviewed.

**Setting.**
- `P` is infinite and finitely generated, and `nu : P -> N` is a bijection.
- `E_nu(P) = <rho(P), E_2>`, with near shift group `R_nu = <lambda(P), s>`, as in
  `mz-envelope-germ-group-is-an-antitwisted-fiber-product`.
- `Γ_nu = H_n(E_nu(P))` for `n >= 1`, with `H_1(E_nu(P)) = E_nu(P)`.
- `K = H_n(E_2)` is independent of `nu` (for `n = 1`, `K = E_2`).
- `rho^(k)_g` is `rho(g)` acting on ray `k`, i.e. `[∅, (1..rho(g)..1), ∅]` (Observation 5.1).
- Then `Γ_nu = <K, rho^(k)_g : k <= n, g in a finite generating set of P>`. This follows from Proposition 5.10 of
  `houghton-like-groups-are-strongly-shift-similar` for `n >= 2`, and is the definition of `E_nu(P)` for `n = 1`.

**Statement.**
1. **Local stability.** Suppose the canonical map `P * <s> -> R_nu` is injective. Let `w` be any word in these
   generators with `w = 1` in `Γ_nu`. Then there is a finite set `S ⊂ P` such that `w = 1` also in `Γ_nu'` (same
   `K`, the letters `rho^(k)_g` read with `nu'`) for every bijection `nu'` agreeing with `nu` on `S`.
2. **Not finitely presented.** Under the same hypothesis, `Γ_nu = H_n(E_nu(P))` is not finitely presented, for
   every `n >= 1`.
3. **Finite determination (no hypothesis on `nu`).** If `H_n(E_nu(P))` is finitely presented, then there is a
   finite set `R` of words, each trivial for `nu`, with the following property: every bijection `nu'` for which
   all words of `R` are trivial satisfies `nu'(h) = nu(hc)` for all `h`, for some fixed `c in P`.
4. **Counterexample to lifting.** Take `P = Z`, `nu` with `Z * <s> -> R_nu` injective, and `n = 3`. By
   `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group` item 3, the germ group
   `H_3(E_nu(Z))/FSym` is finitely presented, since `R_nu ≅ F_2`. By item 2, `H_3(E_nu(Z))` is not. So
   `houghton-like-envelopes-lift-finite-presentation-from-germs` is false. Such `nu` exist by
   `regular-enumerations-can-make-near-shift-free-product`, whose elementary route this lane read; that node carries
   no status line on main.

**Reading.**
- Along any permutation envelope route, the free-shift enumerations are dead in every form: n = 1, every
  `n >= 2`, and the Cantor shell. That is so even though the germ-level obstruction disappears for `n >= 2`.
- Item 3 is the general necessary condition. Finitely many relations of `Γ_nu` must determine `nu` "at
  infinity". Every successful enumeration must carry near relations that are not stable under changing `nu` far
  out. The zigzag enumeration of `Z` has them: `E_nu(Z)` is finitely presented
  (`zigzag-cyclic-shift-envelope-is-finitely-presented`).
