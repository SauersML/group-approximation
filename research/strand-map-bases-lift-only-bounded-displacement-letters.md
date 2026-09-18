---
rg: 2
id: strand-map-bases-lift-only-bounded-displacement-letters
kind: claim
title: Over a base of eventual strand maps such as H_n(E_2), the lifting criterion certifies a rho-letter only if the enumeration gives it eventually periodic displacement, so over that base it reaches only virtually cyclic inputs
requires:
  - fsym-extensions-lift-fp-via-pair-transitive-stable-subgroups
  - regular-enumeration-displacement-bounds-growth
distinct_from:
  free-shift-houghton-like-envelopes-are-not-fp: that shows H_n(E_nu(P)) is not finitely presented for free-shift nu; this shows that one sufficient mechanism, over the Houghton base, cannot see any input beyond the virtually cyclic ones, whatever nu is.
  finite-ray-shift-envelopes-require-virtually-cyclic-input: that says E_nu(P) fits inside some E_m only for virtually cyclic P; this says the lifting criterion, with every conjugation-stable subgroup taken inside a strand-map base, needs each rho-generator to be eventually periodic by itself.
  fp-bounded-displacement-e2-envelopes-are-eventually-periodic: that assumes bounded displacement and finite presentation, and concludes eventual periodicity; this assumes only that one lifting certificate exists, and concludes periodic displacement.
---

**ESTABLISHED** (lane proof, elementary, proved below; not independently reviewed; no priority claimed).

**Setting.**
- `P` is infinite and finitely generated, `nu : P -> N` is a bijection, and `n >= 1`.
- `Γ = H_n(E_nu(P))` acts on `X = [n] x N`. Each ray splits into its even and odd strands, and each strand is
  identified with `N`, as in `free-shift-houghton-envelopes-local-stability-proof`.
- Write `E_k` for the even strand of ray `k`, `s` for the strand shift `m -> m+1`, and `lambda_g(nu(h)) = nu(gh)`.
- `y = rho^(k)_g` acts on `E_k` by `lambda_g` and fixes every other point.
- A permutation of `X` is an *eventual strand map* if, outside a finite set, it sends each strand `j` to one strand
  `j'` by `m -> m + c_j`. Every element of `H_n(E_2)` is one (same source).

**Statement.** Let `K <= Γ` consist of eventual strand maps, and let `g ≠ 1`. Suppose some finitely generated
`C <= K` with `y C y^-1 <= K` has finitely many orbits on the 2-element subsets of `X`. Then for some `a ≠ 0`,

    lambda_g(m + a) = lambda_g(m) + a   for all large m.

So on `E_k` the displacement `lambda_g(m) - m` is eventually `a`-periodic, and in particular bounded.

**Corollary.** Let `S` generate `P`. Suppose `H_n(E_nu(P)) = <K, rho^(k_g)_g : g ∈ S>` is certified by
`fsym-extensions-lift-fp-via-pair-transitive-stable-subgroups`, with every `C_i` inside `K` and `K` a group of
eventual strand maps (for example `K = H_n(E_2)`, `n >= 2`). Then every `lambda_g`, `g ∈ S`, has bounded
displacement. By `regular-enumeration-displacement-bounds-growth`, `P` has linear growth, so `P` is virtually
cyclic (a finitely generated group of linear growth is virtually cyclic).

**Corollary 2 (one letter already decides).** If `P` is not virtually cyclic, then over a strand-map base no letter
`rho^(k)_g` with `g` of infinite order has a certificate, whatever `nu` is.

*Proof.* By the statement, for `m >= M` we have `lambda_g(m) = m + delta(m)` with `delta` `a`-periodic.
- Far out, `lambda_g` maps each residue class `r` mod `a` by translation into the class `tau(r) = r + delta(r)`.
  Translations preserve density and `lambda_g` is a bijection, so `tau` is a permutation of `Z/a`.
- Let `M' = M + max|delta|`, and suppose some orbit `O` of `lambda_g` lies in `[M', ∞)`. The residues of its
  points then follow `tau` forward and `tau^-1` backward, around one `tau`-cycle of some length `p`. Along it,
  `m_(i+p) = m_i + Δ` for a fixed `Δ`.
- If `Δ = 0`, the orbit is finite. But `g` has infinite order and the action is free, so there are no finite
  orbits. If `Δ ≠ 0`, the orbit goes below `M'` in one direction. So every orbit meets `[1, M')`, and there are
  finitely many orbits.
- The orbits of `lambda_g` are the cosets `<g>h`. So `[P : <g>] < ∞`. ∎

**Proof.**
1. *Every `c ∈ C` sends `E_k` to itself.* Suppose `c` sends `E_k` to a strand `S ≠ E_k` by `m -> m + a'`. For all
   but finitely many `x ∈ E_k`, the point `lambda_g^-1(x)` is far out on `E_k`, `c` sends it to
   `lambda_g^-1(x) + a'` on `S`, and `y` fixes that point. So `y c y^-1(x) = lambda_g^-1(x) + a'` on `S`. Now
   `y c y^-1 ∈ K` is an eventual strand map, so for almost all `x` it is `x + b` on `S`. Hence `lambda_g^-1`
   agrees with `m -> m + (b - a')` outside a finite set. A permutation of `N` that is eventually a translation is
   eventually the identity, so `lambda_g^-1` has finite support. But `P` acts freely and `g ≠ 1`, so `lambda_g`
   moves every point. Contradiction.
2. *Some generator of `C` shifts `E_k`.* By step 1, each `c ∈ C` is eventually `m -> m + a_c` on `E_k`. If
   `a_c = 0` for every `c` in a finite generating set, then all of `C` fixes every point of `E_k` beyond some `M`.
   So the pairs `{x, x'}` of such points are fixed by `C`, one orbit each. That gives infinitely many orbits,
   against the hypothesis. So some `c ∈ C` has `a = a_c ≠ 0`.
3. *The near relation.* On far points of `E_k`, `y c y^-1 = lambda_g s^a lambda_g^-1`. It lies in `K` and maps
   far points of `E_k` into `E_k`, so it is eventually `s^b` there. Near indices are additive and vanish on
   permutations, so comparing them gives `b = a`. Hence `lambda_g s^a ≡ s^a lambda_g` near infinity, which is the
   displayed identity. ∎

## Reading

- The obstruction is local to one letter. It does not use finite presentation of anything, only that `C` sits in a
  strand-map base.
- The zigzag enumeration of `Z` passes the necessary condition: `lambda_1` has eventually 2-periodic displacement
  (`+2` on one parity class, `-2` on the other). There the envelope is finitely presented anyway
  (`zigzag-houghton-like-envelopes-are-virtually-houghton`).
- To go beyond virtually cyclic inputs along this route, one needs at least one of the following:
  - the iterated form of hypothesis (c), with `C_i` inside `<K, earlier rho-letters>`;
  - a finitely presented base `K ⊇ FSym(X)` inside `Γ` whose elements have unbounded displacement on the
    `rho`-strands.

  Neither is available on main. The natural candidate base, `FSym(X)` together with `rho(P)` and its flip
  conjugate on the odd strands, is a pair of lampshufflers `FSym(P) ⋊ P`. Its single remaining letter is the
  slide. For a finite-index `A <= P`, the slide conjugates `rho(A)` back into that base only if a power of `s`
  conjugates `lambda(A)` into `lambda(P)` near infinity. `one-ended-shell-inputs-admit-no-shift-normalizing-enumeration`
  excludes this for `A = P` when `P` is one-ended. Proper finite-index `A` are not checked here. A multi-ended
  input would first need its lampshuffler to be finitely presented, which is not known here.
