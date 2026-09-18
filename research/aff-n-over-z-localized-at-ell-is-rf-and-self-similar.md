---
rg: 2
id: aff-n-over-z-localized-at-ell-is-rf-and-self-similar
kind: claim
title: For a prime l, Aff_n(Z_(l)) — which contains every GL_n(Z[1/P]) with l not in P — is residually finite and acts faithfully and self-similarly by finite-state automorphisms on the l^n-ary tree
distinct_from:
  pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori: that studies the Mobius self-similar group Gamma_p, which contains Aff_1(Z_(p)) but is not finite-state; this is the affine group in every rank n, which is finite-state.
  rational-linear-groups-satisfy-boone-higman: that uses Zaremsky's finitely generated self-similar affine groups over Z[1/m]; this is the non-finitely-generated affine group over the local ring Z_(l), which contains the groups of every co-nonempty infinite P at once.
  gl-n-q-embeds-in-fp-simple-group: that root's O1 says GL_n(Q) has no residually finite overgroup; this shows O1 is exactly the case of all primes, since omitting one prime l already gives a residually finite self-similar group.
  fg-piecewise-linear-hosts-omit-natural-gl-n-q: that is about derivative cocycles of finitely generated hosts; this records the natural affine action of one non-finitely-generated group.
---

**ESTABLISHED** through `aff-n-over-z-localized-at-ell-is-rf-and-self-similar-proof`.
Lane proof, not independently reviewed. Elementary; no priority is claimed.

**Statement.** Let `l` be a prime and `Z_(l) = {a/b in Q : l ∤ b}`. Let
`Aff_n(Z_(l)) = Z_(l)^n ⋊ GL_n(Z_(l))` act on `Z_l^n` by `x -> gx + b`. Then:
1. **Residually finite.** `Aff_n(Z_(l))` is residually finite, and so is its
   subgroup `GL_n(Z[1/P])` for every set `P` of primes with `l ∉ P`.
2. **Self-similar.** The action preserves the cosets of `l^k Z_l^n`. So it is an
   action on the rooted `l^n`-ary tree whose level `k` is `(Z/l^k)^n`. The action
   is faithful, and the group is self-similar: every section of `x -> gx + b` is a
   map `y -> gy + c` with the same `g` and some `c in Z_(l)^n`.
3. **Finite-state.** Every element has only finitely many distinct sections.
4. **Finitely generated subgroups see finitely many primes.** Every finitely
   generated subgroup of `Aff_n(Z_(l))` lies in `Aff_n(Z[1/m])` for some integer
   `m` prime to `l`.

**Reading.**
- **Which P are easier.** For every set `P` that misses at least one prime `l`,
  the group `GL_n(Z[1/P]) <= Aff_n(Z_(l))` is residually finite and self-similar.
  So obstruction O1 of `gl-n-q-embeds-in-fp-simple-group` holds exactly when `P`
  is the set of all primes.
- **Which P are hardest.** `GL_n(Z[1/P]) <= GL_n(Z_(l))` for all `P ∌ l`, so the
  hardest residually finite case is `P` = all primes except one, i.e.
  `gl-n-z-localized-at-ell-embeds-in-fp-simple-group`.
- **The affine route stays finite.** Part 4, with
  `infinite-prime-localizations-embed-in-no-fg-linear-group`, shows that the
  affine self-similar hosts of `rational-linear-groups-satisfy-boone-higman` reach
  only `GL_n(Z[1/m])`. A finitely presented self-similar host for an infinite `P`
  (`aff-n-z-localized-lies-in-fp-self-similar-group`) would have to be non-linear.
