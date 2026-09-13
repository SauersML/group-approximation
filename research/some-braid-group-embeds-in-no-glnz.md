---
rg: 2
id: some-braid-group-embeds-in-no-glnz
kind: claim
title: Some braid group B_N has no injective homomorphism into any GL_m(Z)
---

There is `N` such that no homomorphism `B_N -> GL_m(Z)`, for any `m`, is
injective. This is the negative answer to Zaremsky Problem 3.2
(`zaremsky-3-02-braid-groups-embed-in-glnz`). Such an `N` is at least 4
(`braid-groups-on-at-most-three-strands-embed-in-glnz`), and then every `B_n`
with `n >= N` fails too, since `B_N <= B_n`.

## Attempts

1. **Necessary conditions that braid groups already satisfy.** A finitely
   generated subgroup of `GL_m(Z)` is residually finite, virtually residually
   `p` for every prime `p`, and has polycyclic solvable subgroups; it satisfies
   the Tits alternative. `B_n` passes every one of these tests:
   - it is linear over `Q(q, t)`, hence residually finite with the Tits
     alternative;
   - `P_n` is residually torsion-free nilpotent (Falk–Randell), and finitely
     generated torsion-free nilpotent groups are residually `p` for every
     prime `p`;
   - its solvable subgroups are virtually abelian of bounded rank
     (Birman–Lubotzky–McCarthy);
   - it has a finite classifying space.
   None of these tests can give the negative answer.
2. **Discreteness.** What is special about `GL_m(Z)` is that a subgroup's image
   is discrete in `GL_m(R)`, so it acts properly on `SL_m(R)/SO(m)`. Rigidity
   theorems for semisimple actions of mapping class groups on CAT(0) spaces do
   not apply directly, because integral images may contain unipotent, hence
   parabolic, elements.
3. **Two-generator tests for RAAG embeddings.** These concern only the
   virtual-special route to the affirmative answer, not Z-linearity itself.
   Sufficiently high powers of mapping classes generate RAAGs (Koberda), so
   such tests cannot come from powers.
