---
rg: 2
id: ck-finite-bi-index-hole-is-kazhdan-boone-higman
kind: claim
title: The finite bi-index envelope hole implies Kazhdan Boone--Higman, and is equivalent to it when the simple core is free
distinct_from:
  bi-index-core-makes-normals-core-class-unions: that is the structural lemma about one envelope; this applies it to the quantified hole and compares the hole with conjectures.
  simple-core-bi-index-counts-coset-action-pair-orbits: that turns finite bi-index into a type (A) coset action for the twisted Brin--Thompson step; this shows that step is not needed, since finite bi-index already yields a finitely presented simple Kazhdan quotient.
  permutational-boone-higman-conjecture: that is the type (A) universality target; this is a statement about the double-coset hole and property (T) and makes no claim about type (A) actions beyond noting the hole's quotients.
artifacts:
  - research/artifacts/finite-bi-index-normal-lattice-collapse-2026-09-17.md
---

**ESTABLISHED** through `ck-finite-bi-index-hole-is-kazhdan-boone-higman-proof`.
Not independently reviewed.

## Readings of the hole

`ck-envelope-simple-core-has-finite-bi-index` asks, for each finitely
generated `G` with solvable word problem, for

    G <= S <= Gamma,   S simple,   Gamma finitely presented with property (T),
    Gamma = <<g>>_Gamma for some 1 != g in G,   |S \ Gamma / S| < infinity .

- **Free core (H-free).** `S` is any simple group containing `G`.
- **Fixed core (H-fixed).** `S` is the finitely generated simple envelope
  from `boone-higman-thompson-simple-envelope`, as in the route.
- **No (T) (H-noT).** Either reading with property (T) dropped. The route
  `boone-higman-via-finite-bi-index-envelope` never uses (T).

## Statement

1. H-fixed implies H-free, and H-free implies `kazhdan-boone-higman-conjecture`.
2. `kazhdan-boone-higman-conjecture` implies H-free. So H-free is
   **equivalent** to Kazhdan Boone--Higman.
3. H-noT (free core) is equivalent to `boone-higman-conjecture`.
4. For a single envelope, finite bi-index implies that **every** proper
   normal subgroup is finitely normally generated. So H-fixed, for the
   envelope it produces, implies the conclusion of
   `ck-envelope-has-a-finitely-normally-generated-maximal-kernel` for that
   envelope. This corrects the recorded belief that neither of the two
   open claims implies the other.
5. If in H-free the core `S` is finitely generated and its image in the
   simple quotient `T = Gamma/M` is proper, then `T` is a finitely presented
   simple Kazhdan group carrying the type (A) action `T` on `T/S`, whose
   stabilizer contains `G`.

## What this changes

The double-coset formulation does not bring "different tools" to a
different object. With the normal generator it forces Max-n and finite
presentation of every proper quotient. The hole is therefore the Kazhdan
strengthening of Boone--Higman itself. Reading H-noT is literally
Boone--Higman. The twisted Brin--Thompson group in the route is idle: the
envelope's maximal quotient is already the finitely presented simple host.

A proof of the hole must in particular produce finitely presented simple
Kazhdan hosts for all decidable groups, a problem on which no method is
recorded. A refutation of Kazhdan Boone--Higman refutes the hole in every
reading without touching Boone--Higman.
