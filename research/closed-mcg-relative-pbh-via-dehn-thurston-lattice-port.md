---
rg: 2
id: closed-mcg-relative-pbh-via-dehn-thurston-lattice-port
kind: route
title: Adjoin the Dehn–Thurston translation lattice to Mod(S_g) on ML_Z, take a finitely presented lattice host, and glue a Houghton port along the translations
target: closed-mapping-class-groups-satisfy-relative-pbh
requires:
  - mapping-class-ports-are-dehn-thurston-translations-not-twists
  - closed-mcg-lies-in-an-fp-dehn-thurston-lattice-host
  - cofinite-abelian-subgroups-give-relative-pbh
---

1. **The embedding.** By `mapping-class-ports-are-dehn-thurston-translations-not-twists`, items 2
   and 3, `Mod(S_g) ≅ Φ Mod(S_g) Φ^-1 ≤ D_g ≤ Sym(Z^N)`. The action is faithful, since `Mod(S_g)`
   acts faithfully on `ML_Z` for `g ≥ 3`. For `g = 2` the hyperelliptic involution acts trivially,
   so the route covers only the torsion-free finite-index subgroups of `Mod(S_2)`, which embed.
2. **The host.** By `closed-mcg-lies-in-an-fp-dehn-thurston-lattice-host` (OPEN), some
   finitely presented `D ⊇ D_g` acting on `Z^N` has finitely generated stabilizers. The translations
   `T ≅ Z^N ≤ D` act regularly.
3. **The port.** By `cofinite-abelian-subgroups-give-relative-pbh`, item 2, `Mod(S_g) ≤ D` satisfies
   relative PBH. ∎
