# Lane hl-atiyah: parity obstruction to the norm equation for the level-15 lattice (2026-09-13)

## Boundary on main (pinned there, not re-pinned here)
- Farkas--Linnell and Fisher--Ng: subgroups of torsion-free compact p-adic analytic
  groups satisfy Strong Atiyah over C (`p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah`),
  which covers every subgroup of Gamma(3) and Gamma(4) in SL_3(Z)
  (`congruence-kazhdan-groups-satisfy-strong-atiyah`).
- Locally indicable groups (Jaikin-Zapirain--Lopez-Alvarez), Linnell's class C, and
  Schick's elementary amenable extensions: see `strong-atiyah-torsion-free` and its
  citation nodes.
- SL_3(Z): denominator 48 established, 24 open, reduced to denominator 8 on K_I.
- The torsion-free test case: the level-15 lattice H embeds in no torsion-free profinite
  group, its ranks lie in (1/2)Z, and Strong Atiyah for H is the twisted norm equation
  sigma(a) a = h^2 in D_C(N).

## New here
1. `twisted-norm-equation-dies-under-invariant-parity-character`: an h-invariant
   homomorphism D(N)^x -> Z/2 nontrivial on h^2 kills every solution.
2. `level15-lattice-has-invariant-parity-character-detecting-h2`: at group level such a
   character exists, and every Z/2 character of N factors through reduction mod 5 to K,
   of order 16.
3. OPEN `level15-parity-character-extends-to-linnell-division-ring`, and OPEN
   `level15-torsion-free-lattice-satisfies-strong-atiyah`, with two routes.

## Verbatim computation output (MSI, python3.12)
```
|P5| = 32
|K| = 16
|Phi(K)| = 2  dim V = log2(|K|/|Phi|) = 3
|V| = 8  results over all M with chi(M)=1 (M^2 in image(1+sigma)?, |image|): {(False, 2)}
```

## Not done
- No Lueck-approximation numerics: the finite quotients have order at least 16 * 15^8,
  and the norm equation concerns non-group elements, so small congruence quotients would
  certify nothing.
- No extension of the character to D_C(N)^x.
