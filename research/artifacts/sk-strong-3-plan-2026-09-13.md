# sk-strong-3 plan: one simple Kazhdan group that contains every finitely generated linear group

Lane sk-strong-3 (SK swarm, wave 6), 2026-09-13. Lens: the most astonishing corollary for a non-specialist.

## Target
**Universal envelope.** There is an infinite, finitely generated, simple group G with property (T) that is LEF, so
sofic and hyperlinear, and that contains a copy of every finitely generated residually finite group with solvable
word problem. In particular G contains:
- every finitely presented residually finite group (McKinsey–Mal'cev: solvable word problem);
- every finitely generated linear group over a field (Mal'cev: residually finite; Rabin: solvable word problem):
  SL_n(Z) for all n, surface groups, braid groups, right-angled Artin groups, Coxeter groups, hyperbolic 3-manifold
  groups;
- mapping class groups, and every finite group.

## Why it is astonishing and high impact
- A single finitely generated group with no nontrivial normal subgroups and Kazhdan's rigidity property, every finite
  piece of which is a piece of a finite group, holds all these groups at once.
- Optimality: no finitely generated group contains every f.g. RF group, because a f.g. group has countably many f.g.
  subgroups while there are continuum many f.g. RF groups. So a countable, recursion-theoretically defined class is the
  most one can ask for.
- A stretch goal adds computability: G with solvable word problem containing every f.p. RF group. McKinsey's algorithm
  is uniform, so this is not blocked by the Boone–Rogers obstruction.

## Route
1. The class C of f.g. RF groups with solvable word problem is countable up to isomorphism (recursive relator sets).
2. P = the free product of representatives of C is a countable RF group (Gruenberg 1957).
3. P embeds in a finitely generated RF group W. Verify the literature source (Wilson 1980?) or prove it inside a
   product of finite symmetric groups.
4. Apply Theorem E of sk-universal-embedding-a (3bcc003284, unreviewed) to W:
   - W ≤ [Δ,Δ] with Δ f.g. RF (Ore);
   - X_Δ a free minimal Toeplitz subshift with window models;
   - G = EL_3(LC(X_Δ,F_2)⋊Δ), with w ↦ diag(u_w,1,1).
   Step 4 is re-checked here, since the corollary rests on it.

## Not duplicated
- sk-universal-embedding-a proved the one-group embedding, not a universal envelope.
- sk-lef-embedding-c/d/e and sk-universal-embedding-b work on LEF input.
- sk-wp-embedding (Boone–Higman form for a given group) is a neighbor of the stretch goal only; I will message it if
  both of us reach computability.

## Deliverables
- Cairn claim + route, with citation nodes for Gruenberg, the countable-to-f.g. RF embedding, and McKinsey/Mal'cev.
- A §6 proposal: at most one sentence and a short proof sketch, conditional on a PASS for Theorem E.
