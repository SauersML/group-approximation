# sk-strong-5 plan: a second family with a strictly shorter complete proof

Lane `sk-strong-5` (wave 8, ROSTER-F). The lens: a SECOND family of infinite simple Kazhdan LEF groups whose complete
proof of every headline property is strictly shorter than the note's. If it is shorter, it could replace or accompany
the headline.

## Target
- The note (main e80dcf20ad, rev2) proves:
  - G_X = EL_3(LC(X,F_2)⋊Z) is infinite, f.g., simple and Kazhdan;
  - it is a marked limit of finite simple SL_{3N}(F_2) whose Cayley graphs are expanders;
  - so it is LEF, sofic and hyperlinear.
- Its §1 is about 115 source lines. The shortest reviewed rewrite is sk-open-2 v5, at 67 lines.
- The benchmark: a family whose complete proof of ALL of these is shorter than v5, with nothing cited that the note
  does not already cite.

## Candidates to test (honest length accounting, each with its obstruction)
1. The lamplighter host over Z: L = Z/2 ≀ Z acting on 2^Z. Identify R = LC(2^Z,F_2)⋊L with the algebraic
   Bernoulli-shift crossed product of the F_2-CAR algebra, (⊗_Z M_2(F_2)) ⋊ Z.
   - The full shift has every configuration legal, so LEF needs no periodic-word lemma.
   - Look for finite SIMPLE models: cyclically permuting the tensor factors of (F_2^2)^{⊗N} should give surjections onto
     M_{2^N}(F_2), and so marked limits of SL_{3·2^N}(F_2) with expanders.
   - Simplicity needs towers over a topologically free action (a density patch).
2. Toeplitz over Z², rotation codings over Z^d, and the Γ-version of the note (Theorem G): more general, not shorter.
3. EL_2 over subshift rings (sk-el2): needs the EJZK grading criterion, so longer.
4. Published sandwich theorems (Bass–Vaserstein stable rank, Preusser exchange rings, Stepanov (b)) for a family whose
   ring fact is short to verify. Check which ring facts are known.
5. "Simplicity for free" from limits of finite simple groups. Expect a firewall: SL_3(Z) is a marked limit of the finite
   simple groups SL_3(F_p), p ≡ 2 mod 3, has (T), and is not simple.
6. PSL_3 of an infinite f.g. division ring: its existence is a famous open problem, so this is a firewall only.

## Deliverables
- An artifact with the length table, the candidate proofs, and firewalls.
- Cairn nodes for the new facts:
  - the CAR identification;
  - the qubit-shift finite simple models of EL_3 of the CAR crossed product;
  - the marked-limit firewall.
- A §6 proposal, with the expected verdict "no replacement", unless candidate 1 or 4 is strictly shorter.

## Non-duplication
- sk-universal-embedding-b owns the lamplighter host for every LEF Δ (reviewed PASS twice). This lane adds only the Δ = Z
  CAR picture, the finite simple models, and the length comparison.
- sk-open-2 and sk-simpler-* own shortening §1 of the subshift proof.
