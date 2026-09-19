undef $/; $_ = <STDIN>;
s/(  prime-shift-affine-group-a1-has-fg-point-stabilizer: [^\n]*\n)---/$1refuted_by:\n  - prime-shift-affine-group-a1-is-not-finitely-presented\n---/;
s/\*\*OPEN\.\*\* The group `A_1 = <x -> x\+1, x -> 2x, x -> -x, σ> <= Sym\(Q\)` of\n`gl-n-q-lies-in-prime-shift-permutation-group` is finitely presented\./**REFUTED (2026-09-18)** by `prime-shift-affine-group-a1-is-not-finitely-presented`.\nDeep-denominator germs map `A_1 \/ <<τ>>` onto `Z ≀ Z`, with kernel of order at most `2`,\nso no dilation lies in `<<τ>>` and `A_1` is not finitely presented. That holds whether or\nnot `Π_1 -> A_1` is injective.\n\n**Refuted statement.** The group `A_1 = <x -> x+1, x -> 2x, x -> -x, σ> <= Sym(Q)` of\n`gl-n-q-lies-in-prime-shift-permutation-group` is finitely presented./;
print;
