undef $/; $_ = <STDIN>;
s/Take `P_f ∈ Z\[Y_ρ\]` to be the product\nof that term's inequations, times the resolvents of `f`\./Take `P_f ∈ Z[Y_ρ]` to be the product\nof ALL nonzero polynomials occurring in the Boolean description of `f`'s cells, resolvents\nincluded (referee b, W1). Then `{P_f ≠ 0}` is the atom where every such polynomial is\nnonzero. That atom lies in the equation-free term, hence in `C_f`./;
s/So the capacity-chain presentation stays non-simple after adding any finitely many\ncommutative relations true in its concrete model/So the capacity-chain presentation stays non-simple after adding any finitely many\nrelations from `ℬ` true in its concrete model/;
print;
