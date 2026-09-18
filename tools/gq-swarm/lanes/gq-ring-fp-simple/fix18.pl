undef $/; $_ = <STDIN>;
s/Since `T` and `K`\n  are localizations of `D`/Since `T` and `K = Q(t)`\n  are localizations of `D`/;
s/re-review by\n`gq-referee-b` pending\)\./and by `gq-referee-b`,\n852a0771f)./;
s/The coefficient ring `B⁺` of a single-register completion, the `σ`-closure of registers,\nindicators, reciprocals and resolvents, is a finite product of such rings, one per type\./The coefficient ring `B⁺` of a single-register completion, the `σ`-closure of registers,\nindicators, reciprocals and resolvents, is a finite product of such rings *provided it\ncontains every point indicator `δ_n`*. That is not automatic (referee b, A1): for `R_L` the\ngenerated ring is `Q[N][(N+c)^(-1)]`, with no idempotents, and part 4 fails there for the\nreset./;
print;
