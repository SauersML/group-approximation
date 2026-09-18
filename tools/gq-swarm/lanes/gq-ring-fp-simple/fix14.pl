undef $/; $_ = <STDIN>;
s/So the localized module is the tail ring `T'` with `T_𝔮` acting through the injective\n    substitution/So the localized module is a localization of the tail ring `T'`, with `T_𝔮` acting\n    through the injective substitution/;
s/Multiplication by `d` is injective on `\(1−e\)B⁺_T`, since `d`\n  has no zeros there, so the second summand is free of rank `1`\./Multiplication by `d` is injective on `(1−e)B⁺_T`, since `d`\n  has no zeros there, so the second summand is isomorphic to `(1−e)B⁺_T`, which is\n  projective (a direct summand of `B⁺_T`)./;
s/\(lane proof; re-review requested\)\./(lane proof; re-review PASS by `gq-referee-a`, proof gaps, 035fee55a; re-review by\n`gq-referee-b` pending)./;
print;
