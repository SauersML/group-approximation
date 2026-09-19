undef $/; $_ = <STDIN>;
s/  - In general `V_\(k\+1\) ∈ Q·V_0` has a denominator growing like `\(k\+1\)!`\. So `V_0` is\n    divisible by every `n`\./  - In general the recursion puts every `V_k` in `Q·V_0`. That every `n` occurs among the\n    denominators, so that `V_0` is divisible by every `n`, is checked here only for\n    `k <= 3` in this variant; it is part of item 3./;
s/  finitely presented positivity relation\./  finitely presented positivity relation. There every `n` does occur as a denominator.\n  So a fallback is a variant without `a_u` in which positivity is achieved differently./;
print;
