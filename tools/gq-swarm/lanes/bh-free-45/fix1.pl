my $f = shift; local $/; open my $h, '<', $f or die; my $t = <$h>; close $h; my $n = 0;
if ($f =~ /full-group-label-length/) {
  $n += $t =~ s/   `SV_Γ` whenever that group is finitely generated\.\n/   `SV_Γ` whenever that group is finitely generated.\n   For `K = SV_Γ` this is Belk–Zaremsky, arXiv:2001.04579, Theorem 1.2 (`thm:quasi-retracts`), proved there\n   by an explicit quasi-retraction `SV_Γ -> Γ`. The label-length proof below is different and also covers\n   intermediate `K`, but the `K = SV_Γ` case is theirs.\n/;
}
if ($f =~ /hyperbolic-groups-undistortedly/) {
  $n += $t =~ s/   group `SV_Γ` of `prop:contr_to_simple`\. Here `Γ` acts on the orbit `S` of a rational point\./   group `SV_Γ` of `prop:contr_to_simple`. Here `Γ` acts on the orbit `S` of a rational point. Item 2 is a\n   special case of Belk–Zaremsky, arXiv:2001.04579, Theorem 1.2 (every finitely generated `G` is\n   undistorted in a finitely generated `SV_G`); only item 1, through `G*Z <= Γ`, is new here./;
  $n += $t =~ s/be of type F_∞\. For `SV_Γ` this is tied to BBMZ Question `quest:F_infty` \(are full contracting RSGs of type F_∞\?\) and\nto the Belk–Zaremsky type F_n conjecture for twisted Brin–Thompson groups\./be of type F_∞. For this host it comes down to BBMZ Question `quest:F_infty` (are full contracting RSGs of type\nF_∞?). `Γ` acts oligomorphically on `S` (BBMZ `prop:HighlyTransitiveAction`), so Belk–Zaremsky's Theorem 1.4\n(arXiv:2001.04579, `thm:FinitenessTheorem`, a theorem, not a conjecture) makes `SV_Γ` of type F_∞ once `Γ` and the\nstabilizers in `Γ` of finite subsets of `S` are F_∞. Conversely, `SV_Γ` of type F_∞ forces `Γ` to be F_∞\n(quasi-retract, their Theorem 1.2, plus Alonso). Their conjecture is only the sharper characterization./;
}
if ($f =~ /embedding-proof/) {
  $n += $t =~ s/This is item 2 of the target for an arbitrary full contracting RSG\./This is item 2 of the target for an arbitrary full contracting RSG. For `K = SV_Γ` it is Belk–Zaremsky,\narXiv:2001.04579, Theorem 1.2, which gives a quasi-retraction; either proof suffices./;
}
if ($f =~ /quasi-isometrically-embed/) {
  $n += $t =~ s/For this host it is tied to two open questions: BBMZ Question\n   `quest:F_infty` \(is `Γ` of type F_∞\?\) and the Belk–Zaremsky type F_n criterion for `SV_G` at n ≥ 3, which\n   is a conjecture \(arXiv:2001.04579\)\. Any other undistorted host of type F_∞ would also do\./For this host it comes down to BBMZ Question `quest:F_infty` (is `Γ`\n   of type F_∞?): Belk–Zaremsky, arXiv:2001.04579, Theorem 1.4 (proved) makes `SV_Γ` of type F_∞ once `Γ` and its\n   finite-set stabilizers on `S` are F_∞, and their Theorem 1.2 with Alonso shows `Γ` must be F_∞. (Correction\n   09-18: an earlier version of this entry called their F_n criterion a conjecture; only the sharper\n   characterization is conjectural.) Any other undistorted host of type F_∞ would also do./;
}
open $h, '>', $f or die; print $h $t; close $h; print "$f: $n\n";
