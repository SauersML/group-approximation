local $/; my $t = <STDIN>;
$t =~ s/The F_∞ half for all hyperbolic groups is exactly BBMZ `quest:F_infty` for this\n   host\. It is not available from print\.\*\*/For this host, the F_∞ half for all hyperbolic groups reduces to BBMZ\n   `quest:F_infty`: F_∞ of the RSG family suffices, and F_∞ of `Γ` is necessary. It is not available from print.**/ or die "nomatch";
print $t;
