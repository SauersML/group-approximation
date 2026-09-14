Read("bal.g");;
Read("open16_targets.g");;
Print("targets ", Length(TARGETS), "\n");;
for t in TARGETS do Print(t[1], " order=", Size(t[2]), " simple=", IsSimpleGroup(t[2]), "\n"); od;;
QUIT;
