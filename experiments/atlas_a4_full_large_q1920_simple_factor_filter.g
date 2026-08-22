# Exact order filter forced by normal generation of a full Q1920 carrier.
# The source simple factor contains Q1920 or Q1920/Z, as well as the injected
# S3 x S3 vertex, so its order is divisible by lcm(960,36)=2880.

targets:=Filtered(
  AllSmallNonabelianSimpleGroups([1..999999]),
  group->Size(group) mod 2880=0
);;

Print("target_count=",Length(targets),"\n");
Print("targets=",List(targets,
  group->[StructureDescription(group),Size(group)]),"\n");
QUIT;
