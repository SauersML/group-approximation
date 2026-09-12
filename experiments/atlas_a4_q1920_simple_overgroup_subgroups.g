# Exact conjugacy-class census of the two possible simple-factor Q images.
# Set TARGET_INDEX before Read().  Targets are the complete nonabelian simple
# groups below 10^7 whose order is divisible by 2880.

if not IsBound(TARGET_INDEX) then Error("set TARGET_INDEX in [1..15]"); fi;
targets:=[
  ["A8",function() return AlternatingGroup(8); end],
  ["PSL(3,4)",function() return PSL(3,4); end],
  ["O(5,3)",function() return PSp(4,3); end],
  ["M12",function() return MathieuGroup(12); end],
  ["A9",function() return AlternatingGroup(9); end],
  ["PSL(2,64)",function() return PSL(2,64); end],
  ["M22",function() return MathieuGroup(22); end],
  ["HJ",function() return First(AllSmallNonabelianSimpleGroups([604800])); end],
  ["O(5,4)",function() return PSp(4,4); end],
  ["O(7,2)",function() return Sp(6,2); end],
  ["A10",function() return AlternatingGroup(10); end],
  ["PSU(4,3)",function() return PSU(4,3); end],
  ["O(5,5)",function() return PSp(4,5); end],
  ["PSL(4,3)",function() return PSL(4,3); end],
  ["PSL(5,2)",function() return PSL(5,2); end]
];;

entry:=targets[TARGET_INDEX];;
name:=entry[1];;
ambient:=Image(IsomorphismPermGroup(entry[2]()));;
q960:=PerfectGroup(960,1);;
q1920:=PerfectGroup(1920,1);;
images960:=IsomorphicSubgroups(ambient,q960);;
images1920:=IsomorphicSubgroups(ambient,q1920);;

Print("target_index=",TARGET_INDEX,
      " target=",name,
      " order=",Size(ambient),
      " q960_classes=",Length(images960),
      " q1920_classes=",Length(images1920),"\n");
QUIT;
