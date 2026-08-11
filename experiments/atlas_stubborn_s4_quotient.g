# Exact quotient test for the four stubborn perfect-overlap relators.
#
# The five words below lie in the free product S4 * S4.  The first four are
# certified-zero atlas boundary words (indices 70, 90, 91, and 86), while
# `phase` is the survivor at index 11.  This script asks GAP to simplify the
# quotient by the four zero words and retain the image of the phase word.

F := FreeGroup("s1", "t1", "s2", "t2");;
s1 := F.1;; t1 := F.2;; s2 := F.3;; t2 := F.4;;

s4Relations := [
  s1^2, t1^3, (s1*t1)^4,
  s2^2, t2^3, (s2*t2)^4
];;

w70 := s2*t1^2*s1*t1*s1*s2*s1*s2*t1^2*s1*t1;;
w90 := t2^2*s2*t2*s1*t1^2*s1*t1*s1*s2*t2^2*s2*t2*s2
       *s1*t1^2*s1*t1*s1*t2^2*s2*t2*s2*s1*t1^2*s1*t1*s1;;
w91 := t2^2*s2*t2*s2*s1*t1^2*s1*t1*s1*t2^2*s2*t2*s2
       *s1*t1^2*s1*t1*s1*t2^2*s2*t2*s2*s1*t1^2*s1*t1*s1;;
w86 := s1*s2*s1*t1^2*s1*t1*s2*s1*t1^2*s1*t1
       *s2*s1*t1^2*s1*t1*s1;;

phase := t2*s2*t2^2*s2*t2*t1*s1*t1^2*s1*t1*s2*t1*s1*t1^2*s1*t1
         *t2*s2*t2^2*s2*t2*t1*s1*t1^2*s1*t1*s2*t1^2*s1;;

G := F / Concatenation(s4Relations, [w70, w90, w91, w86]);;
iso := IsomorphismSimplifiedFpGroup(G);;
H := Image(iso);;
phaseInG := MappedWord(phase, GeneratorsOfGroup(F), GeneratorsOfGroup(G));;
phaseImage := Image(iso, phaseInG);;

Print("original_generators ", Length(GeneratorsOfGroup(G)), "\n");
Print("simplified_generators ", Length(GeneratorsOfGroup(H)), "\n");
Print("simplified_relators ", RelatorsOfFpGroup(H), "\n");
Print("phase_image ", phaseImage, "\n");

# An epimorphism onto a finite group under which `phaseInG` is nonidentity is
# a checkable certificate that the four displayed zero relators alone do not
# normally generate the phase word.
targets := [
  ["S3", SymmetricGroup(3)],
  ["D8", DihedralGroup(IsPermGroup, 8)],
  ["A4", AlternatingGroup(4)],
  ["S4", SymmetricGroup(4)],
  ["A5", AlternatingGroup(5)],
  ["S5", SymmetricGroup(5)],
  ["PSL(2,7)", PSL(2, 7)]
];;
for named in targets do
  quotients := GQuotients(G, named[2]);
  survivors := Filtered(quotients,
    hom -> Image(hom, phaseInG) <> One(named[2]));
  Print("target ", named[1], " quotients ", Length(quotients),
        " phase_survivors ", Length(survivors), "\n");
  if Length(survivors) > 0 then
    certificate := survivors[1];
    certificateImages := [];
    for generator in GeneratorsOfGroup(G) do
      Add(certificateImages, Image(certificate, generator));
    od;
    Print("certificate_images ", certificateImages, "\n");
    Print("certificate_phase ", Image(certificate, phaseInG), "\n");
    break;
  fi;
od;
