import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S123

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s231Trace1 :
    rotationWord (word (rotationSignedWord "XYxzYxYxzYxyZXyyZXyXZXYXy")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "XYxzYxxxyZXyxzYXYXXZXYXy")) :=
      rotationConsequenceStep "XYxzYxYxzYxyZXyyZXyXZXYXy" "XYxzYxxxyZXyxzYXYXXZXYXy" "XYxzYxxxyZXy"
        "YxzYXXYxzYxyZXyyZXyxyxyZX" false (hrelation := s123Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "zYXYXXZXYXy")) :=
      rotationStep "XYxzYxxxyZXyxzYXYXXZXYXy" "zYXYXXZXYXy" "XYxzY" 0 false
    _ = rotationWord (word (rotationSignedWord "zYXYxZXYXy")) :=
      rotationStep "zYXYXXZXYXy" "zYXYxZXYXy" "zYXY" 0 true
    _ = rotationWord (word (rotationSignedWord "zYXYxzXYXy")) :=
      rotationStep "zYXYxZXYXy" "zYXYxzXYXy" "zYXYx" 2 true
    _ = rotationWord (word (rotationSignedWord "zYXYxzxxYXy")) :=
      rotationStep "zYXYxzXYXy" "zYXYxzxxYXy" "zYXYxz" 0 true
    _ = rotationWord (word (rotationSignedWord "zYXYZXZxYXy")) :=
      rotationStep "zYXYxzxxYXy" "zYXYZXZxYXy" "zYXY" 3 false
    _ = rotationWord (word (rotationSignedWord "zYXYZyXzy")) :=
      rotationStep "zYXYZXZxYXy" "zYXYZyXzy" "zYXYZy" 5 true
    _ = rotationWord (word (rotationSignedWord "zYYzyzy")) :=
      rotationStep "zYXYZyXzy" "zYYzyzy" "zY" 6 true
    _ = rotationWord (word (rotationSignedWord "zYYYZ")) :=
      rotationStep "zYYzyzy" "zYYYZ" "zYYz" 4 false
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "zYYYZ" "" "z" 1 true

end

end GroupApproximation.LiteralBaseP13RotationReplay
