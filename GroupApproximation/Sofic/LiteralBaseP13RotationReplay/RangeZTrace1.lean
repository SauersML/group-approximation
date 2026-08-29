import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_31

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem rangeZTrace1 :
    rotationWord (word (rotationSignedWord "YxzYXZXYXyXyZXyXYxzYzYXYXyZXyXXyZXyzYXYZ")) =
      rotationWord (word (rotationSignedWord "YxzYxyZXyzYXyZXyxyZXyzyyXYZ")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYXXyZXyXZXYzYzYXYXyZXyXXyZXyzYXYZ")) :=
      rotationConsequenceStep "YxzYXZXYXyXyZXyXYxzYzYXYXyZXyXXyZXyzYXYZ" "YxzYXXyZXyXZXYzYzYXYXyZXyXXyZXyzYXYZ" "YxzYXXyZXyXZXYXy"
        "YxyxzxYxzYxZXYXyXyZXyX" false (hrelation := o21_31Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyXZXYzYzYXYXyZXyXXyZXyzYXYZ")) :=
      rotationStep "YxzYXXyZXyXZXYzYzYXYXyZXyXXyZXyzYXYZ" "YxzYxyZXyXZXYzYzYXYXyZXyXXyZXyzYXYZ" "YxzY" 0 true
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyXZXYzYzYXYXyZXyxyZXyzYXYZ")) :=
      rotationStep "YxzYxyZXyXZXYzYzYXYXyZXyXXyZXyzYXYZ" "YxzYxyZXyXZXYzYzYXYXyZXyxyZXyzYXYZ" "YxzYxyZXyXZXYzYzYXYXyZXy" 0 true
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyXZXYZYzYXYXyZXyxyZXyzYXYZ")) :=
      rotationStep "YxzYxyZXyXZXYzYzYXYXyZXyxyZXyzYXYZ" "YxzYxyZXyXZXYZYzYXYXyZXyxyZXyzYXYZ" "YxzYxyZXyXZXY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyXZXYZYZYXYXyZXyxyZXyzYXYZ")) :=
      rotationStep "YxzYxyZXyXZXYZYzYXYXyZXyxyZXyzYXYZ" "YxzYxyZXyXZXYZYZYXYXyZXyxyZXyzYXYZ" "YxzYxyZXyXZXYZY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyXZXzXYXyZXyxyZXyzYXYZ")) :=
      rotationStep "YxzYxyZXyXZXYZYZYXYXyZXyxyZXyzYXYZ" "YxzYxyZXyXZXzXYXyZXyxyZXyzYXYZ" "YxzYxyZXyXZXY" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyXZXZXYXyZXyxyZXyzYXYZ")) :=
      rotationStep "YxzYxyZXyXZXzXYXyZXyxyZXyzYXYZ" "YxzYxyZXyXZXZXYXyZXyxyZXyzYXYZ" "YxzYxyZXyXZX" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyzYXyZXyxyZXyzYXYZ")) :=
      rotationStep "YxzYxyZXyXZXZXYXyZXyxyZXyzYXYZ" "YxzYxyZXyzYXyZXyxyZXyzYXYZ" "YxzYxyZXyX" 3 true
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyzYXyZXyxyZXyzyyXYZ")) :=
      rotationStep "YxzYxyZXyzYXyZXyxyZXyzYXYZ" "YxzYxyZXyzYXyZXyxyZXyzyyXYZ" "YxzYxyZXyzYXyZXyxyZXyz" 1 true

end

end GroupApproximation.LiteralBaseP13RotationReplay
