import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_32
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_23
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s132Trace1 :
    rotationWord (word (rotationSignedWord "xzYXYXzYXYXyxyZyxyZxxyZXy")) =
      rotationWord (word (rotationSignedWord "ZXyzxZxxyZx")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "xzYXYXzYXYXyxyZyZXyxyxyZx")) :=
      rotationConsequenceStep "xzYXYXzYXYXyxyZyxyZxxyZXy" "xzYXYXzYXYXyxyZyZXyxyxyZx" "xzYXYXzYXYXyxyZyZXyxyxyZx"
        "YxzYXXzYXZXyxyxyZx" true (hrelation := o12_32Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "xzYXYXzYXZXyyxyZyxyZx")) :=
      rotationConsequenceStep "xzYXYXzYXYXyxyZyZXyxyxyZx" "xzYXYXzYXZXyyxyZyxyZx" "xzYXYXzYXZXyyxyZX"
        "YxzYzYXYxyZXyyxyZX" true (hrelation := o12_13Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "xzYXYXzYXZXYxyZyxyZx")) :=
      rotationStep "xzYXYXzYXZXyyxyZyxyZx" "xzYXYXzYXZXYxyZyxyZx" "xzYXYXzYXZX" 1 false
    _ = rotationWord (word (rotationSignedWord "xzYXYXZYXZXYxyZyxyZx")) :=
      rotationStep "xzYXYXzYXZXYxyZyxyZx" "xzYXYXZYXZXYxyZyxyZx" "xzYXYX" 2 false
    _ = rotationWord (word (rotationSignedWord "xzYXYXZYXZxxYxyZyxyZx")) :=
      rotationStep "xzYXYXZYXZXYxyZyxyZx" "xzYXYXZYXZxxYxyZyxyZx" "xzYXYXZYXZ" 0 true
    _ = rotationWord (word (rotationSignedWord "xzYXYXZXzxyxYxyZyxyZx")) :=
      rotationStep "xzYXYXZYXZxxYxyZyxyZx" "xzYXYXZXzxyxYxyZyxyZx" "xzYXYXZ" 5 true
    _ = rotationWord (word (rotationSignedWord "xzYXYXZXZxyxYxyZyxyZx")) :=
      rotationStep "xzYXYXZXzxyxYxyZyxyZx" "xzYXYXZXZxyxYxyZyxyZx" "xzYXYXZX" 2 false
    _ = rotationWord (word (rotationSignedWord "xzYXYzxxyxYxyZyxyZx")) :=
      rotationStep "xzYXYXZXZxyxYxyZyxyZx" "xzYXYzxxyxYxyZyxyZx" "xzYXYX" 3 true
    _ = rotationWord (word (rotationSignedWord "xzYXYzXyxYxyZyxyZx")) :=
      rotationStep "xzYXYzxxyxYxyZyxyZx" "xzYXYzXyxYxyZyxyZx" "xzYXYz" 0 false
    _ = rotationWord (word (rotationSignedWord "xzYXYZXyxYxyZyxyZx")) :=
      rotationStep "xzYXYzXyxYxyZyxyZx" "xzYXYZXyxYxyZyxyZx" "xzYXY" 2 false
    _ = rotationWord (word (rotationSignedWord "xzYXyyZXyxYxyZyxyZx")) :=
      rotationStep "xzYXYZXyxYxyZyxyZx" "xzYXyyZXyxYxyZyxyZx" "xzYX" 1 true
    _ = rotationWord (word (rotationSignedWord "xzxzyZXyxZXZyxyZx")) :=
      rotationConsequenceStep "xzYXyyZXyxYxyZyxyZx" "xzxzyZXyxZXZyxyZx" "xzxzyZXyxZXYXy"
        "YxyxzXYxzYZXYXyyZXyx" false (hrelation := o21_23Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "ZXyZXyxZXZyxyZx")) :=
      rotationStep "xzxzyZXyxZXZyxyZx" "ZXyZXyxZXZyxyZx" "" 3 false
    _ = rotationWord (word (rotationSignedWord "ZXyZXyxxzxyxyZx")) :=
      rotationStep "ZXyZXyxZXZyxyZx" "ZXyZXyxxzxyxyZx" "ZXyZXyx" 3 true
    _ = rotationWord (word (rotationSignedWord "ZXyZXyXzxyxyZx")) :=
      rotationStep "ZXyZXyxxzxyxyZx" "ZXyZXyXzxyxyZx" "ZXyZXy" 0 false
    _ = rotationWord (word (rotationSignedWord "ZXyZXXZxxyZx")) :=
      rotationStep "ZXyZXyXzxyxyZx" "ZXyZXXZxxyZx" "ZXyZXy" 5 false
    _ = rotationWord (word (rotationSignedWord "ZXyZxZxxyZx")) :=
      rotationStep "ZXyZXXZxxyZx" "ZXyZxZxxyZx" "ZXyZ" 0 true
    _ = rotationWord (word (rotationSignedWord "ZXyzxZxxyZx")) :=
      rotationStep "ZXyZxZxxyZx" "ZXyzxZxxyZx" "ZXy" 2 true

end

end GroupApproximation.LiteralBaseP13RotationReplay
