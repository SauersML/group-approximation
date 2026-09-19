import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O13_23
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_23
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s213Trace1 :
    rotationWord (word (rotationSignedWord "YxyxzxzYXYZXYXyyxyZXyZXyx")) =
      rotationWord (word (rotationSignedWord "YxyXZyXZxyxzYXy")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxyZXYXYZXYXyyxyZXyZXyx")) :=
      rotationStep "YxyxzxzYXYZXYXyyxyZXyZXyx" "YxyZXYXYZXYXyyxyZXyZXyx" "Yxy" 3 false
    _ = rotationWord (word (rotationSignedWord "YxyZXYXYZXYXyyZXyxyxyZX")) :=
      rotationConsequenceStep "YxyZXYXYZXYXyyxyZXyZXyx" "YxyZXYXYZXYXyyZXyxyxyZX" "YxyZXYXYZXYXyyZXyxyxyZX"
        "xzYXYXYxzxyZXyZXyx" false (hrelation := o13_23Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "YxyZXYXZXyxZXYXyyxyZX")) :=
      rotationConsequenceStep "YxyZXYXYZXYXyyZXyxyxyZX" "YxyZXYXZXyxZXYXyyxyZX" "YxyZXYXZXyxZXYXy"
        "YxyxzXYxzYZXYXyyZXyx" false (hrelation := o21_23Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "YxyZXYXZXyxZXYXYxyZX")) :=
      rotationStep "YxyZXYXZXyxZXYXyyxyZX" "YxyZXYXZXyxZXYXYxyZX" "YxyZXYXZXyxZXYX" 1 false
    _ = rotationWord (word (rotationSignedWord "YxyZxxYXZXyxZXYXYxyZX")) :=
      rotationStep "YxyZXYXZXyxZXYXYxyZX" "YxyZxxYXZXyxZXYXYxyZX" "YxyZ" 0 true
    _ = rotationWord (word (rotationSignedWord "YxyZxzxyXXyxZXYXYxyZX")) :=
      rotationStep "YxyZxxYXZXyxZXYXYxyZX" "YxyZxzxyXXyxZXYXYxyZX" "YxyZxx" 5 true
    _ = rotationWord (word (rotationSignedWord "YxyZxzxyxyxZXYXYxyZX")) :=
      rotationStep "YxyZxzxyXXyxZXYXYxyZX" "YxyZxzxyxyxZXYXYxyZX" "YxyZxzxy" 0 true
    _ = rotationWord (word (rotationSignedWord "YxyzxzxyxyxZXYXYxyZX")) :=
      rotationStep "YxyZxzxyxyxZXYXYxyZX" "YxyzxzxyxyxZXYXYxyZX" "Yxy" 2 true
    _ = rotationWord (word (rotationSignedWord "YxyXZyxyxZXYXYxyZX")) :=
      rotationStep "YxyzxzxyxyxZXYXYxyZX" "YxyXZyxyxZXYXYxyZX" "Yxyz" 3 false
    _ = rotationWord (word (rotationSignedWord "YxyXZyxyXXZXYXYxyZX")) :=
      rotationStep "YxyXZyxyxZXYXYxyZX" "YxyXZyxyXXZXYXYxyZX" "YxyXZyxy" 0 false
    _ = rotationWord (word (rotationSignedWord "YxyXZyxyXzxzYXYxyZX")) :=
      rotationStep "YxyXZyxyXXZXYXYxyZX" "YxyXZyxyXzxzYXYxyZX" "YxyXZyxyXX" 3 true
    _ = rotationWord (word (rotationSignedWord "YxyXZyZxYzYXYxyZX")) :=
      rotationStep "YxyXZyxyXzxzYXYxyZX" "YxyXZyZxYzYXYxyZX" "YxyXZyxy" 5 false
    _ = rotationWord (word (rotationSignedWord "YxyXZyZxZXyxzYXYY")) :=
      rotationConsequenceStep "YxyXZyZxYzYXYxyZX" "YxyXZyZxZXyxzYXYY" "YxyXZyZxZXy"
        "YxzYzYXYxyZXyyxyZX" false (hrelation := o12_13Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "YxyXZyZxZXyxzYXy")) :=
      rotationStep "YxyXZyZxZXyxzYXYY" "YxyXZyZxZXyxzYXy" "YxyXZyZxZXyxzYX" 1 true
    _ = rotationWord (word (rotationSignedWord "YxyXZyzxZXyxzYXy")) :=
      rotationStep "YxyXZyZxZXyxzYXy" "YxyXZyzxZXyxzYXy" "YxyXZy" 2 true
    _ = rotationWord (word (rotationSignedWord "YxyXZyzxzXyxzYXy")) :=
      rotationStep "YxyXZyzxZXyxzYXy" "YxyXZyzxzXyxzYXy" "YxyXZyzx" 2 true
    _ = rotationWord (word (rotationSignedWord "YxyXZyXZXXyxzYXy")) :=
      rotationStep "YxyXZyzxzXyxzYXy" "YxyXZyXZXXyxzYXy" "YxyXZyz" 3 false
    _ = rotationWord (word (rotationSignedWord "YxyXZyXZxyxzYXy")) :=
      rotationStep "YxyXZyXZXXyxzYXy" "YxyXZyXZxyxzYXy" "YxyXZyXZ" 0 true

end

end GroupApproximation.LiteralBaseP13RotationReplay
