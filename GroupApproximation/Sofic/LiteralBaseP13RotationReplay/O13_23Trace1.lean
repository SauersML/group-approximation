import GroupApproximation.Sofic.LiteralBaseP13RotationReplay

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o13_23Trace1 :
    rotationWord (word (rotationSignedWord "xzYXYXYxzxyZXyZXyx")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "xzYXYXYXXzxyZXyZXyx")) :=
      rotationStep "xzYXYXYxzxyZXyZXyx" "xzYXYXYXXzxyZXyZXyx" "xzYXYXY" 0 false
    _ = rotationWord (word (rotationSignedWord "xzYXYXYXYXZxZXyZXyx")) :=
      rotationStep "xzYXYXYXXzxyZXyZXyx" "xzYXYXYXYXZxZXyZXyx" "xzYXYXYX" 5 false
    _ = rotationWord (word (rotationSignedWord "xzxyxyZxZXyZXyx")) :=
      rotationStep "xzYXYXYXYXZxZXyZXyx" "xzxyxyZxZXyZXyx" "xz" 7 true
    _ = rotationWord (word (rotationSignedWord "xzxyxyzxZXyZXyx")) :=
      rotationStep "xzxyxyZxZXyZXyx" "xzxyxyzxZXyZXyx" "xzxyxy" 2 true
    _ = rotationWord (word (rotationSignedWord "xzxyxyzxzXyZXyx")) :=
      rotationStep "xzxyxyzxZXyZXyx" "xzxyxyzxzXyZXyx" "xzxyxyzx" 2 true
    _ = rotationWord (word (rotationSignedWord "xzxyxyXZXXyZXyx")) :=
      rotationStep "xzxyxyzxzXyZXyx" "xzxyxyXZXXyZXyx" "xzxyxyz" 3 false
    _ = rotationWord (word (rotationSignedWord "xzxyxyXZxyZXyx")) :=
      rotationStep "xzxyxyXZXXyZXyx" "xzxyxyXZxyZXyx" "xzxyxyXZ" 0 true
    _ = rotationWord (word (rotationSignedWord "xzxyxyXzxyZXyx")) :=
      rotationStep "xzxyxyXZxyZXyx" "xzxyxyXzxyZXyx" "xzxyxyX" 2 true
    _ = rotationWord (word (rotationSignedWord "xzxyZxZXyx")) :=
      rotationStep "xzxyxyXzxyZXyx" "xzxyZxZXyx" "xzxyxy" 5 false
    _ = rotationWord (word (rotationSignedWord "xzxyzxZXyx")) :=
      rotationStep "xzxyZxZXyx" "xzxyzxZXyx" "xzxy" 2 true
    _ = rotationWord (word (rotationSignedWord "xzxyzxzXyx")) :=
      rotationStep "xzxyzxZXyx" "xzxyzxzXyx" "xzxyzx" 2 true
    _ = rotationWord (word (rotationSignedWord "xzxyXZXXyx")) :=
      rotationStep "xzxyzxzXyx" "xzxyXZXXyx" "xzxyz" 3 false
    _ = rotationWord (word (rotationSignedWord "xzxyXZxyx")) :=
      rotationStep "xzxyXZXXyx" "xzxyXZxyx" "xzxyXZ" 0 true
    _ = rotationWord (word (rotationSignedWord "xzxyXzxyx")) :=
      rotationStep "xzxyXZxyx" "xzxyXzxyx" "xzxyX" 2 true
    _ = rotationWord (word (rotationSignedWord "xxx")) :=
      rotationStep "xzxyXzxyx" "xxx" "xzxy" 5 false
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "xxx" "" "" 0 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
