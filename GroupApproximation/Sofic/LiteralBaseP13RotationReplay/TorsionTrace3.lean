import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace2

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace3 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxyxyZXYxzYXZXYzYX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxyxyZXYxzYXZXYzYXYxzYXZXYzYX")) := torsionTrace2
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxyxyZXYxzYzxzYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzyxzYXyxyxyZXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzyxzYXyxyxyZXYxzYzxzYzYXYxzYXZXYzYX" "YxzYzyxzYXyxyxyZXYxzYX" 3 true
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxyxzYzYXYxzYXZXYzYX")) :=
      rotationConsequenceStep "YxzYzyxzYXyxyxyZXYxzYzxzYzYXYxzYXZXYzYX" "YxzYzyxzYXyxYxzYXyxyxzYzYXYxzYXZXYzYX" "YxzYzyxzYXyxYxzYXyxyZyZXy"
        "YxzYzYXYxyZXyyxyZX" false (hrelation := o12_13Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxyxZYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzyxzYXyxYxzYXyxyxzYzYXYxzYXZXYzYX" "YxzYzyxzYXyxYxzYXyxyxZYzYXYxzYXZXYzYX" "YxzYzyxzYXyxYxzYXyxyx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxyxZYZYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzyxzYXyxYxzYXyxyxZYzYXYxzYXZXYzYX" "YxzYzyxzYXyxYxzYXyxyxZYZYXYxzYXZXYzYX" "YxzYzyxzYXyxYxzYXyxyxZY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxyxyzXYxzYXZXYzYX")) :=
      rotationStep "YxzYzyxzYXyxYxzYXyxyxZYZYXYxzYXZXYzYX" "YxzYzyxzYXyxYxzYXyxyxyzXYxzYXZXYzYX" "YxzYzyxzYXyxYxzYXyxyx" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxyxyZXYxzYXZXYzYX")) :=
      rotationStep "YxzYzyxzYXyxYxzYXyxyxyzXYxzYXZXYzYX" "YxzYzyxzYXyxYxzYXyxyxyZXYxzYXZXYzYX" "YxzYzyxzYXyxYxzYXyxyxy" 2 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
