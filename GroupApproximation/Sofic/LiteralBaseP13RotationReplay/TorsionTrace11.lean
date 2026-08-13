import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace10
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_32

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace11 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "XYxZyxZXzyXYXzX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "XYxZyxzXYZXYZYxyxyxyzX")) := torsionTrace10
    _ = rotationWord (word (rotationSignedWord "XYxZyxzXYZXYZYYXYXYXzX")) :=
      rotationStep "XYxZyxzXYZXYZYxyxyxyzX" "XYxZyxzXYZXYZYYXYXYXzX" "XYxZyxzXYZXYZY" 7 false
    _ = rotationWord (word (rotationSignedWord "XYxZyxzXYZXYZyXYXYXzX")) :=
      rotationStep "XYxZyxzXYZXYZYYXYXYXzX" "XYxZyxzXYZXYZyXYXYXzX" "XYxZyxzXYZXYZ" 1 true
    _ = rotationWord (word (rotationSignedWord "XYxZyxzXYZYzXYXzX")) :=
      rotationStep "XYxZyxzXYZXYZyXYXYXzX" "XYxZyxzXYZYzXYXzX" "XYxZyxzXYZ" 6 true
    _ = rotationWord (word (rotationSignedWord "XYxZyxzXYZYZXYXzX")) :=
      rotationStep "XYxZyxzXYZYzXYXzX" "XYxZyxzXYZYZXYXzX" "XYxZyxzXYZY" 2 false
    _ = rotationWord (word (rotationSignedWord "XYxZyxzXzyXYXzX")) :=
      rotationStep "XYxZyxzXYZYZXYXzX" "XYxZyxzXzyXYXzX" "XYxZyxzXY" 4 true
    _ = rotationWord (word (rotationSignedWord "XYxZyxZXzyXYXzX")) :=
      rotationStep "XYxZyxzXzyXYXzX" "XYxZyxZXzyXYXzX" "XYxZyx" 2 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
