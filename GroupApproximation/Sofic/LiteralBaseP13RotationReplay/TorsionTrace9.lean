import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace8
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_32

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace9 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "XYxZyxzyxYYZxYxzYXyxyxyzX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "XYxZyXZXzYXyxYxzYXyxyxyzX")) := torsionTrace8
    _ = rotationWord (word (rotationSignedWord "XYxZyXZXZYXyxYxzYXyxyxyzX")) :=
      rotationStep "XYxZyXZXzYXyxYxzYXyxyxyzX" "XYxZyXZXZYXyxYxzYXyxyxyzX" "XYxZyXZX" 2 false
    _ = rotationWord (word (rotationSignedWord "XYxZyzxYXyxYxzYXyxyxyzX")) :=
      rotationStep "XYxZyXZXZYXyxYxzYXyxyxyzX" "XYxZyzxYXyxYxzYXyxyxyzX" "XYxZyX" 3 true
    _ = rotationWord (word (rotationSignedWord "XYxZyZxYXyxYxzYXyxyxyzX")) :=
      rotationStep "XYxZyzxYXyxYxzYXyxyxyzX" "XYxZyZxYXyxYxzYXyxyxyzX" "XYxZy" 2 false
    _ = rotationWord (word (rotationSignedWord "XYxZyxyXzyxYxzYXyxyxyzX")) :=
      rotationStep "XYxZyZxYXyxYxzYXyxyxyzX" "XYxZyxyXzyxYxzYXyxyxyzX" "XYxZyxy" 5 true
    _ = rotationWord (word (rotationSignedWord "XYxZyxyXYZYZxYxzYXyxyxyzX")) :=
      rotationStep "XYxZyxyXzyxYxzYXyxyxyzX" "XYxZyxyXYZYZxYxzYXyxyxyzX" "XYxZyxyXY" 4 false
    _ = rotationWord (word (rotationSignedWord "XYxZyxzyxYYZxYxzYXyxyxyzX")) :=
      rotationStep "XYxZyxyXYZYZxYxzYXyxyxyzX" "XYxZyxzyxYYZxYxzYXyxyxyzX" "XYxZyxy" 6 true

end

end GroupApproximation.LiteralBaseP13RotationReplay
