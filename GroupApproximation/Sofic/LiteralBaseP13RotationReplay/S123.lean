import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S123Trace4

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s123Image_eq_one :
    rotationWord (word (rotationSignedWord "YxzYXXYxzYxyZXyyZXyxyxyZX")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := s123Trace4
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay
