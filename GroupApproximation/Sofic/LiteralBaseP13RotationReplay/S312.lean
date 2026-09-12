import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S312Trace4

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s312Image_eq_one :
    rotationWord (word (rotationSignedWord "xYxzYxYxzYXXyZXyyZXyxyxyZx")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := s312Trace4
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay
