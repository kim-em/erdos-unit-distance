import Mathlib

/- Target: Rankin-style ideal count. Prove the theorem below (replace sorry),
keeping the statement EXACTLY as given. You may add helper lemmas above it. -/

namespace Erdos

open NumberField

theorem card_ideal_absNorm_le (F : Type) [Field F] [NumberField F]
    {X : ℝ} (hX : 1 ≤ X) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite ∧
      (({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ)) ≤
        X ^ 2 * 2 ^ Module.finrank ℚ F := by
  sorry

end Erdos
