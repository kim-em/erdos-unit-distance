import Mathlib

/- Target: Rankin-style ideal count. Prove the theorem below (replace sorry),
keeping the statement EXACTLY as given. You may add helper lemmas above it. -/

namespace Erdos

open NumberField

private theorem finite_ideal_absNorm_le_real (F : Type) [Field F] [NumberField F] (X : ℝ) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite := by
  refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 F) ⌊X⌋₊).subset ?_
  intro I hI
  exact Nat.le_floor hI.2

private theorem card_ideal_absNorm_le_bound (F : Type) [Field F] [NumberField F]
    {X : ℝ} (hX : 1 ≤ X) :
    (({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ)) ≤
      X ^ 2 * 2 ^ Module.finrank ℚ F := by
  sorry

theorem card_ideal_absNorm_le (F : Type) [Field F] [NumberField F]
    {X : ℝ} (hX : 1 ≤ X) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite ∧
      (({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ)) ≤
        X ^ 2 * 2 ^ Module.finrank ℚ F := by
  exact ⟨finite_ideal_absNorm_le_real F X, card_ideal_absNorm_le_bound F hX⟩

end Erdos
