import Mathlib

/-!
# Sard's theorem when the source has smaller dimension

The image of a `C¹` map `f : E → F` with `dim E < dim F` is null for any Haar measure on `F`:
it has Hausdorff dimension at most `dim E`, and a set of Hausdorff dimension below `dim F` is
null for the Hausdorff measure of dimension `dim F`, itself a Haar measure on `F`.

Split off from `Part2/Ch14.lean`, which restates it as `Chapter14.sard_of_finrank_lt`, so that
files needing only this regime do not import the vendored `SardMoreira` development behind the
high-dimensional regime of Sard's theorem.
-/

open MeasureTheory Module Set
open scoped NNReal

namespace MorseFloer

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Sard's theorem, low-dimensional regime.** The image of any set by a `C¹` map to a space
of larger dimension is null. -/
theorem measure_image_eq_zero_of_finrank_lt (μ : Measure F) [μ.IsAddHaarMeasure]
    {f : E → F} (hf : ContDiff ℝ 1 f) (s : Set E) (hEF : finrank ℝ E < finrank ℝ F) :
    μ (f '' s) = 0 := by
  have hlt : dimH (f '' s) < (finrank ℝ F : ℝ≥0) := by
    refine lt_of_le_of_lt ((dimH_mono (image_subset_range f s)).trans (hf.differentiable one_ne_zero).dimH_range_le) ?_
    exact_mod_cast hEF
  refine measure_zero_of_dimH_lt (d := (finrank ℝ F : ℝ≥0)) ?_ hlt
  exact Measure.absolutelyContinuous_isAddHaarMeasure μ (μH[(finrank ℝ F : ℝ)])

end MorseFloer
