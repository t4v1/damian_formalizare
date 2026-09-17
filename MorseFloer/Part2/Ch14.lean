import MorseFloer.Basic
import MorseFloer.Part2.SardMoreira.MainTheorem

/-!
# Chapter 14: A little differential geometry

Formalization of Chapter 14 of Audin–Damian, *Théorie de Morse et homologie de
Floer* — the appendix collecting the differential-geometric toolkit that Parts I
and II use throughout.

This chapter is where the project's Mathlib coverage is decided, so the file is
deliberately explicit about what exists and what does not.  Its sections:

* **§14.1** manifolds, submanifolds, the embedding theorem, tangent vectors,
  vector fields, differential forms, orientation.
* **§14.2** critical points, critical values, and Sard's theorem.
* **§14.3** transversality, the `Cᵏ` topology, and the transversality theorems.
* **§14.4** vector fields as differential equations: flows, the Lie derivative,
  linearisation along a solution.

## What Mathlib already provides

Charted spaces and `IsManifold`, the tangent bundle and `mfderiv`, immersions,
submersions and smooth embeddings (namespace `Manifold`), partitions of unity
and smooth bump coverings, the Whitney embedding of a compact manifold
(`SmoothBumpCovering.embeddingPiTangent`), integral curves with existence,
uniqueness and a completeness criterion (`Geometry/Manifold/IntegralCurve/`),
and the Lie bracket of vector fields (`mlieBracket`).  Where Mathlib has a
result, this file cites it rather than restating it.

## What is missing, and what that costs

* **Morse–Sard above the diagonal** (Theorem 14.2.1) is not in Mathlib.  The
  theorem splits on the two dimensions: below the diagonal the whole image is
  null, on the diagonal it is Mathlib's Jacobian lemma after transport, and
  above the diagonal it is the genuine Morse–Sard theorem, `sard_of_lt_finrank`,
  stated at the sharp smoothness threshold and derived from Moreira's theorem in
  `Part2/SardMoreira/` (Kudryashov's project, transplanted).  All three regimes
  are proved, so the chapter assumes nothing.

* **Submanifolds** have no Mathlib type, so Theorem 14.1.1 (the equivalence of
  the local-equations, local-parametrisation and local-model descriptions) and
  Proposition 14.3.5 (`f ⋔ P` implies `f⁻¹(P)` is a submanifold) are recorded in
  the blueprint without Lean statements.
* **The `Cᵏ` topology on `C^∞(M,N)`** does not exist, so the transversality
  theorems 14.3.10, 14.3.11 and 14.3.13, which are statements about dense open
  subsets of that space, are likewise blueprint-only.

## What is proved here

The linear algebra underlying transversality — that transverse subspaces
intersect in the expected dimension, so codimensions add — and the reconciliation
of the book's general definition of a critical point (the tangent map fails to
have maximal rank) with the definition used for real-valued functions
(the differential vanishes), which is the "fundamental example" of §14.2.a.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap Filter Topology

namespace MorseFloer
namespace Chapter14

/-! ## §14.2.a Critical points of a map between manifolds -/

section CriticalPoints

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A linear map has maximal rank** when it is injective or surjective
(§14.2.a).  In finite dimensions the rank of `L : E → F` is at most
`min (dim E) (dim F)`; equality holds exactly in the injective case when
`dim E ≤ dim F` and exactly in the surjective case when `dim E ≥ dim F`, and
each of those implies the other in the remaining direction.  So the disjunction
is precisely the book's condition "corank zero", with no case split. -/
def HasMaximalRank (L : E →L[ℝ] F) : Prop :=
  Function.Injective L ∨ Function.Surjective L

/-- **A critical point of a map** (§14.2.a): the tangent map fails to have
maximal rank. -/
def IsCriticalPointOfMap (L : E →L[ℝ] F) : Prop := ¬ HasMaximalRank L

/-- **The fundamental example** (§14.2.a).  For a real-valued function the
general definition collapses to the vanishing of the differential: on a
nontrivial space, a linear form has maximal rank exactly when it is nonzero.

This is what reconciles `IsCriticalPointOfMap` with `MorseFloer.IsCriticalPoint`
and with the local `IsCriticalPt` used throughout Part I. -/
theorem isCriticalPointOfMap_iff_eq_zero [Nontrivial E] (L : E →L[ℝ] ℝ) :
    IsCriticalPointOfMap L ↔ L = 0 := by
  constructor
  · intro h
    by_contra hne
    -- A nonzero linear form onto `ℝ` is surjective, hence of maximal rank.
    obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
      by_contra hall
      exact hne (by ext w; exact not_not.mp (not_exists.mp hall w))
    refine h (Or.inr fun r => ⟨(r / L v) • v, ?_⟩)
    rw [ContinuousLinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  · rintro rfl
    rintro (hinj | hsurj)
    · -- The zero form is not injective on a nontrivial space.
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      exact hv (hinj (by simp))
    · -- The zero form is not surjective onto `ℝ`.
      obtain ⟨v, hv⟩ := hsurj 1
      simp at hv

end CriticalPoints

/-! ## §14.2.b Sard's theorem -/

section Sard

open MeasureTheory Module Set
open scoped NNReal ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The set of critical points of a differentiable map (§14.2.a). -/
def criticalSet (f : E → F) : Set E := {x | IsCriticalPointOfMap (fderiv ℝ f x)}

/-- The set of critical values: the image of the critical set (§14.2.b).  Note
that a regular value need not be a value at all, and that a point outside the
critical set may still map to a critical value. -/
def criticalValues (f : E → F) : Set F := f '' criticalSet f

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- A critical point in the book's sense fails, in particular, to have surjective
differential.  This is the only consequence of criticality that Sard's proof uses,
and it is what makes the theorem below insensitive to which of the two clauses of
`HasMaximalRank` fails. -/
theorem not_surjective_of_mem_criticalSet {f : E → F} {x : E} (hx : x ∈ criticalSet f) :
    ¬ Function.Surjective (fderiv ℝ f x) :=
  fun hs => hx (Or.inr hs)

omit [MeasurableSpace F] [BorelSpace F] in
/-- For an endomorphism of a finite-dimensional space, a vanishing determinant is
exactly the failure of surjectivity.  This is the bridge between the book's
rank condition and the determinant condition that Mathlib's Jacobian theory uses. -/
theorem det_eq_zero_iff_not_surjective (A : F →L[ℝ] F) :
    A.det = 0 ↔ ¬ Function.Surjective A := by
  rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq,
    LinearMap.ker_eq_bot, LinearMap.injective_iff_surjective]
  rfl

/-- **Sard's theorem, low-dimensional regime.**  When the source has strictly
smaller dimension than the target, the image of *any* set is null — criticality
plays no role, because the whole image is already too thin.

Proved.  The image has Hausdorff dimension at most `dim E`, since a `C¹` map does
not raise Hausdorff dimension, and a set of Hausdorff dimension below `dim F` is
null for the Hausdorff measure of dimension `dim F`, which is itself a Haar
measure on `F`.  Nullity does not depend on which Haar measure is chosen, as any
two are mutually absolutely continuous. -/
theorem sard_of_finrank_lt (μ : Measure F) [μ.IsAddHaarMeasure]
    {f : E → F} (hf : ContDiff ℝ 1 f) (s : Set E) (hEF : finrank ℝ E < finrank ℝ F) :
    μ (f '' s) = 0 := by
  have hlt : dimH (f '' s) < (finrank ℝ F : ℝ≥0) := by
    refine lt_of_le_of_lt ((dimH_mono (image_subset_range f s)).trans hf.dimH_range_le) ?_
    exact_mod_cast hEF
  refine measure_zero_of_dimH_lt (d := (finrank ℝ F : ℝ≥0)) ?_ hlt
  exact Measure.absolutelyContinuous_isAddHaarMeasure μ (μH[(finrank ℝ F : ℝ)])

/-- **Sard's theorem, equidimensional regime.**  The critical values of a
differentiable map between spaces of equal dimension are null.

Proved, and with a weaker hypothesis than the book's: differentiability alone
suffices, no `C¹` and no continuity of the differential.  Mathlib supplies the
analytic content, for a self-map of a single space, as
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, itself
following Fremlin.  The work here is transport: a linear isomorphism `e : E ≃L F`
exists because the dimensions agree, and `f ∘ e.symm` is a self-map of `F` whose
differential fails to be surjective exactly where that of `f` does. -/
theorem sard_of_finrank_eq (μ : Measure F) [μ.IsAddHaarMeasure]
    {f : E → F} (hf : Differentiable ℝ f) {s : Set E}
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderiv ℝ f x))
    (hEF : finrank ℝ E = finrank ℝ F) :
    μ (f '' s) = 0 := by
  set e : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hEF with he
  set g : F → F := f ∘ e.symm with hg
  set g' : F → F →L[ℝ] F := fun y => (fderiv ℝ f (e.symm y)).comp
    (e.symm : F →L[ℝ] E) with hg'
  have himg : f '' s = g '' (e '' s) := by
    simp [hg, Set.image_image]
  rw [himg]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ (f' := g') ?_ ?_
  · intro y _
    exact HasFDerivAt.hasFDerivWithinAt
      ((hf (e.symm y)).hasFDerivAt.comp y (e.symm.hasFDerivAt))
  · rintro y ⟨x, hx, rfl⟩
    rw [det_eq_zero_iff_not_surjective]
    simp only [hg', ContinuousLinearEquiv.symm_apply_apply]
    intro hsurj
    rw [ContinuousLinearMap.coe_comp] at hsurj
    exact hcrit x hx hsurj.of_comp

omit [FiniteDimensional ℝ E] in
/-- **Sard's theorem, high-dimensional regime** — the genuine Morse–Sard theorem.

*Proved*, by transplanting Yury Kudryashov's `SardMoreira` project (the modules
under `Part2/SardMoreira/`, adapted to this project's Mathlib).  That project
proves Moreira's sharper statement: if `f` is `C^{k,α}` on `s` and its
differential has rank at most `p` there, then `f '' s` is null for the Hausdorff
measure of dimension `p + (dim E - p)/(k + α)`.  Taking `p = dim F - 1` and
`α = 0`, the hypothesis `dim E < dim F + k` is exactly what makes that dimension
at most `dim F`, so `f '' s` is null for `μH[dim F]`, which is a Haar measure on
`F`; any other Haar measure is absolutely continuous with respect to it.

The hypothesis `finrank E < finrank F + k` is the sharp smoothness threshold
`k ≥ dim E - dim F + 1`; Whitney's 1935 example of a `C¹` function constant on
no arc of its critical set shows it cannot be lowered. -/
theorem sard_of_lt_finrank (μ : Measure F) [μ.IsAddHaarMeasure]
    {f : E → F} {k : ℕ} (hf : ContDiff ℝ k f) {s : Set E}
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderiv ℝ f x))
    (hFE : finrank ℝ F < finrank ℝ E) (hk : finrank ℝ E < finrank ℝ F + k) :
    μ (f '' s) = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  -- `F` is nontrivial: onto a zero-dimensional space every linear map is surjective.
  have hF : 1 ≤ finrank ℝ F := by
    by_contra h
    have hsub : Subsingleton F := (Module.finrank_zero_iff (R := ℝ)).mp (by omega)
    exact hcrit x₀ hx₀ fun y => ⟨0, Subsingleton.elim _ _⟩
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hp : finrank ℝ F - 1 < finrank ℝ E := by omega
  -- Moreira's theorem with rank bound `dim F - 1` and Hölder exponent `0`.
  have hmain := hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le
    (E := E) (F := F) (p := finrank ℝ F - 1) (k := k) (α := 0) hp hk0 (f := f) (s := s)
    (fun x _ => ContDiffMoreiraHolderAt.zero_exponent_iff.2 hf.contDiffAt)
    (fun x hx => by
      have hne : LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] F) ≠ ⊤ :=
        fun h => hcrit x hx (LinearMap.range_eq_top.1 h)
      have := Submodule.finrank_lt hne
      omega)
  -- The Moreira dimension is at most `dim F` exactly because `dim E < dim F + k`.
  have hb : ((sardMoreiraBound (finrank ℝ E) k 0 (finrank ℝ F - 1) : ℝ≥0) : ℝ) ≤
      finrank ℝ F := by
    have hmul := mul_sardMoreiraBound (n := finrank ℝ E) (p := finrank ℝ F - 1) hk0 hp.le 0
    simp only [Set.Icc.coe_zero, add_zero] at hmul
    have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    rw [← mul_le_mul_iff_right₀ hkpos, hmul]
    have h1 : ((finrank ℝ F - 1 : ℕ) : ℝ) = finrank ℝ F - 1 := by
      rw [Nat.cast_sub hF, Nat.cast_one]
    have h2 : ((finrank ℝ E : ℕ) : ℝ) + 1 ≤ finrank ℝ F + k := by exact_mod_cast hk
    rw [h1]
    nlinarith
  have hH : μH[(finrank ℝ F : ℝ)] (f '' s) = 0 :=
    nonpos_iff_eq_zero.1 ((Measure.hausdorffMeasure_mono hb _).trans hmain.le)
  exact Measure.absolutelyContinuous_isAddHaarMeasure μ μH[(finrank ℝ F : ℝ)] hH

/-- **Theorem 14.2.1 (Sard's theorem).**  The critical values of a smooth map
form a set of measure zero.

Proved in all three dimension regimes.  Below the diagonal the whole image is
null and criticality is irrelevant; on the diagonal the statement is Mathlib's
Jacobian lemma after transport; above the diagonal it is the genuine Morse–Sard
theorem, `sard_of_lt_finrank`, derived from Moreira's theorem in
`Part2/SardMoreira/`.

Note which regime the applications need.  Proposition 1.2.1, which produces Morse
functions, applies Sard to the endpoint map of a normal bundle, whose source and
target both have dimension `n`: that is the equidimensional case, proved here.
It is proved in `Part1/DistSqMorse.lean` by running the normal-bundle argument in
charts. -/
theorem sard (μ : Measure F) [μ.IsAddHaarMeasure] {f : E → F} (hf : ContDiff ℝ ω f) :
    μ (criticalValues f) = 0 := by
  have hcrit : ∀ x ∈ criticalSet f, ¬ Function.Surjective (fderiv ℝ f x) :=
    fun _ hx => not_surjective_of_mem_criticalSet hx
  rcases lt_trichotomy (finrank ℝ E) (finrank ℝ F) with h | h | h
  · exact sard_of_finrank_lt μ (hf.of_le (OrderTop.le_top _)) _ h
  · exact sard_of_finrank_eq μ (hf.differentiable WithTop.top_ne_zero) hcrit h
  · exact sard_of_lt_finrank μ (k := finrank ℝ E - finrank ℝ F + 1)
      (hf.of_le (OrderTop.le_top _)) hcrit h (by omega)

end Sard

/-! ## §14.3 Transversality

The manifold statements (Theorem 14.3.1, Proposition 14.3.5, Theorem 14.3.7 and
the genericity theorems 14.3.10–14.3.13) need submanifolds and the `Cᵏ` topology
and are blueprint-only.  Their linear-algebraic core, however, is exactly the
content below, and it is what the codimension bookkeeping in Chapters 2, 3 and 8
actually uses. -/

section Transversality

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Transverse subspaces**: two subspaces are transverse when together they
span the whole space.  This is the tangent-space condition `T_uM + T_uN = T_uP`
of Theorem 14.3.1. -/
def IsTransverse (U V : Submodule ℝ E) : Prop := U ⊔ V = ⊤

theorem isTransverse_comm {U V : Submodule ℝ E} (h : IsTransverse U V) :
    IsTransverse V U := by
  rw [IsTransverse, sup_comm]; exact h

/-- Everything is transverse to the whole space. -/
theorem isTransverse_top (U : Submodule ℝ E) : IsTransverse U ⊤ := by
  simp [IsTransverse]

/-- **The dimension count for a transverse intersection** (Theorem 14.3.1).
When `U` and `V` are transverse, `dim U + dim V = dim E + dim (U ⊓ V)`;
equivalently the codimension of the intersection is the sum of the
codimensions, which is the numerical content of the theorem. -/
theorem finrank_add_finrank_of_isTransverse [FiniteDimensional ℝ E]
    {U V : Submodule ℝ E} (h : IsTransverse U V) :
    Module.finrank ℝ U + Module.finrank ℝ V
      = Module.finrank ℝ E + Module.finrank ℝ (U ⊓ V : Submodule ℝ E) := by
  have key := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [IsTransverse] at h
  rw [h] at key
  simp only [finrank_top] at key
  omega

/-- **Codimensions add** (Theorem 14.3.1, restated).  Writing `codim W` for
`dim E - dim W`, a transverse intersection has
`codim (U ⊓ V) = codim U + codim V`. -/
theorem codim_inf_of_isTransverse [FiniteDimensional ℝ E]
    {U V : Submodule ℝ E} (h : IsTransverse U V) :
    Module.finrank ℝ E - Module.finrank ℝ (U ⊓ V : Submodule ℝ E)
      = (Module.finrank ℝ E - Module.finrank ℝ U)
        + (Module.finrank ℝ E - Module.finrank ℝ V) := by
  have key := finrank_add_finrank_of_isTransverse h
  have hU : Module.finrank ℝ U ≤ Module.finrank ℝ E := Submodule.finrank_le U
  have hV : Module.finrank ℝ V ≤ Module.finrank ℝ E := Submodule.finrank_le V
  omega

/-- **Remark 14.3.4.**  Two subspaces whose dimensions sum to less than the
dimension of the ambient space cannot be transverse: transversality in that
range would force an intersection of negative dimension.  For submanifolds this
is the statement that transversality means *disjointness*. -/
theorem not_isTransverse_of_finrank_add_lt [FiniteDimensional ℝ E]
    {U V : Submodule ℝ E}
    (h : Module.finrank ℝ U + Module.finrank ℝ V < Module.finrank ℝ E) :
    ¬ IsTransverse U V := by
  intro htr
  have key := finrank_add_finrank_of_isTransverse htr
  omega

end Transversality

end Chapter14
end MorseFloer
