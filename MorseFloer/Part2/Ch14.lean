import MorseFloer.Basic

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

* **Sard's theorem** (Theorem 14.2.1) is stated here and assumed.  Mathlib has
  measure-theoretic ingredients but no Sard for manifolds.  This single gap is
  what forces Proposition 1.2.1 and every transversality genericity statement in
  the book to remain assumed.
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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The set of critical points of a differentiable map (§14.2.a). -/
def criticalSet (f : E → F) : Set E := {x | IsCriticalPointOfMap (fderiv ℝ f x)}

/-- The set of critical values: the image of the critical set (§14.2.b).  Note
that a regular value need not be a value at all, and that a point outside the
critical set may still map to a critical value. -/
def criticalValues (f : E → F) : Set F := f '' criticalSet f

/-- **Theorem 14.2.1 (Sard's theorem).**  The critical values of a smooth map
form a set of measure zero.

*Assumed.*  This is the single most consequential gap in the project: it is what
Proposition 1.2.1 needs to produce Morse functions, and what every genericity
statement about transversality in Chapters 8 and 11 rests on.  Mathlib has the
measure-theoretic ingredients (`MeasureTheory.Function.Jacobian`, Hausdorff
dimension bounds) but no Sard theorem. -/
theorem sard (μ : MeasureTheory.Measure F) [μ.IsAddHaarMeasure]
    {f : E → F} (_hf : ContDiff ℝ ω f) :
    μ (criticalValues f) = 0 := by
  sorry

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
