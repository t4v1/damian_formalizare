/-
Copyright (c) 2026 Octavian Halmaghi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Octavian Halmaghi
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Additivity of the index of a linear map under composition

`LinearMap.finrank_ker_sub_finrank_coker_comp` says that the quantity

  `dim (ker f) - dim (coker f)`

is additive under composition, whenever the four spaces involved are finite
dimensional. For continuous linear maps between Banach spaces this quantity is
the Fredholm index, and the statement is the additivity of that index; but
nothing here is topological, so it is stated for bare linear maps.

The usual proof goes through the six-term exact sequence

  `0 → ker a → ker (b ∘ a) → ker b → coker a → coker (b ∘ a) → coker b → 0`

and an alternating-sum count. That is avoided here: four applications of
rank–nullity to four explicitly constructed maps give the identity directly,
which needs nothing beyond `LinearMap.finrank_range_add_finrank_ker`,
`Submodule.liftQ` and `Submodule.comapSubtypeEquivOfLe`.

This belongs beside `LinearMap.finrank_range_add_finrank_ker` in
`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`.
-/

namespace LinearMap

variable {K : Type*} [DivisionRing K]

theorem finrank_ker_sub_finrank_coker_comp {X Y Z : Type*}
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
    (a : X →ₗ[K] Y) (b : Y →ₗ[K] Z)
    [FiniteDimensional K (LinearMap.ker (b ∘ₗ a))] [FiniteDimensional K (LinearMap.ker b)]
    [FiniteDimensional K (Y ⧸ LinearMap.range a)]
    [FiniteDimensional K (Z ⧸ LinearMap.range (b ∘ₗ a))] :
    (Module.finrank K (LinearMap.ker (b ∘ₗ a)) : ℤ)
        - (Module.finrank K (Z ⧸ LinearMap.range (b ∘ₗ a)) : ℤ)
      = ((Module.finrank K (LinearMap.ker b) : ℤ)
          - (Module.finrank K (Z ⧸ LinearMap.range b) : ℤ))
        + ((Module.finrank K (LinearMap.ker a) : ℤ)
          - (Module.finrank K (Y ⧸ LinearMap.range a) : ℤ)) := by
  -- `ker a ≤ ker (b ∘ a)`
  have hle : LinearMap.ker a ≤ LinearMap.ker (b ∘ₗ a) := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    rw [hx, map_zero]
  -- (1) `dim ker (b ∘ a) = dim (ker b ⊓ range a) + dim ker a`
  have h1 : Module.finrank K (LinearMap.ker (b ∘ₗ a))
      = Module.finrank K ↥(LinearMap.ker b ⊓ LinearMap.range a)
        + Module.finrank K (LinearMap.ker a) := by
    have hrf : LinearMap.range (a ∘ₗ (LinearMap.ker (b ∘ₗ a)).subtype)
        = LinearMap.ker b ⊓ LinearMap.range a := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      ext y
      simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range,
        LinearMap.comp_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, x, rfl⟩
      · rintro ⟨hy, x, rfl⟩
        exact ⟨x, hy, rfl⟩
    have hkf : LinearMap.ker (a ∘ₗ (LinearMap.ker (b ∘ₗ a)).subtype)
        = Submodule.comap (LinearMap.ker (b ∘ₗ a)).subtype (LinearMap.ker a) :=
      LinearMap.ker_comp _ _
    have hr := LinearMap.finrank_range_add_finrank_ker
      (a ∘ₗ (LinearMap.ker (b ∘ₗ a)).subtype)
    rw [hrf, hkf, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hr
    omega
  -- (2) `dim ker b = dim S + dim (ker b ⊓ range a)`
  have h2 : Module.finrank K (LinearMap.ker b)
      = Module.finrank K ↥(Submodule.map (LinearMap.range a).mkQ (LinearMap.ker b))
        + Module.finrank K ↥(LinearMap.ker b ⊓ LinearMap.range a) := by
    have hrg : LinearMap.range ((LinearMap.range a).mkQ ∘ₗ (LinearMap.ker b).subtype)
        = Submodule.map (LinearMap.range a).mkQ (LinearMap.ker b) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hkg : LinearMap.ker ((LinearMap.range a).mkQ ∘ₗ (LinearMap.ker b).subtype)
        = Submodule.comap (LinearMap.ker b).subtype
            (LinearMap.ker b ⊓ LinearMap.range a) := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_inf,
        Submodule.comap_subtype_self, top_inf_eq]
    have hr := LinearMap.finrank_range_add_finrank_ker
      ((LinearMap.range a).mkQ ∘ₗ (LinearMap.ker b).subtype)
    rw [hrg, hkg, (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq] at hr
    omega
  -- (3) `dim (Y ⧸ range a) = dim T + dim S`
  have hle3 : LinearMap.range a
      ≤ LinearMap.ker ((LinearMap.range (b ∘ₗ a)).mkQ ∘ₗ b) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  have h3 : Module.finrank K (Y ⧸ LinearMap.range a)
      = Module.finrank K ↥(Submodule.map (LinearMap.range (b ∘ₗ a)).mkQ (LinearMap.range b))
        + Module.finrank K ↥(Submodule.map (LinearMap.range a).mkQ (LinearMap.ker b)) := by
    have hker3 : LinearMap.ker ((LinearMap.range (b ∘ₗ a)).mkQ ∘ₗ b)
        = LinearMap.ker b ⊔ LinearMap.range a := by
      refine le_antisymm (fun y hy => ?_) ?_
      · simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hy
        obtain ⟨x, hx⟩ := hy
        have hmem : y - a x ∈ LinearMap.ker b := by
          simp only [LinearMap.mem_ker, map_sub, hx, sub_self]
        have hy' : y = (y - a x) + a x := by abel
        rw [hy']
        exact Submodule.add_mem_sup hmem ⟨x, rfl⟩
      · rw [sup_le_iff]
        refine ⟨fun y hy => ?_, hle3⟩
        simp only [LinearMap.mem_ker] at hy
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, hy, map_zero]
    have hrg : LinearMap.range ((LinearMap.range a).liftQ
          ((LinearMap.range (b ∘ₗ a)).mkQ ∘ₗ b) hle3)
        = Submodule.map (LinearMap.range (b ∘ₗ a)).mkQ (LinearMap.range b) := by
      rw [Submodule.range_liftQ]
      exact LinearMap.range_comp b _
    have hkg : LinearMap.ker ((LinearMap.range a).liftQ
          ((LinearMap.range (b ∘ₗ a)).mkQ ∘ₗ b) hle3)
        = Submodule.map (LinearMap.range a).mkQ (LinearMap.ker b) := by
      rw [Submodule.ker_liftQ, hker3, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
    have hr := LinearMap.finrank_range_add_finrank_ker
      ((LinearMap.range a).liftQ ((LinearMap.range (b ∘ₗ a)).mkQ ∘ₗ b) hle3)
    rw [hrg, hkg] at hr
    omega
  -- (4) `dim (Z ⧸ range (b ∘ a)) = dim (Z ⧸ range b) + dim T`
  have hle4 : LinearMap.range (b ∘ₗ a) ≤ LinearMap.ker (LinearMap.range b).mkQ := by
    rw [Submodule.ker_mkQ]
    exact LinearMap.range_comp_le_range a b
  have h4 : Module.finrank K (Z ⧸ LinearMap.range (b ∘ₗ a))
      = Module.finrank K (Z ⧸ LinearMap.range b)
        + Module.finrank K ↥(Submodule.map (LinearMap.range (b ∘ₗ a)).mkQ
            (LinearMap.range b)) := by
    have hrg : LinearMap.range ((LinearMap.range (b ∘ₗ a)).liftQ (LinearMap.range b).mkQ hle4)
        = ⊤ := by
      rw [Submodule.range_liftQ, Submodule.range_mkQ]
    have hkg : LinearMap.ker ((LinearMap.range (b ∘ₗ a)).liftQ (LinearMap.range b).mkQ hle4)
        = Submodule.map (LinearMap.range (b ∘ₗ a)).mkQ (LinearMap.range b) := by
      rw [Submodule.ker_liftQ, Submodule.ker_mkQ]
    have hr := LinearMap.finrank_range_add_finrank_ker
      ((LinearMap.range (b ∘ₗ a)).liftQ (LinearMap.range b).mkQ hle4)
    rw [hrg, hkg, Submodule.topEquiv.finrank_eq] at hr
    omega
  omega

/-! ### A finite-rank perturbation of the identity -/

end LinearMap
