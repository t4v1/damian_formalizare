import MorseFloer.Part2.RhoProperties

/-!
# Properties of `ρ`: naturality and the transpose

Two more clauses of Theorem 7.1.3 for the map `ρ` of `Part2/Rho.lean`: `ρ(T A T⁻¹) = ρ(A)` for
`T` symplectic (`rho_naturality`) and `ρ(Aᵀ) = ρ(A⁻¹)` (`rho_transpose`).

For naturality, `T A T⁻¹` has the characteristic polynomial of `A`, its generalised eigenspace
at `μ` is the image of that of `A` under `T` (`E_conj_mul`), and `T` preserves `ω`, hence the
Hermitian form `G`; the positive index of a form is invariant under an injective linear
isometry, the Gram matrices of a basis and of its image being equal
(`posIndex_map_of_isometry`).  So all the spectral data agree and the factors agree.  For the
transpose, `Aᵀ J A = J` gives `Aᵀ = J A⁻¹ J⁻¹`, and `J` is symplectic.
-/

open Polynomial Matrix Module

namespace MorseFloer
namespace Rho

open Chapter7 SymplecticEigen SymplecticSpectrum EigenDecomp EigenMult HermitianIndex
  SignatureContinuity

/-! ### The index is invariant under isometries -/

section Isometry

variable {m : Type*} [Fintype m]

/-- The positive index of `G` is invariant under an injective linear map preserving `G`. -/
theorem posIndex_map_of_isometry {G : (m → ℂ) → (m → ℂ) → ℂ} (hG : IsHermForm G)
    (T : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (hT : LinearMap.ker T = ⊥) (hiso : ∀ x y, G (T x) (T y) = G x y)
    (V : Submodule ℂ (m → ℂ)) : posIndex G (V.map T) = posIndex G V := by
  classical
  obtain ⟨e, he, heV⟩ := exists_basis_family V
  have he' : LinearIndependent ℂ (T ∘ e) := he.map' T hT
  have hspan' : Submodule.span ℂ (Set.range (T ∘ e)) = V.map T := by
    rw [Set.range_comp, Submodule.span_image, heV]
  rw [posIndex_eq_countP hG he' hspan', posIndex_eq_countP hG he heV]
  have hgram : HermitianIndex.gram G (T ∘ e) = HermitianIndex.gram G e := by
    ext i j
    simp only [HermitianIndex.gram, Matrix.of_apply, Function.comp, hiso]
  rw [hgram]

end Isometry

/-! ### Naturality -/

variable {l : Type*} [DecidableEq l] [Fintype l]

theorem charpoly_conj_mul {M T : Matrix (l ⊕ l) (l ⊕ l) ℂ} (hT : IsUnit T.det) :
    (T * M * T⁻¹).charpoly = M.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT, Matrix.one_mul]

theorem inGen_conj_mul {M T : Matrix (l ⊕ l) (l ⊕ l) ℂ} (hT : IsUnit T.det) {μ : ℂ} {k : ℕ}
    {X : (l ⊕ l) → ℂ} : InGen (T * M * T⁻¹) μ k (T *ᵥ X) ↔ InGen M μ k X := by
  unfold InGen
  have e1 : T * M * T⁻¹ - μ • (1 : Matrix (l ⊕ l) (l ⊕ l) ℂ) = T * (M - μ • 1) * T⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_nonsing_inv _ hT]
  have e : (T * M * T⁻¹ - μ • (1 : Matrix (l ⊕ l) (l ⊕ l) ℂ)) ^ k
      = T * (M - μ • 1) ^ k * T⁻¹ := by
    rw [e1]
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.mul_nonsing_inv _ hT]
    | succ k ih =>
      rw [pow_succ, pow_succ, ih]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc T⁻¹ T, Matrix.nonsing_inv_mul _ hT, Matrix.one_mul]
  rw [e, Matrix.mulVec_mulVec, Matrix.mul_assoc (T * (M - μ • 1) ^ k),
    Matrix.nonsing_inv_mul _ hT, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    calc (M - μ • 1) ^ k *ᵥ X = T⁻¹ *ᵥ (T *ᵥ ((M - μ • 1) ^ k *ᵥ X)) := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hT, Matrix.one_mulVec]
      _ = 0 := by rw [h, Matrix.mulVec_zero]
  · intro h
    rw [h, Matrix.mulVec_zero]

/-- `E_μ(T M T⁻¹) = T (E_μ(M))`. -/
theorem E_conj_mul {M T : Matrix (l ⊕ l) (l ⊕ l) ℂ} (hT : IsUnit T.det) (μ : ℂ) :
    E (T * M * T⁻¹) μ = (E M μ).map (Matrix.toLin' T) := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · intro hy
    refine ⟨T⁻¹ *ᵥ y, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := (mem_E_iff _ _ _).1 hy
      refine (mem_E_iff _ _ _).2 ⟨k, (inGen_conj_mul hT).1 ?_⟩
      rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hT, Matrix.one_mulVec]
    · rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hT,
        Matrix.one_mulVec]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := (mem_E_iff _ _ _).1 hx
    rw [Matrix.toLin'_apply]
    exact (mem_E_iff _ _ _).2 ⟨k, (inGen_conj_mul hT).2 hk⟩

theorem mPos_conj_mul {A T : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hT : T ∈ Matrix.symplecticGroup l ℝ)
    (μ : ℂ) : mPos (cpx T * cpx A * (cpx T)⁻¹) μ = mPos (cpx A) μ := by
  have hunit := isUnit_det_cpx hT
  rw [mPos, mPos, E_conj_mul hunit]
  refine posIndex_map_of_isometry isHermForm_GForm _ ?_ ?_ _
  · rw [LinearMap.ker_eq_bot']
    intro x hx
    rw [Matrix.toLin'_apply] at hx
    calc x = (cpx T)⁻¹ *ᵥ (cpx T *ᵥ x) := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
      _ = 0 := by rw [hx, Matrix.mulVec_zero]
  · intro x y
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, GForm, GForm, HForm_cpx hT]

open Classical in
theorem sigma_conj_mul {A T : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hT : T ∈ Matrix.symplecticGroup l ℝ)
    (μ : ℂ) : sigma (cpx T * cpx A * (cpx T)⁻¹) μ = sigma (cpx A) μ := by
  unfold sigma
  rw [mPos_conj_mul hT, charpoly_conj_mul (isUnit_det_cpx hT)]

open Classical in
theorem factor_conj_mul {A T : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hT : T ∈ Matrix.symplecticGroup l ℝ)
    (μ : ℂ) : factor (cpx T * cpx A * (cpx T)⁻¹) μ = factor (cpx A) μ := by
  unfold factor
  rw [sigma_conj_mul hT, charpoly_conj_mul (isUnit_det_cpx hT)]

theorem rhoC_conj_mul {A T : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hT : T ∈ Matrix.symplecticGroup l ℝ) :
    rhoC (cpx T * cpx A * (cpx T)⁻¹) = rhoC (cpx A) := by
  classical
  rw [rhoC, rhoC, charpoly_conj_mul (isUnit_det_cpx hT)]
  exact Finset.prod_congr rfl fun μ _ => factor_conj_mul hT μ

omit [DecidableEq l] in
theorem cpx_mul (A B : Matrix (l ⊕ l) (l ⊕ l) ℝ) : cpx (A * B) = cpx A * cpx B := by
  rw [cpx, cpx, cpx, Matrix.map_mul]

/-- **Naturality: `ρ(T A T⁻¹) = ρ(A)`** for `T` symplectic (Theorem 7.1.3). -/
theorem rho_naturality (n : ℕ) (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    {T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hT : T ∈ Matrix.symplecticGroup (Fin n) ℝ) :
    rho n (T * A * T⁻¹) = rho n A := by
  rw [rho, rho, cpx_mul, cpx_mul, cpx_inv hT, rhoC_conj_mul hT]

/-! ### The transpose -/

theorem transpose_eq_conj_inv {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    Aᵀ = Matrix.J l ℝ * A⁻¹ * (Matrix.J l ℝ)⁻¹ := by
  have h := SymplecticGroup.mem_iff'.1 hA
  have hdetA : IsUnit A.det := by
    rw [SymplecticGroup.det_eq_one hA]
    exact isUnit_one
  have hJ : IsUnit (Matrix.J l ℝ).det := by
    rw [SymplecticGroup.det_eq_one (SymplecticGroup.J_mem l ℝ)]
    exact isUnit_one
  calc Aᵀ = Aᵀ * Matrix.J l ℝ * A * A⁻¹ * (Matrix.J l ℝ)⁻¹ := by
        rw [Matrix.mul_assoc (Aᵀ * Matrix.J l ℝ) A A⁻¹, Matrix.mul_nonsing_inv _ hdetA,
          Matrix.mul_one, Matrix.mul_assoc Aᵀ, Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one]
    _ = Matrix.J l ℝ * A⁻¹ * (Matrix.J l ℝ)⁻¹ := by rw [h]

/-- **`ρ(Aᵀ) = ρ(A⁻¹)`** (Theorem 7.1.3): `Aᵀ = J A⁻¹ J⁻¹`. -/
theorem rho_transpose (n : ℕ) {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ) : rho n Aᵀ = rho n A⁻¹ := by
  rw [transpose_eq_conj_inv hA, rho_naturality n A⁻¹ (SymplecticGroup.J_mem (Fin n) ℝ)]

end Rho
end MorseFloer
