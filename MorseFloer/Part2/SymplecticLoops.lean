import MorseFloer.Part2.UnitaryLoops
import MorseFloer.Part2.SymplecticConnected

/-!
# Loops of symplectic matrices

A loop of symplectic matrices based at the identity, on which `ρ` has a closed continuous angle,
is homotopic to the constant loop with its ends fixed (`loop_homotopic_refl`). Two paths from the
identity to the same matrix along which the angle of `ρ` changes by the same amount are therefore
homotopic with their ends fixed (`homotopic_of_lifts`).

The loop is first deformed into `U(n)` by the polar decomposition `A = (A R⁻¹) R`,
`R = √(AᵀA)`: the positive factor is contracted to the identity along the Cayley path of
`Part2/SymplecticConnected.lean`, continuously in `A` since the square root is. On `U(n)`,
`ρ = det`, so the winding of `det` is zero and `Part2/UnitaryLoops.lean` contracts the loop; the
contraction through free loops is turned into one with the base point fixed by multiplying with the
inverse of its value at the base point.
-/

open Matrix unitInterval ContinuousMap
open scoped MatrixOrder

namespace MorseFloer
namespace MaslovIndex

open Chapter7 Rho UnitaryLoops

variable {n : ℕ}

/-- The symplectic group as a topological space. -/
abbrev SpT (n : ℕ) := ↥(Matrix.symplecticGroup (Fin n) ℝ)

/-! ### Angles along homotopies of loops -/

section Angles

/-- **A closed angle survives a homotopy of loops.** -/
theorem exists_closed_lift_of_homotopy {φ : I × I → ℂ} (hφ : Continuous φ)
    (h1 : ∀ p, ‖φ p‖ = 1) (hloop : ∀ s, φ (s, 0) = φ (s, 1)) {θ : I → ℝ} (hθc : Continuous θ)
    (hθe : ∀ t, Complex.exp (θ t * Complex.I) = φ (0, t)) (hθ01 : θ 0 = θ 1) :
    ∃ θ' : I → ℝ, Continuous θ' ∧ θ' 0 = θ' 1 ∧
      ∀ t, Complex.exp (θ' t * Complex.I) = φ (1, t) := by
  set π : ℝ → I := Set.projIcc 0 1 zero_le_one
  have hπ : Continuous π := continuous_projIcc
  have hψ : Continuous fun p : ℝ × ℝ => φ (π p.1, π p.2) :=
    hφ.comp ((hπ.comp continuous_fst).prodMk (hπ.comp continuous_snd))
  obtain ⟨G, hG, hG0, hGe⟩ := exists_lift hψ (fun p => h1 _) (0, 0) (θ₀ := θ 0) (by
    rw [hθe]; simp [π])
  have hmul : ∀ s : ℝ, ∃ k : ℤ, G (s, 1) - G (s, 0) = k * Real.pi := fun s => by
    have h : Complex.exp (G (s, 1) * Complex.I) = Complex.exp (G (s, 0) * Complex.I) := by
      rw [hGe, hGe]
      simp only [π, Set.projIcc_left, Set.projIcc_right]
      exact (hloop _).symm
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    refine ⟨2 * m, ?_⟩
    have := congrArg Complex.im hm
    simp at this
    push_cast; linarith
  have hconst := eq_of_exp_two_mul
    ((hG.comp (continuous_id.prodMk continuous_const)).sub
      (hG.comp (continuous_id.prodMk continuous_const))) hmul 0 1
  have h0 : (fun t : ℝ => G (0, t)) = fun t => θ (π t) :=
    lift_unique (hG.comp (continuous_const.prodMk continuous_id)) (hθc.comp hπ)
      (fun t => by rw [hGe, hθe]; simp [π]) 0 (by simp [π, hG0])
  have e1 : G (0, 1) = θ 1 := by
    have := congrFun h0 1
    simp only [π, Set.projIcc_right] at this
    exact this
  have e0 : G (0, 0) = θ 0 := by
    have := congrFun h0 0
    simp only [π, Set.projIcc_left] at this
    exact this
  simp only [Pi.sub_apply, Function.comp_apply, id] at hconst
  refine ⟨fun t => G (1, t), hG.comp (continuous_const.prodMk continuous_subtype_val),
    show G (1, 0) = G (1, 1) by linarith, fun t => ?_⟩
  rw [hGe]
  simp [π]

end Angles

/-! ### `ρ` on the unitary group -/

section RealForm

theorem rho_realForm {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    rho n (realForm V) = V.det := by
  have hO : Chapter5.IsOrthogonalMat (realForm V) := by
    rw [Chapter5.IsOrthogonalMat, realForm_transpose, ← realForm_mul,
      ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').1 hV, realForm_one]
  unfold realForm at hO ⊢
  rw [rho_det_unitary n _ _ hO]
  congr 1
  ext i j
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm, Complex.re_add_im]

end RealForm

/-! ### The polar decomposition, continuously -/

section Polar

/-- The positive factor `√(AᵀA)`. -/
noncomputable def posPart (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  CFC.sqrt (Aᵀ * A)

theorem posPart_spec {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ) :
    posPart A * posPart A = Aᵀ * A ∧ (posPart A).PosSemidef ∧ (posPart A).det ≠ 0 ∧
      posPart A ∈ Matrix.symplecticGroup (Fin n) ℝ := by
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr
    (Ne.isUnit (det_ne_zero_of_mem_symplecticGroup hA))
  have hQpos : (Aᵀ * A).PosDef := by
    have := Matrix.PosDef.conjTranspose_mul_self A (Matrix.mulVec_injective_iff_isUnit.mpr hAu)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact sqrt_mem_symplecticGroup (Submonoid.mul_mem _ (SymplecticGroup.transpose_mem hA) hA)
    hQpos

theorem posPart_one : posPart (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) = 1 := by
  rw [posPart, Matrix.transpose_one, Matrix.mul_one, CFC.sqrt_one]

set_option backward.isDefEq.respectTransparency false in
theorem continuous_posPart {X : Type*} [TopologicalSpace X]
    {F : X → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hF : Continuous F) :
    Continuous fun x => posPart (F x) := by
  have h0 : ∀ x, 0 ≤ (F x)ᵀ * F x := fun x => by
    have := Matrix.posSemidef_conjTranspose_mul_self (F x)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact Matrix.nonneg_iff_posSemidef.mpr this
  open scoped Matrix.Norms.L2Operator in
  exact CFC.continuousOn_sqrt.comp_continuous (hF.matrix_transpose.mul hF) h0

/-- The complex matrix of a real matrix commuting with `J`. -/
noncomputable def cplx (U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  U.toBlocks₁₁.map (fun x : ℝ => (x : ℂ)) + Complex.I • U.toBlocks₂₁.map (fun x : ℝ => (x : ℂ))

theorem continuous_cplx {X : Type*} [TopologicalSpace X]
    {F : X → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hF : Continuous F) :
    Continuous fun x => cplx (F x) := by
  unfold cplx
  refine (continuous_pi fun i => continuous_pi fun j => ?_).add
    ((continuous_pi fun i => continuous_pi fun j => ?_).const_smul Complex.I) <;>
  · simp only [Matrix.map_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.of_apply]
    fun_prop

/-- The unitary factor `A R⁻¹` is the real form of a unitary matrix. -/
theorem unitPart_spec {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ) :
    A * (posPart A)⁻¹ = realForm (cplx (A * (posPart A)⁻¹)) ∧
      cplx (A * (posPart A)⁻¹) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  obtain ⟨hRR, hRp, hRdet, hRmem⟩ := posPart_spec hA
  set R := posPart A
  have hRt : Rᵀ = R := transpose_eq_of_posSemidef hRp
  set U := A * R⁻¹
  have hUmem : U ∈ Matrix.symplecticGroup (Fin n) ℝ :=
    Submonoid.mul_mem _ hA (Chapter5.inv_mem_symplecticGroup hRmem)
  have hUo : Uᵀ * U = 1 := by
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hRt]
    calc R⁻¹ * Aᵀ * (A * R⁻¹) = R⁻¹ * (R * R) * R⁻¹ := by
          rw [hRR]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul R (Ne.isUnit hRdet), Matrix.one_mul,
            Matrix.mul_nonsing_inv R (Ne.isUnit hRdet)]
  have hUc : U * Matrix.J (Fin n) ℝ = Matrix.J (Fin n) ℝ * U :=
    Chapter5.complexLinear_of_symplectic_of_orthogonal hUmem hUo
  have hUV : U = realForm (cplx U) := eq_realForm_of_commute hUc
  refine ⟨hUV, Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  apply realForm_injective
  rw [realForm_mul, realForm_one, Matrix.star_eq_conjTranspose, ← realForm_transpose, ← hUV, hUo]

theorem posPath_one_left (s : ℝ) :
    posPath (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) s = 1 := by
  unfold posPath
  rw [← add_smul, ← add_smul, show 1 + s + (1 - s) = (2 : ℝ) by ring,
    show 1 - s + (1 + s) = (2 : ℝ) by ring]
  exact Matrix.mul_nonsing_inv _ (Ne.isUnit (by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]; exact pow_ne_zero _ two_ne_zero))

end Polar

/-! ### Homotopies of paths in `Sp(2n)` -/

section Paths

/-- Build a homotopy of paths in `Sp(2n)`, ends fixed, from a continuous function. -/
theorem pathHomotopic_of {x y : SpT n} {p q : Path x y}
    (H : I × I → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hH : Continuous H)
    (hmem : ∀ z, H z ∈ Matrix.symplecticGroup (Fin n) ℝ) (h0 : ∀ t, H (0, t) = p t)
    (h1 : ∀ t, H (1, t) = q t) (hx : ∀ s, H (s, 0) = x) (hy : ∀ s, H (s, 1) = y) :
    p.Homotopic q :=
  ⟨{ toFun := fun z => ⟨H z, hmem z⟩
     continuous_toFun := hH.subtype_mk _
     map_zero_left := fun t => Subtype.ext (h0 t)
     map_one_left := fun t => Subtype.ext (h1 t)
     prop' := fun s t ht => by
       rcases ht with rfl | rfl
       · exact Subtype.ext ((hx s).trans (by simp))
       · exact Subtype.ext ((hy s).trans (by simp)) }⟩

/-- **A loop in `Sp(2n)` on which `ρ` has a closed angle is contractible, ends fixed.** -/
theorem loop_homotopic_refl (L : Path (1 : SpT n) 1)
    (hw : ∃ θ : I → ℝ, Continuous θ ∧ θ 0 = θ 1 ∧
      ∀ t, Complex.exp (θ t * Complex.I) = rho n (L t)) :
    L.Homotopic (Path.refl 1) := by
  set l : I → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := fun t => (L t : _)
  have hl : Continuous l := continuous_subtype_val.comp L.continuous
  have hlmem : ∀ t, l t ∈ Matrix.symplecticGroup (Fin n) ℝ := fun t => (L t).2
  have hl0 : l 0 = 1 := by simp [l]
  have hl1 : l 1 = 1 := by simp [l]
  set R : I → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := fun t => posPart (l t)
  have hR : Continuous R := continuous_posPart hl
  have hRspec := fun t => posPart_spec (hlmem t)
  have hRt : ∀ t, (R t)ᵀ = R t := fun t => transpose_eq_of_posSemidef (hRspec t).2.1
  have hRJR : ∀ t, R t * Matrix.J (Fin n) ℝ * R t = Matrix.J (Fin n) ℝ := fun t => by
    have := SymplecticGroup.mem_iff'.mp (hRspec t).2.2.2; rwa [hRt] at this
  -- the retraction onto `U(n)`
  set r : I × I → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
    fun p => l p.2 * (posPath (R p.2) p.1)⁻¹
  have hPmem : ∀ p : I × I, posPath (R p.2) p.1 ∈ Matrix.symplecticGroup (Fin n) ℝ :=
    fun p => posPath_mem (hRspec p.2).2.1 (hRJR p.2) p.1.2
  have hrmem : ∀ p, r p ∈ Matrix.symplecticGroup (Fin n) ℝ := fun p =>
    Submonoid.mul_mem _ (hlmem p.2) (Chapter5.inv_mem_symplecticGroup (hPmem p))
  have hrc : Continuous r := by
    have hnum : Continuous fun p : I × I => (1 + (p.1 : ℝ)) • R p.2 +
        (1 - (p.1 : ℝ)) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
      have := hR.comp (continuous_snd : Continuous (Prod.snd : I × I → I)); fun_prop
    have hden : Continuous fun p : I × I => (1 - (p.1 : ℝ)) • R p.2 +
        (1 + (p.1 : ℝ)) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
      have := hR.comp (continuous_snd : Continuous (Prod.snd : I × I → I)); fun_prop
    have hP : Continuous fun p : I × I => posPath (R p.2) p.1 :=
      hnum.mul (continuousOn_univ.1 (continuousOn_inv_of_det_ne_zero hden.continuousOn
        fun p _ => (posDef_posPath_den (hRspec p.2).2.1 p.1.2).det_pos.ne'))
    exact (hl.comp continuous_snd).mul (continuousOn_univ.1 (continuousOn_inv_of_det_ne_zero
      hP.continuousOn fun p _ => det_ne_zero_of_mem_symplecticGroup (hPmem p)))
  have hr0 : ∀ s : I, r (s, 0) = 1 := fun s => by
    simp only [r, hl0, R, posPart_one, posPath_one_left, inv_one, Matrix.mul_one]
  have hr1 : ∀ s : I, r (s, 1) = 1 := fun s => by
    simp only [r, hl1, R, posPart_one, posPath_one_left, inv_one, Matrix.mul_one]
  -- its end is the real form of a unitary loop
  set U : I → Matrix (Fin n) (Fin n) ℂ := fun t => cplx (l t * (R t)⁻¹)
  have hUspec := fun t => unitPart_spec (hlmem t)
  have hrU : ∀ t, r (1, t) = realForm (U t) := fun t => by
    simp only [r, Set.Icc.coe_one, posPath_one]
    exact (hUspec t).1
  have hUc : Continuous U := continuous_cplx (hl.mul (continuousOn_univ.1
    (continuousOn_inv_of_det_ne_zero hR.continuousOn fun t _ => (hRspec t).2.2.1)))
  have hU0 : U 0 = 1 := realForm_injective (by rw [← hrU, hr0, realForm_one])
  have hU1 : U 1 = 1 := realForm_injective (by rw [← hrU, hr1, realForm_one])
  let Uc : C(I, Matrix (Fin n) (Fin n) ℂ) := ⟨U, hUc⟩
  have hUloop : IsULoop Uc := ⟨fun t => (hUspec t).2, by simp [Uc, hU0, hU1]⟩
  -- the winding of `det` on `U` is that of `ρ` on the loop
  have hUw : WindsZero Uc := by
    obtain ⟨θ, hθc, hθ01, hθe⟩ := hw
    obtain ⟨θ', hθ'c, hθ'01, hθ'e⟩ := exists_closed_lift_of_homotopy (φ := fun p => rho n (r p))
      ((continuousOn_rho n).comp_continuous hrc hrmem) (fun p => norm_rho n _)
      (fun s => by simp only [hr0, hr1]) hθc (fun t => by
        rw [hθe]; simp [r, R, posPath_zero (hRspec t).2.1, l]) hθ01
    exact ⟨θ', hθ'c, hθ'01, fun t => by rw [hθ'e, hrU, rho_realForm (hUspec t).2]; rfl⟩
  obtain ⟨K⟩ := nullHomotopic_of_windsZero hUloop hUw
  -- the two homotopies: retract, then contract with the base point held
  have hstep1 : L.Homotopic ⟨⟨fun t => ⟨realForm (U t), realForm_mem_symplecticGroup
      (hUspec t).2⟩, (continuous_realForm.comp hUc).subtype_mk _⟩,
      Subtype.ext (by simp [hU0, realForm_one]), Subtype.ext (by simp [hU1, realForm_one])⟩ :=
    pathHomotopic_of r hrc hrmem (fun t => by simp [r, R, posPath_zero (hRspec t).2.1, l])
      (fun t => by simp [hrU]) (fun s => by simp [hr0]) (fun s => by simp [hr1])
  have hK : ∀ z : I × I, K z ∈ Matrix.unitaryGroup (Fin n) ℂ := fun z => (K.prop z.1).1 z.2
  set K' : I × I → Matrix (Fin n) (Fin n) ℂ := fun z => star (K (z.1, 0)) * K z
  have hK'mem : ∀ z, K' z ∈ Matrix.unitaryGroup (Fin n) ℂ := fun z =>
    Submonoid.mul_mem _ (Unitary.star_mem (hK _)) (hK z)
  refine hstep1.trans (pathHomotopic_of (fun z => realForm (K' z))
    (continuous_realForm.comp ((K.continuous.comp (continuous_fst.prodMk continuous_const)).star.mul
      K.continuous)) (fun z => realForm_mem_symplecticGroup (hK'mem z)) (fun t => ?_) (fun t => ?_)
    (fun s => ?_) (fun s => ?_))
  · simp [K', K.apply_zero, Uc, hU0]
  · simp [K', K.apply_one, realForm_one]
  · simp [K', (Matrix.mem_unitaryGroup_iff').1 (hK (s, 0)), realForm_one]
  · have hloop : K (s, 0) = K (s, 1) := (K.prop s).2
    simp only [K']
    rw [← hloop, (Matrix.mem_unitaryGroup_iff').1 (hK (s, 0)), realForm_one]
    rfl

/-- **Paths with the same change of angle of `ρ` are homotopic, ends fixed.** -/
theorem homotopic_of_lifts {A : SpT n} (α β : Path (1 : SpT n) A) {θα θβ : I → ℝ}
    (hα : Continuous θα) (hβ : Continuous θβ)
    (heα : ∀ t, Complex.exp (θα t * Complex.I) = rho n (α t))
    (heβ : ∀ t, Complex.exp (θβ t * Complex.I) = rho n (β t))
    (h : θα 1 - θα 0 = θβ 1 - θβ 0) : α.Homotopic β := by
  set π : ℝ → I := Set.projIcc 0 1 zero_le_one
  have hπ : Continuous π := continuous_projIcc
  -- an explicit angle of `ρ` along `α` followed by `β` backwards
  set Θ : I → ℝ := fun t => θα (π (2 * t)) - θβ 1 + θβ (π (2 - 2 * t))
  have hΘ : Continuous Θ := by
    have hm : Continuous fun t : I => (2 : ℝ) * (t : ℝ) :=
      continuous_const.mul continuous_subtype_val
    have hm' : Continuous fun t : I => (2 : ℝ) - 2 * (t : ℝ) := continuous_const.sub hm
    exact ((hα.comp (hπ.comp hm)).sub continuous_const).add (hβ.comp (hπ.comp hm'))
  have hA : ‖rho n (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)‖ = 1 := norm_rho n _
  have hΘe : ∀ t, Complex.exp (Θ t * Complex.I) = rho n ((α.trans β.symm) t) := fun t => by
    have hsplit : ∀ a b c : ℝ, Complex.exp (((a - b + c : ℝ) : ℂ) * Complex.I) =
        Complex.exp (a * Complex.I) * Complex.exp (c * Complex.I) / Complex.exp (b * Complex.I) :=
      fun a b c => by
        rw [← Complex.exp_add, ← Complex.exp_sub]; congr 1; push_cast; ring
    rw [Path.trans_apply]
    split_ifs with ht
    · -- first half: the `β` terms cancel
      have e1 : π (2 * t) = ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ :=
        Set.projIcc_of_mem _ _
      have e2 : π (2 - 2 * t) = 1 := Set.projIcc_of_right_le _ (by linarith)
      simp only [Θ, e1, e2, sub_add_cancel]
      exact heα _
    · -- second half: `α 1 = β 1 = A`
      have e1 : π (2 * t) = 1 := Set.projIcc_of_right_le _ (by push Not at ht; linarith)
      have hmem : 2 - 2 * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [t.2.2], by
        push Not at ht; linarith⟩
      have e2 : π (2 - 2 * t) = ⟨2 - 2 * t, hmem⟩ := Set.projIcc_of_mem _ _
      simp only [Θ, e1, e2]
      rw [hsplit, heα, heβ, heβ, α.target, β.target]
      rw [Path.symm_apply, Function.comp_apply]
      have hσ : ∀ x : I, (x : ℝ) = 2 * t - 1 → σ x = ⟨2 - 2 * t, hmem⟩ := fun x hx =>
        Subtype.ext (by rw [unitInterval.coe_symm_eq, hx]; ring)
      rw [hσ _ rfl]
      have hne : rho n (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hA; exact zero_ne_one hA
      field_simp
  have hloop := loop_homotopic_refl (α.trans β.symm) ⟨Θ, hΘ, by
    simp only [Θ, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one, sub_zero]
    have e0 : π 0 = 0 := Set.projIcc_left _
    have e1 : π 2 = 1 := Set.projIcc_of_right_le _ (by norm_num)
    have e2 : π (2 - 2) = 0 := by rw [sub_self]; exact e0
    rw [e0, e1, e2]
    linarith, hΘe⟩
  -- `α ≃ α (β⁻¹ β) ≃ (α β⁻¹) β ≃ β`
  have h1 : α.Homotopic (α.trans (Path.refl A)) := Path.Homotopic.symm ⟨Path.Homotopy.transRefl α⟩
  have h2 : (α.trans (Path.refl A)).Homotopic (α.trans (β.symm.trans β)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl α) ⟨Path.Homotopy.reflSymmTrans β⟩
  have h3 : (α.trans (β.symm.trans β)).Homotopic ((α.trans β.symm).trans β) :=
    Path.Homotopic.symm ⟨Path.Homotopy.transAssoc α β.symm β⟩
  have h4 : ((α.trans β.symm).trans β).Homotopic ((Path.refl 1).trans β) :=
    Path.Homotopic.hcomp hloop (Path.Homotopic.refl β)
  have h5 : ((Path.refl 1).trans β).Homotopic β := ⟨Path.Homotopy.reflTrans β⟩
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

end Paths

end MaslovIndex
end MorseFloer
