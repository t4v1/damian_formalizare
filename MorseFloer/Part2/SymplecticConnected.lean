import MorseFloer.Part2.MaslovPaths

/-!
# `Sp(2n)` is path-connected

The path-connectedness half of **Proposition 5.6.9** of Audin–Damian, proved
by the polar decomposition, as the book does:

* for `A ∈ Sp(2n)`, `Q = AᵀA` is a positive definite symplectic matrix; its
  positive square root `R = √Q` (Mathlib's `CFC.sqrt`) is symplectic too,
  because `J⁻¹RJ` and `R⁻¹` are both positive square roots of
  `J⁻¹QJ = Q⁻¹` (`sqrt_mem_symplecticGroup`);
* `R` is joined to `Id` inside `Sp(2n)` by the path
  `R_s = ((1+s)R + (1−s))((1−s)R + (1+s))⁻¹`, the Cayley transform of `s` times
  the Cayley transform of `R`; it is symplectic because
  `P J P = Q' J Q'` for the two factors, a polynomial identity in `R` once
  `RJR = J` (`posPath`);
* `U = AR⁻¹` is orthogonal and symplectic, hence commutes with `J`, hence is
  the real form of a unitary matrix `V` (`eq_realForm_of_commute`);
* `U(n)` is path-connected: after a rotation `V ↦ e^{iθ}V` that removes the
  eigenvalue `−1`, the unitary Cayley path
  `W_s = ((1+s)W + (1−s))((1−s)W + (1+s))⁻¹` joins `Id` to `W` (`uPath`).

The last lemma, `joinedIn_conj`, is what Chapter 7 uses: conjugating a matrix
of `Sp(2n)⋆` by a symplectic matrix does not leave its path component.
-/

open scoped Matrix MatrixOrder
open Complex (I)

namespace MorseFloer
namespace Chapter7

section Generalities

theorem joinedIn_of_line {α : Type*} [TopologicalSpace α] {F : Set α} {x y : α} (γ : ℝ → α)
    (hγ : ContinuousOn γ unitInterval) (h0 : γ 0 = x) (h1 : γ 1 = y)
    (hmem : ∀ t ∈ unitInterval, γ t ∈ F) : JoinedIn F x y :=
  JoinedIn.ofLine hγ h0 h1 (by rintro _ ⟨t, ht, rfl⟩; exact hmem t ht)

variable {X : Type*} [TopologicalSpace X] {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
  [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [ContinuousInv₀ 𝕜]

/-- The inverse of a continuous family of invertible matrices is continuous. -/
theorem continuousOn_inv_of_det_ne_zero {F : X → Matrix n n 𝕜} {s : Set X}
    (hF : ContinuousOn F s) (hd : ∀ x ∈ s, (F x).det ≠ 0) :
    ContinuousOn (fun x => (F x)⁻¹) s := by
  have h : (fun x => (F x)⁻¹) = fun x => ((F x).det)⁻¹ • (F x).adjugate := by
    funext x; rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [h]
  have h1 : ContinuousOn (fun x => (F x).det) s := continuous_id.matrix_det.comp_continuousOn hF
  have h2 : ContinuousOn (fun x => (F x).adjugate) s :=
    continuous_id.matrix_adjugate.comp_continuousOn hF
  exact (h1.inv₀ hd).smul h2

end Generalities

/-! ## The positive part of the polar decomposition -/

section Polar

variable {l : Type*} [DecidableEq l] [Fintype l]

theorem transpose_J_mul_J : (Matrix.J l ℝ)ᵀ * Matrix.J l ℝ = 1 := by
  rw [Matrix.J_transpose, Matrix.neg_mul, Matrix.J_squared, neg_neg]

theorem J_mul_transpose_J : Matrix.J l ℝ * (Matrix.J l ℝ)ᵀ = 1 := by
  rw [Matrix.J_transpose, Matrix.mul_neg, Matrix.J_squared, neg_neg]

omit [DecidableEq l] [Fintype l] in
theorem transpose_eq_of_posSemidef {R : Matrix (l ⊕ l) (l ⊕ l) ℝ} (h : R.PosSemidef) :
    Rᵀ = R := by
  have := h.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem det_ne_zero_of_mem_symplecticGroup {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) : A.det ≠ 0 := by
  rw [SymplecticGroup.det_eq_one hA]; exact one_ne_zero

/-- The positive square root of a positive definite symplectic matrix is
symplectic: `J⁻¹RJ` and `R⁻¹` are both positive square roots of `Q⁻¹`. -/
theorem sqrt_mem_symplecticGroup {Q : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hQ : Q ∈ Matrix.symplecticGroup l ℝ) (hpos : Q.PosDef) :
    CFC.sqrt Q * CFC.sqrt Q = Q ∧ (CFC.sqrt Q).PosSemidef ∧ (CFC.sqrt Q).det ≠ 0 ∧
      CFC.sqrt Q ∈ Matrix.symplecticGroup l ℝ := by
  set R := CFC.sqrt Q with hRdef
  have hQ0 : 0 ≤ Q := hpos.posSemidef.nonneg
  have hRR : R * R = Q := CFC.sqrt_mul_sqrt_self Q hQ0
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg Q
  have hRp : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hR0
  have hdet : R.det ≠ 0 := by
    intro h
    have := hpos.det_pos
    rw [← hRR, Matrix.det_mul, h, zero_mul] at this
    exact lt_irrefl _ this
  refine ⟨hRR, hRp, hdet, ?_⟩
  have hQt : Qᵀ = Q := transpose_eq_of_posSemidef hpos.posSemidef
  have hQJQ : Q * Matrix.J l ℝ * Q = Matrix.J l ℝ := by
    have := SymplecticGroup.mem_iff'.mp hQ
    rwa [hQt] at this
  have hQinv : (Matrix.J l ℝ)ᵀ * Q * Matrix.J l ℝ = Q⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    calc (Matrix.J l ℝ)ᵀ * Q * Matrix.J l ℝ * Q
        = (Matrix.J l ℝ)ᵀ * (Q * Matrix.J l ℝ * Q) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQJQ, transpose_J_mul_J]
  set R' := (Matrix.J l ℝ)ᵀ * R * Matrix.J l ℝ with hR'
  have hR'0 : 0 ≤ R' := by
    have := hRp.conjTranspose_mul_mul_same (Matrix.J l ℝ)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this.nonneg
  have hR'R' : R' * R' = Q⁻¹ := by
    rw [← hQinv, ← hRR, hR']
    calc (Matrix.J l ℝ)ᵀ * R * Matrix.J l ℝ * ((Matrix.J l ℝ)ᵀ * R * Matrix.J l ℝ)
        = (Matrix.J l ℝ)ᵀ * R * (Matrix.J l ℝ * (Matrix.J l ℝ)ᵀ) * R * Matrix.J l ℝ := by
          simp only [Matrix.mul_assoc]
      _ = (Matrix.J l ℝ)ᵀ * (R * R) * Matrix.J l ℝ := by
          rw [J_mul_transpose_J, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hRi0 : 0 ≤ R⁻¹ := hRp.inv.nonneg
  have hRiRi : R⁻¹ * R⁻¹ = Q⁻¹ := by rw [← Matrix.mul_inv_rev, hRR]
  have h1 : CFC.sqrt Q⁻¹ = R' := CFC.sqrt_unique hR'R' hR'0
  have h2 : CFC.sqrt Q⁻¹ = R⁻¹ := CFC.sqrt_unique hRiRi hRi0
  have hkey : R' = R⁻¹ := h1.symm.trans h2
  have hRt : Rᵀ = R := transpose_eq_of_posSemidef hRp
  rw [SymplecticGroup.mem_iff', hRt]
  calc R * Matrix.J l ℝ * R = Matrix.J l ℝ * R' * R := by
        rw [hR']; simp only [← Matrix.mul_assoc, J_mul_transpose_J, Matrix.one_mul]
    _ = Matrix.J l ℝ := by
        rw [hkey, Matrix.mul_assoc, Matrix.nonsing_inv_mul R (Ne.isUnit hdet), Matrix.mul_one]

/-- The polynomial identity behind the symplectic Cayley path. -/
theorem pencil_J {R : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hRJR : R * Matrix.J l ℝ * R = Matrix.J l ℝ) (a b : ℝ) :
    (a • R + b • 1) * Matrix.J l ℝ * (a • R + b • 1)
      = (b • R + a • 1) * Matrix.J l ℝ * (b • R + a • 1) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]
  rw [hRJR]
  module

/-- The Cayley path from `Id` to a positive symplectic matrix `R`. -/
noncomputable def posPath (R : Matrix (l ⊕ l) (l ⊕ l) ℝ) (s : ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ :=
  ((1 + s) • R + (1 - s) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ)) *
    ((1 - s) • R + (1 + s) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ))⁻¹

omit [Fintype l] in
theorem posDef_posPath_den {R : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hR : R.PosSemidef) {s : ℝ}
    (hs : s ∈ unitInterval) :
    ((1 - s) • R + (1 + s) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ)).PosDef :=
  Matrix.PosDef.posSemidef_add (hR.smul (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s))
    (Matrix.PosDef.one.smul (by linarith [hs.1] : (0 : ℝ) < 1 + s))

theorem posPath_zero {R : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hR : R.PosSemidef) : posPath R 0 = 1 := by
  have hd := (posDef_posPath_den hR (s := 0) ⟨le_rfl, zero_le_one⟩).det_pos.ne'
  unfold posPath
  simp only [add_zero, sub_zero, one_smul] at hd ⊢
  exact Matrix.mul_nonsing_inv _ (Ne.isUnit hd)

theorem inv_two_smul_one {m : Type*} [Fintype m] [DecidableEq m] :
    ((2 : ℝ) • (1 : Matrix m m ℝ))⁻¹ = (2 : ℝ)⁻¹ • 1 := by
  apply Matrix.inv_eq_left_inv
  rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem posPath_one (R : Matrix (l ⊕ l) (l ⊕ l) ℝ) : posPath R 1 = R := by
  unfold posPath
  rw [show (1 : ℝ) + 1 = 2 by norm_num, sub_self, zero_smul, zero_smul, add_zero, zero_add,
    inv_two_smul_one, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ two_ne_zero,
    one_smul]

theorem posPath_mem {R : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hR : R.PosSemidef)
    (hRJR : R * Matrix.J l ℝ * R = Matrix.J l ℝ) {s : ℝ} (hs : s ∈ unitInterval) :
    posPath R s ∈ Matrix.symplecticGroup l ℝ := by
  have hQ := posDef_posPath_den hR hs
  have hRt : Rᵀ = R := transpose_eq_of_posSemidef hR
  unfold posPath
  set P := (1 + s) • R + (1 - s) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) with hP
  set Q := (1 - s) • R + (1 + s) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) with hQdef
  have hQu : IsUnit Q.det := Ne.isUnit hQ.det_pos.ne'
  have hPt : Pᵀ = P := by
    rw [hP, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, hRt,
      Matrix.transpose_one]
  have hQt : Qᵀ = Q := by
    rw [hQdef, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, hRt,
      Matrix.transpose_one]
  have hPJP : P * Matrix.J l ℝ * P = Q * Matrix.J l ℝ * Q := pencil_J hRJR _ _
  rw [SymplecticGroup.mem_iff', Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hQt, hPt]
  calc Q⁻¹ * P * Matrix.J l ℝ * (P * Q⁻¹) = Q⁻¹ * (P * Matrix.J l ℝ * P) * Q⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = Q⁻¹ * Q * Matrix.J l ℝ * (Q * Q⁻¹) := by rw [hPJP]; simp only [Matrix.mul_assoc]
    _ = Matrix.J l ℝ := by
        rw [Matrix.nonsing_inv_mul Q hQu, Matrix.mul_nonsing_inv Q hQu, Matrix.one_mul,
          Matrix.mul_one]

theorem continuousOn_posPath {R : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hR : R.PosSemidef) :
    ContinuousOn (posPath R) unitInterval := by
  have hP : Continuous fun s : ℝ => (1 + s) • R + (1 - s) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) := by
    fun_prop
  have hQ : Continuous fun s : ℝ => (1 - s) • R + (1 + s) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) := by
    fun_prop
  exact hP.continuousOn.mul (continuousOn_inv_of_det_ne_zero hQ.continuousOn
    fun s hs => (posDef_posPath_den hR hs).det_pos.ne')

end Polar

/-! ## `U(n)` is path-connected -/

section Unitary

variable {l : Type*} [DecidableEq l] [Fintype l]

omit [DecidableEq l] in
theorem re_star_dotProduct_self_pos {v : l → ℂ} (hv : v ≠ 0) : 0 < (star v ⬝ᵥ v).re := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hterm : ∀ z : ℂ, (star z * z).re = Complex.normSq z := by
    intro z
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  rw [dotProduct, Complex.re_sum]
  simp only [Pi.star_apply, hterm]
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
    (Finset.single_le_sum (f := fun j => Complex.normSq (v j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))

omit [DecidableEq l] in
theorem star_dotProduct_smul_self (c : ℂ) (x : l → ℂ) :
    star (c • x) ⬝ᵥ (c • x) = (star c * c) * (star x ⬝ᵥ x) := by
  rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem star_dotProduct_mulVec_unitary {W : Matrix l l ℂ} (hW : star W * W = 1) (v : l → ℂ) :
    star (W *ᵥ v) ⬝ᵥ (W *ᵥ v) = star v ⬝ᵥ v := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.star_eq_conjTranspose, hW, Matrix.one_mulVec]

/-- `αW + β` is invertible for `W` unitary and `α² ≠ β²`. -/
theorem det_smul_add_ne_zero {W : Matrix l l ℂ} (hW : star W * W = 1) {α β : ℝ}
    (hab : α ^ 2 ≠ β ^ 2) : ((α : ℂ) • W + (β : ℂ) • (1 : Matrix l l ℂ)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hWv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    add_eq_zero_iff_eq_neg] at hWv
  have hWW := star_dotProduct_mulVec_unitary hW v
  have key := congrArg (fun x => star x ⬝ᵥ x) hWv
  simp only [star_neg, neg_dotProduct, dotProduct_neg, neg_neg, star_dotProduct_smul_self,
    hWW] at key
  have hre := re_star_dotProduct_self_pos hv
  have hne : star (α : ℂ) * α ≠ star (β : ℂ) * β := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    intro h'
    apply hab
    have h'' : ((α * α : ℝ) : ℂ) = ((β * β : ℝ) : ℂ) := by push_cast; exact h'
    have := Complex.ofReal_injective h''
    rw [sq, sq]; exact this
  have hsub : (star (α : ℂ) * α - star (β : ℂ) * β) * (star v ⬝ᵥ v) = 0 := by
    rw [sub_mul, key, sub_self]
  rcases mul_eq_zero.mp hsub with h1 | h1
  · exact hne (sub_eq_zero.mp h1)
  · rw [h1, Complex.zero_re] at hre
    exact lt_irrefl _ hre

/-- The polynomial identity behind the unitary Cayley path. -/
theorem pencil_unitary {W : Matrix l l ℂ} (hW : star W * W = 1) (a b : ℝ) :
    star ((a : ℂ) • W + (b : ℂ) • 1) * ((a : ℂ) • W + (b : ℂ) • 1)
      = star ((b : ℂ) • W + (a : ℂ) • 1) * ((b : ℂ) • W + (a : ℂ) • 1) := by
  simp only [star_add, star_smul, star_one, Complex.star_def, Complex.conj_ofReal, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hW]
  module

/-- The Cayley path from `Id` to a unitary matrix `W` without the eigenvalue `−1`. -/
noncomputable def uPath (W : Matrix l l ℂ) (s : ℝ) : Matrix l l ℂ :=
  (((1 + s : ℝ) : ℂ) • W + ((1 - s : ℝ) : ℂ) • (1 : Matrix l l ℂ)) *
    (((1 - s : ℝ) : ℂ) • W + ((1 + s : ℝ) : ℂ) • (1 : Matrix l l ℂ))⁻¹

theorem uPath_den_ne {W : Matrix l l ℂ} (hW : star W * W = 1) (h1 : (W + 1).det ≠ 0) {s : ℝ}
    (hs : s ∈ unitInterval) :
    (((1 - s : ℝ) : ℂ) • W + ((1 + s : ℝ) : ℂ) • (1 : Matrix l l ℂ)).det ≠ 0 := by
  rcases eq_or_lt_of_le hs.1 with h0 | hpos
  · subst h0
    simpa using h1
  · refine det_smul_add_ne_zero hW ?_
    intro h
    nlinarith

theorem uPath_zero {W : Matrix l l ℂ} (h1 : (W + 1).det ≠ 0) : uPath W 0 = 1 := by
  unfold uPath
  simp only [add_zero, sub_zero, Complex.ofReal_one, one_smul]
  exact Matrix.mul_nonsing_inv _ (Ne.isUnit h1)

theorem uPath_one (W : Matrix l l ℂ) : uPath W 1 = W := by
  have h2 : (((2 : ℝ) : ℂ) • (1 : Matrix l l ℂ))⁻¹ = ((2 : ℝ) : ℂ)⁻¹ • 1 := by
    apply Matrix.inv_eq_left_inv
    rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ (by norm_num), one_smul]
  unfold uPath
  rw [show (1 : ℝ) + 1 = 2 by norm_num, sub_self, Complex.ofReal_zero, zero_smul, zero_smul,
    add_zero, zero_add, h2, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ (by norm_num), one_smul]

theorem uPath_mem {W : Matrix l l ℂ} (hW : star W * W = 1) (h1 : (W + 1).det ≠ 0) {s : ℝ}
    (hs : s ∈ unitInterval) : uPath W s ∈ Matrix.unitaryGroup l ℂ := by
  have hQ := uPath_den_ne hW h1 hs
  rw [Matrix.mem_unitaryGroup_iff']
  unfold uPath
  set P := ((1 + s : ℝ) : ℂ) • W + ((1 - s : ℝ) : ℂ) • (1 : Matrix l l ℂ) with hP
  set Q := ((1 - s : ℝ) : ℂ) • W + ((1 + s : ℝ) : ℂ) • (1 : Matrix l l ℂ) with hQdef
  have hQu : IsUnit Q.det := Ne.isUnit hQ
  have hQs : IsUnit (star Q).det := by
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]; exact hQu.star
  have hPP : star P * P = star Q * Q := pencil_unitary hW _ _
  have hsi : star Q⁻¹ = (star Q)⁻¹ := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv]
  rw [star_mul, hsi]
  calc (star Q)⁻¹ * star P * (P * Q⁻¹) = (star Q)⁻¹ * (star P * P) * Q⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (star Q)⁻¹ * star Q * (Q * Q⁻¹) := by rw [hPP]; simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Matrix.nonsing_inv_mul _ hQs, Matrix.mul_nonsing_inv _ hQu, Matrix.one_mul]

theorem continuousOn_uPath {W : Matrix l l ℂ} (hW : star W * W = 1) (h1 : (W + 1).det ≠ 0) :
    ContinuousOn (uPath W) unitInterval := by
  have hc : Continuous fun s : ℝ => ((s : ℝ) : ℂ) := Complex.continuous_ofReal
  have hP : Continuous fun s : ℝ =>
      ((1 + s : ℝ) : ℂ) • W + ((1 - s : ℝ) : ℂ) • (1 : Matrix l l ℂ) := by
    refine ((Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).smul
      continuous_const).add ((Complex.continuous_ofReal.comp
      (continuous_const.sub continuous_id)).smul continuous_const)
  have hQ : Continuous fun s : ℝ =>
      ((1 - s : ℝ) : ℂ) • W + ((1 + s : ℝ) : ℂ) • (1 : Matrix l l ℂ) := by
    refine ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).smul
      continuous_const).add ((Complex.continuous_ofReal.comp
      (continuous_const.add continuous_id)).smul continuous_const)
  exact hP.continuousOn.mul (continuousOn_inv_of_det_ne_zero hQ.continuousOn
    fun s hs => uPath_den_ne hW h1 hs)

theorem smul_mem_unitaryGroup {V : Matrix l l ℂ} (hV : star V * V = 1) (θ : ℝ) :
    star (Complex.exp (θ * I) • V) * (Complex.exp (θ * I) • V) = 1 := by
  rw [star_smul, smul_mul_smul_comm, hV, Complex.star_def, mul_comm, exp_mul_conj_exp, one_smul]

/-- A rotation `V ↦ e^{iθ}V` removes the eigenvalue `−1`. -/
theorem exists_det_exp_smul_add_one_ne_zero (V : Matrix l l ℂ) :
    ∃ θ : ℝ, (Complex.exp (θ * I) • V + 1).det ≠ 0 := by
  set S : Set ℂ := {z | z ∈ V.charpoly.roots}
  have hS : S.Finite := V.charpoly.roots.toFinset.finite_toSet.subset
    (fun z hz => Multiset.mem_toFinset.mpr hz)
  set f : ℝ → ℂ := fun θ => -(Complex.exp (θ * I))⁻¹
  have hbad : ∀ θ : ℝ, (Complex.exp (θ * I) • V + 1).det = 0 → f θ ∈ S := by
    intro θ h
    set c := Complex.exp (θ * I)
    have hc : c ≠ 0 := Complex.exp_ne_zero _
    have key : c • V + 1 = (-c) • (Matrix.scalar l (-c⁻¹) - V) := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_sub, smul_smul,
        neg_mul_neg, mul_inv_cancel₀ hc, one_smul, neg_smul, sub_neg_eq_add, add_comm]
    rw [key, Matrix.det_smul] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (pow_eq_zero_iff'.mp h').1 (neg_ne_zero.mpr hc)
    · show -(c)⁻¹ ∈ V.charpoly.roots
      rw [Polynomial.mem_roots (Matrix.charpoly_monic V).ne_zero, Polynomial.IsRoot,
        Matrix.eval_charpoly]
      exact h'
  have hinj : Set.InjOn f (Set.Icc 0 1) := by
    intro θ₁ h₁ θ₂ h₂ h
    simp only [f, neg_inj, inv_inj] at h
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    have him := congrArg Complex.im hk
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat] at him
    have hpi := Real.pi_gt_three
    rcases lt_trichotomy k 0 with hk0 | rfl | hk0
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
    · simp at him; linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
  have hfin : (Set.Icc (0 : ℝ) 1 ∩ f ⁻¹' S).Finite :=
    Set.Finite.of_finite_image (hS.subset (by rintro _ ⟨x, hx, rfl⟩; exact hx.2))
      (hinj.mono Set.inter_subset_left)
  obtain ⟨θ, hθ, hθS⟩ := ((Set.Icc_infinite (zero_lt_one' ℝ)).sdiff hfin).nonempty
  refine ⟨θ, fun h => hθS ⟨hθ, hbad θ h⟩⟩

end Unitary

/-! ## `Sp(2n)` is path-connected -/

section Connected

variable {l : Type*} [DecidableEq l] [Fintype l]

omit [DecidableEq l] [Fintype l] in
theorem realForm_injective : Function.Injective (realForm : Matrix l l ℂ → _) := by
  intro M N h
  obtain ⟨h1, -, h3, -⟩ := Matrix.fromBlocks_inj.mp h
  ext i j
  exact Complex.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h3 i) j)

/-- A real matrix commuting with `J` is the real form of a complex matrix. -/
theorem eq_realForm_of_commute {U : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hU : U * Matrix.J l ℝ = Matrix.J l ℝ * U) :
    U = realForm (U.toBlocks₁₁.map (fun x : ℝ => (x : ℂ)) +
      I • U.toBlocks₂₁.map (fun x : ℝ => (x : ℂ))) := by
  have hJ : Matrix.J l ℝ = Matrix.fromBlocks 0 (-1) 1 0 := rfl
  have hU' := hU
  rw [← Matrix.fromBlocks_toBlocks U, hJ, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hU'
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, zero_add, add_zero] at hU'
  obtain ⟨h11, h12, -, -⟩ := Matrix.fromBlocks_inj.mp hU'
  have hre : (U.toBlocks₁₁.map (fun x : ℝ => (x : ℂ)) +
      I • U.toBlocks₂₁.map (fun x : ℝ => (x : ℂ))).map Complex.re = U.toBlocks₁₁ := by
    ext i j; simp
  have him : (U.toBlocks₁₁.map (fun x : ℝ => (x : ℂ)) +
      I • U.toBlocks₂₁.map (fun x : ℝ => (x : ℂ))).map Complex.im = U.toBlocks₂₁ := by
    ext i j; simp
  rw [realForm, hre, him]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks U]
  refine Matrix.fromBlocks_inj.mpr ⟨rfl, ?_, rfl, ?_⟩
  · rw [h11]
  · exact (neg_inj.mp h12).symm

/-- **Proposition 5.6.9** (path-connectedness half).  Every symplectic matrix is
joined to the identity inside `Sp(2n)`. -/
theorem joinedIn_one_of_mem_symplecticGroup {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    JoinedIn (Matrix.symplecticGroup l ℝ : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ)) 1 A := by
  set Sp := (Matrix.symplecticGroup l ℝ : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ))
  -- the positive part
  set Q := Aᵀ * A with hQdef
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr
    (Ne.isUnit (det_ne_zero_of_mem_symplecticGroup hA))
  have hQpos : Q.PosDef := by
    have := Matrix.PosDef.conjTranspose_mul_self A (Matrix.mulVec_injective_iff_isUnit.mpr hAu)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hQ : Q ∈ Matrix.symplecticGroup l ℝ :=
    Submonoid.mul_mem _ (SymplecticGroup.transpose_mem hA) hA
  obtain ⟨hRR, hRp, hRdet, hRmem⟩ := sqrt_mem_symplecticGroup hQ hQpos
  set R := CFC.sqrt Q
  have hRt : Rᵀ = R := transpose_eq_of_posSemidef hRp
  have hRJR : R * Matrix.J l ℝ * R = Matrix.J l ℝ := by
    have := SymplecticGroup.mem_iff'.mp hRmem; rwa [hRt] at this
  -- `A` is joined to `U = A R⁻¹`
  set U := A * R⁻¹
  have hRinv : R⁻¹ ∈ Matrix.symplecticGroup l ℝ := Chapter5.inv_mem_symplecticGroup hRmem
  have hUmem : U ∈ Matrix.symplecticGroup l ℝ := Submonoid.mul_mem _ hA hRinv
  have hAU : JoinedIn Sp A U := by
    refine joinedIn_of_line (fun s => A * (posPath R s)⁻¹) ?_ ?_ ?_ ?_
    · exact continuousOn_const.mul (continuousOn_inv_of_det_ne_zero (continuousOn_posPath hRp)
        fun s hs => det_ne_zero_of_mem_symplecticGroup (posPath_mem hRp hRJR hs))
    · simp only [posPath_zero hRp, inv_one, Matrix.mul_one]
    · show A * (posPath R 1)⁻¹ = U
      rw [posPath_one]
    · intro s hs
      exact Submonoid.mul_mem _ hA
        (Chapter5.inv_mem_symplecticGroup (posPath_mem hRp hRJR hs))
  -- `U` is orthogonal, hence the real form of a unitary matrix
  have hUo : Uᵀ * U = 1 := by
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hRt]
    calc R⁻¹ * Aᵀ * (A * R⁻¹) = R⁻¹ * (R * R) * R⁻¹ := by
          rw [hRR, hQdef]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul R (Ne.isUnit hRdet), Matrix.one_mul,
            Matrix.mul_nonsing_inv R (Ne.isUnit hRdet)]
  have hUc : U * Matrix.J l ℝ = Matrix.J l ℝ * U :=
    Chapter5.complexLinear_of_symplectic_of_orthogonal hUmem hUo
  set V := U.toBlocks₁₁.map (fun x : ℝ => (x : ℂ)) + I • U.toBlocks₂₁.map (fun x : ℝ => (x : ℂ))
  have hUV : U = realForm V := eq_realForm_of_commute hUc
  have hV : star V * V = 1 := by
    apply realForm_injective
    rw [realForm_mul, realForm_one, Matrix.star_eq_conjTranspose, ← realForm_transpose, ← hUV,
      hUo]
  -- rotate away the eigenvalue `−1`, then contract along the unitary Cayley path
  obtain ⟨θ, hθ⟩ := exists_det_exp_smul_add_one_ne_zero V
  set W := Complex.exp (θ * I) • V
  have hW : star W * W = 1 := smul_mem_unitaryGroup hV θ
  have h1W : JoinedIn Sp 1 (realForm W) := by
    refine joinedIn_of_line (fun s => realForm (uPath W s)) ?_ ?_ ?_ ?_
    · exact continuous_realForm.comp_continuousOn (continuousOn_uPath hW hθ)
    · simp only [uPath_zero hθ, realForm_one]
    · simp only [uPath_one]
    · intro s hs
      exact realForm_mem_symplecticGroup (uPath_mem hW hθ hs)
  have hWV : JoinedIn Sp (realForm W) (realForm V) := by
    refine joinedIn_of_line (fun s => realForm (Complex.exp (((1 - s) * θ : ℝ) * I) • V))
      ?_ ?_ ?_ ?_
    · refine (continuous_realForm.comp ?_).continuousOn
      exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        ((continuous_const.sub continuous_id).mul continuous_const)).mul continuous_const)).smul
        continuous_const
    · simp only [sub_zero, one_mul]; rfl
    · simp only [sub_self, zero_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    · intro s _
      exact realForm_mem_symplecticGroup
        (Matrix.mem_unitaryGroup_iff'.mpr (smul_mem_unitaryGroup hV _))
  rw [hUV] at hAU
  exact (h1W.trans hWV).trans hAU.symm

theorem isPathConnected_symplecticGroup :
    IsPathConnected (Matrix.symplecticGroup l ℝ : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ)) :=
  ⟨1, Submonoid.one_mem _, fun _ hA => joinedIn_one_of_mem_symplecticGroup hA⟩

/-- Conjugating by a symplectic matrix stays in the path component in `Sp(2n)⋆`. -/
theorem joinedIn_conj {X T : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ symplecticStar l)
    (hT : T ∈ Matrix.symplecticGroup l ℝ) :
    JoinedIn (symplecticStar l) X (T * X * T⁻¹) := by
  obtain ⟨γ, hγ⟩ := joinedIn_one_of_mem_symplecticGroup hT
  have hmem : ∀ s ∈ unitInterval, γ.extend s ∈ Matrix.symplecticGroup l ℝ := by
    intro s hs
    rw [show γ.extend s = γ ⟨s, hs⟩ from Path.extend_extends' γ ⟨s, hs⟩]
    exact hγ _
  refine joinedIn_of_line (fun s => γ.extend s * X * (γ.extend s)⁻¹) ?_ ?_ ?_ ?_
  · exact (γ.continuous_extend.continuousOn.mul continuousOn_const).mul
      (continuousOn_inv_of_det_ne_zero γ.continuous_extend.continuousOn
        fun s hs => det_ne_zero_of_mem_symplecticGroup (hmem s hs))
  · simp only [Path.extend_zero, Matrix.one_mul, inv_one, Matrix.mul_one]
  · simp only [Path.extend_one]
  · intro s hs
    have hg := hmem s hs
    have hgu : IsUnit (γ.extend s) := (Matrix.isUnit_iff_isUnit_det _).mpr
      (Ne.isUnit (det_ne_zero_of_mem_symplecticGroup hg))
    refine ⟨Submonoid.mul_mem _ (Submonoid.mul_mem _ hg hX.1)
      (Chapter5.inv_mem_symplecticGroup hg), ?_⟩
    have : γ.extend s * X * (γ.extend s)⁻¹ - 1 = γ.extend s * (X - 1) * (γ.extend s)⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hgu)]
    rw [this, Matrix.det_conj hgu]
    exact hX.2

end Connected

end Chapter7
end MorseFloer
