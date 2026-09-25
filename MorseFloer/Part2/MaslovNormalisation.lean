import MorseFloer.Part2.MaslovIndex

/-!
# The normalisation of the Maslov index (Proposition 7.2.1)

`μ(exp(tJS)) = Ind(S) - n` for a symmetric invertible `S` whose eigenvalues are smaller than
`2π` in absolute value.

* `maslovIndex_expPath_eq_of_path`: along a continuous path of such matrices the index of
  `exp(tJS)` does not change (homotopy invariance).
* `maslovIndex_expPath_smul_one`: the rotations. For `c · Id` the path is the real form of
  `e^{itc} · Id`, on which `ρ = det`; at `c = ± π` it ends at `-Id`, where `ρ̃ = nπ`, and a
  path of scalars reaches every `c` of the same sign.
-/

open Matrix Topology

namespace MorseFloer
namespace MaslovIndex

open Chapter7 Rho SymplecticEigen

variable {n : ℕ}

/-! ### Paths of symmetric matrices -/

section Path

/-- The admissible hypotheses on `S` for the path `exp(tJS)`. -/
structure IsSmallSymm (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) : Prop where
  symm : Sᵀ = S
  det_ne : S.det ≠ 0
  bound : ∀ c : ℝ, (S - c • 1).det = 0 → |c| < 2 * Real.pi

set_option backward.isDefEq.respectTransparency false in
theorem continuous_expPath_uncurry {P : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hP : Continuous P) : Continuous fun p : ℝ × ℝ => expPath (P p.1) p.2 := by
  simp only [expPath_apply]
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous.comp
    (continuous_snd.smul (continuous_const.mul (hP.comp continuous_fst)))

/-- **The index of `exp(tJS)` is constant along a path of admissible `S`.** -/
theorem maslovIndex_expPath_eq_of_path {P : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hP : Continuous P) (hS : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsSmallSymm (P s)) :
    maslovIndex n (expPath (P 0)) = maslovIndex n (expPath (P 1)) := by
  -- clamp the parameter to `[0, 1]`
  set σ : ℝ → ℝ := fun s => max 0 (min s 1)
  have hσ : Continuous σ := by fun_prop
  have hσI : ∀ s, σ s ∈ Set.Icc (0 : ℝ) 1 := fun s =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have h0 : σ 0 = 0 := by simp [σ]
  have h1 : σ 1 = 1 := by simp [σ]
  have := maslovIndex_eq_of_homotopicInS (n := n) ⟨fun s => expPath (P (σ s)),
    continuous_expPath_uncurry (hP.comp hσ), fun s => isAdmissiblePath_expPath
      (hS _ (hσI s)).symm (hS _ (hσI s)).det_ne (hS _ (hσI s)).bound, rfl, rfl⟩
  simpa only [h0, h1] using this

end Path

/-! ### The rotations -/

section Rotation

theorem realForm_eq_fromBlocks (M : Matrix (Fin n) (Fin n) ℂ) :
    realForm M = Matrix.fromBlocks (M.map Complex.re) (-(M.map Complex.im)) (M.map Complex.im)
      (M.map Complex.re) := rfl

/-- On the real form of `z · Id`, `|z| = 1`, the map `ρ` is `det(z · Id) = z ^ n`. -/
theorem rho_realForm_smul_one {z : ℂ} (hz : ‖z‖ = 1) :
    rho n (realForm (z • (1 : Matrix (Fin n) (Fin n) ℂ))) = z ^ n := by
  have hO : Chapter5.IsOrthogonalMat (realForm (z • (1 : Matrix (Fin n) (Fin n) ℂ))) := by
    rw [Chapter5.IsOrthogonalMat, realForm_transpose, ← realForm_mul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, smul_one_mul, smul_smul, ← realForm_one]
    congr 1
    rw [show star z * z = 1 by
      rw [RCLike.star_def, Complex.conj_mul', hz]; norm_num, one_smul]
  rw [realForm_eq_fromBlocks] at hO ⊢
  rw [rho_det_unitary n _ _ hO]
  have : ((z • (1 : Matrix (Fin n) (Fin n) ℂ)).map Complex.re).map (fun r : ℝ => (r : ℂ)) +
      Complex.I • ((z • (1 : Matrix (Fin n) (Fin n) ℂ)).map Complex.im).map
        (fun r : ℝ => (r : ℂ)) = z • 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one, Matrix.add_apply]
      rw [mul_comm, Complex.re_add_im]
    · simp [h]
  rw [this, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

/-- The eigenvalues of `-Id` are all `-1`. -/
theorem roots_neg_one (l : Type*) [DecidableEq l] [Fintype l] :
    (-1 : Matrix l l ℂ).charpoly.roots = Multiset.replicate (Fintype.card l) (-1) := by
  have h : (-1 : Matrix l l ℂ) = Matrix.diagonal fun _ => -1 := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_neg]
  have hf : (fun _ : l => Polynomial.X - Polynomial.C (-1 : ℂ))
      = (fun a : ℂ => Polynomial.X - Polynomial.C a) ∘ (fun _ : l => (-1 : ℂ)) := rfl
  rw [h, Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod, hf, ← Multiset.map_map,
    Polynomial.roots_multiset_prod_X_sub_C, Multiset.map_const', Finset.card_val,
    Finset.card_univ]

/-- **`ρ̃(-Id) = n π`**: `-1` is a real eigenvalue of multiplicity `2n`. -/
theorem rhoLift_neg_one : rhoLift n (-1) = n * Real.pi := by
  classical
  have hcpx : cpx (-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) = -1 := by
    ext i j; by_cases h : i = j <;> simp [cpx, h]
  have hroots := roots_neg_one (Fin n ⊕ Fin n)
  rw [rhoLift, hcpx, ← sum_liftTerm_eq (s := {-1}), Finset.sum_singleton,
    liftTerm_of_real (by simp), hroots, Multiset.count_replicate_self]
  · simp only [Fintype.card_sum, Fintype.card_fin]
    push_cast; ring
  · rw [hroots]
    intro μ hμ
    rw [Multiset.mem_toFinset] at hμ
    exact Finset.mem_singleton.2 (Multiset.eq_of_mem_replicate hμ)

/-- The index of the rotation `exp(t k π J)`, `k = ± 1`: `-k n`. -/
theorem maslovIndex_expPath_rot {k : ℤ} (hk : k = 1 ∨ k = -1) :
    maslovIndex n (expPath (((k : ℝ) * Real.pi) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)))
      = -k * n := by
  have hodd : Odd k := by rcases hk with rfl | rfl <;> decide
  have hψ := isAdmissiblePath_expPath_rot (l := Fin n) hodd
  -- the angle of `ρ` along the rotation is `n t k π`
  have h := (maslovIndex_spec hψ (F := fun t => n * (t * (k * Real.pi)))
    (by fun_prop) (by simp) fun t => by
      rw [expPath_smul_one, rho_realForm_smul_one (by
        rw [Complex.norm_exp_ofReal_mul_I]), ← Complex.exp_nat_mul]
      push_cast; ring_nf).1
  -- the endpoint is `-Id`, where `ρ̃ = n π`
  have hend : expPath (((k : ℝ) * Real.pi) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) 1
      = -1 := by
    rw [expPath_smul_one]
    have : Complex.exp (((1 : ℝ) * ((k : ℝ) * Real.pi) : ℝ) * Complex.I) = -1 := by
      rw [← exp_odd_mul_pi_mul_I hodd]; congr 1; push_cast; ring
    rw [this, neg_one_smul, realForm_neg, realForm_one]
  rw [hend, rhoLift_neg_one] at h
  have h' : ((maslovIndex n (expPath (((k : ℝ) * Real.pi) • 1)) + n : ℤ) : ℝ) =
      ((n - k * n : ℤ) : ℝ) :=
    mul_right_cancel₀ Real.pi_ne_zero (by rw [← h]; push_cast; ring)
  have := Int.cast_injective h'
  linarith

theorem isSmallSymm_smul_one {c : ℝ} (hc0 : c ≠ 0) (hc : |c| < 2 * Real.pi) :
    IsSmallSymm (c • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) :=
  ⟨by rw [Matrix.transpose_smul, Matrix.transpose_one], det_smul_one_ne_zero hc0,
    abs_lt_of_det_smul_one_sub_eq_zero hc⟩

/-- **The rotations.** For `0 < |c| < 2π`, the index of `exp(tJ (c Id))` is `-n` if `c > 0`
and `n` if `c < 0`. -/
theorem maslovIndex_expPath_smul_one {c : ℝ} (hc0 : c ≠ 0) (hc : |c| < 2 * Real.pi) :
    maslovIndex n (expPath (c • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))) =
      if 0 < c then -(n : ℤ) else n := by
  -- move `c` to `± π` along scalars of the same sign
  set k : ℤ := if 0 < c then 1 else -1 with hk
  have hk' : k = 1 ∨ k = -1 := by rw [hk]; split_ifs <;> simp
  have hpath := maslovIndex_expPath_eq_of_path (n := n)
    (P := fun s => ((1 - s) * c + s * (k * Real.pi)) • (1 : Matrix _ _ ℝ))
    (by fun_prop) fun s hs => ?_
  · simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add] at hpath
    rw [hpath, maslovIndex_expPath_rot hk', hk]
    split_ifs <;> simp
  · -- the scalar keeps the sign of `c` and stays below `2π` in absolute value
    obtain ⟨hs0, hs1⟩ := hs
    have hc' := abs_lt.1 hc
    have hπ := Real.pi_pos
    apply isSmallSymm_smul_one
    · rw [hk]
      split_ifs with hpos
      · push_cast; nlinarith
      · have : c < 0 := lt_of_le_of_ne (not_lt.1 hpos) hc0
        push_cast; nlinarith
    · rw [abs_lt, hk]
      split_ifs with hpos
      · push_cast; constructor <;> nlinarith
      · have : c < 0 := lt_of_le_of_ne (not_lt.1 hpos) hc0
        push_cast; constructor <;> nlinarith

end Rotation

/-! ### An eigenvalue bound by the entries, and the normalised matrix -/

section Bound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum of the absolute values of the entries. -/
noncomputable def absSum (A : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, |A i j|

omit [DecidableEq ι] in
theorem absSum_nonneg (A : Matrix ι ι ℝ) : 0 ≤ absSum A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq ι] in
theorem continuous_absSum : Continuous (absSum : Matrix ι ι ℝ → ℝ) := by
  unfold absSum
  fun_prop

/-- A real eigenvalue is bounded by the sum of the absolute values of the entries. -/
theorem abs_le_absSum_of_det {A : Matrix ι ι ℝ} {c : ℝ} (h : (A - c • 1).det = 0) :
    |c| ≤ absSum A := by
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hv
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) ⟨j₀, Finset.mem_univ _⟩
  have hvi : 0 < |v i| := (abs_pos.2 hj₀).trans_le (hi j₀ (Finset.mem_univ _))
  -- the `i`-th coordinate of `A v = c v`
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hAv
  have hrow : ∑ j, A i j * v j = c * v i := by
    have := congrFun hAv i
    simpa [Matrix.mulVec, dotProduct] using this
  have key : |c| * |v i| ≤ absSum A * |v i| := by
    calc |c| * |v i| = |∑ j, A i j * v j| := by rw [hrow, abs_mul]
      _ ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |A i j| * |v i| := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ _)) (abs_nonneg _)
      _ = (∑ j, |A i j|) * |v i| := (Finset.sum_mul _ _ _).symm
      _ ≤ absSum A * |v i| := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := fun i => ∑ j, |A i j|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
          (abs_nonneg _)
  exact le_of_mul_le_mul_right key hvi

theorem det_sub_of_det_smul_sub {A : Matrix ι ι ℝ} {r c : ℝ} (hr : r ≠ 0)
    (h : (r • A - c • 1).det = 0) : (A - (c / r) • 1).det = 0 := by
  have : r • A - c • (1 : Matrix ι ι ℝ) = r • (A - (c / r) • 1) := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ _ hr]
  rw [this, Matrix.det_smul] at h
  exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hr)

/-- The matrix rescaled so that its eigenvalues are smaller than `1`. -/
noncomputable def normalize (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 + absSum A)⁻¹ • A

omit [DecidableEq ι] in
theorem normalize_pos (A : Matrix ι ι ℝ) : 0 < (1 + absSum A)⁻¹ :=
  inv_pos.2 (by linarith [absSum_nonneg A])

omit [DecidableEq ι] in
theorem continuous_normalize : Continuous (normalize : Matrix ι ι ℝ → Matrix ι ι ℝ) :=
  ((continuous_const.add continuous_absSum).inv₀ fun A =>
    ne_of_gt (show (0 : ℝ) < 1 + absSum A by linarith [absSum_nonneg A])).smul continuous_id

end Bound

section Normalize

theorem isSmallSymm_normalize {S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hS : Sᵀ = S)
    (hdet : S.det ≠ 0) : IsSmallSymm (normalize S) := by
  have hr := normalize_pos S
  refine ⟨by rw [normalize, Matrix.transpose_smul, hS], ?_, fun c hc => ?_⟩
  · rw [normalize, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hr.ne') hdet
  · have h := abs_le_absSum_of_det (det_sub_of_det_smul_sub hr.ne' hc)
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr] at h
    have h1 : absSum S * (1 + absSum S)⁻¹ < 1 := by
      rw [← div_eq_mul_inv, div_lt_one (by linarith [absSum_nonneg S])]
      linarith
    linarith [Real.pi_gt_three]

/-- Rescaling `S` by a positive factor does not change the index of `exp(tJS)`. -/
theorem maslovIndex_expPath_normalize {S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hS : IsSmallSymm S) : maslovIndex n (expPath S) = maslovIndex n (expPath (normalize S)) := by
  set r := (1 + absSum S)⁻¹ with hr_def
  have hr := normalize_pos S
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ (by linarith [absSum_nonneg S])
  have h := maslovIndex_expPath_eq_of_path (n := n) (P := fun s => ((1 - s) + s * r) • S)
    (by fun_prop) fun s ⟨hs0, hs1⟩ => by
      have hf : 0 < (1 - s) + s * r := by nlinarith
      have hf1 : (1 - s) + s * r ≤ 1 := by nlinarith
      refine ⟨by rw [Matrix.transpose_smul, hS.symm], ?_, fun c hc => ?_⟩
      · rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hf.ne') hS.det_ne
      · have h := abs_lt.1 (hS.bound _ (det_sub_of_det_smul_sub hf.ne' hc))
        rw [lt_div_iff₀ hf, div_lt_iff₀ hf] at h
        rw [abs_lt]
        have hπ := Real.pi_pos
        constructor <;> nlinarith [h.1, h.2]
  simpa [normalize, ← hr_def] using h

theorem maslovIndex_expPath_of_normalize {S S' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hS : IsSmallSymm S) (hS' : IsSmallSymm S')
    (h : maslovIndex n (expPath (normalize S)) = maslovIndex n (expPath (normalize S'))) :
    maslovIndex n (expPath S) = maslovIndex n (expPath S') := by
  rw [maslovIndex_expPath_normalize hS, maslovIndex_expPath_normalize hS', h]

/-- **Congruence paths.** Along `s ↦ (L s)ᵀ D(s) L(s)`, with `L s` invertible and `D s`
symmetric invertible, the index of the path of the normalised matrices does not change. -/
theorem maslovIndex_congr_path {L D : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hL : Continuous L) (hD : Continuous D)
    (hLdet : ∀ s ∈ Set.Icc (0 : ℝ) 1, (L s).det ≠ 0)
    (hDs : ∀ s ∈ Set.Icc (0 : ℝ) 1, (D s)ᵀ = D s)
    (hDdet : ∀ s ∈ Set.Icc (0 : ℝ) 1, (D s).det ≠ 0) :
    maslovIndex n (expPath (normalize ((L 0)ᵀ * D 0 * L 0))) =
      maslovIndex n (expPath (normalize ((L 1)ᵀ * D 1 * L 1))) :=
  maslovIndex_expPath_eq_of_path (P := fun s => normalize ((L s)ᵀ * D s * L s))
    (continuous_normalize.comp ((hL.matrix_transpose.mul hD).mul hL)) fun s hs =>
      isSmallSymm_normalize
        (by rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hDs s hs,
          Matrix.mul_assoc])
        (by rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
            exact mul_ne_zero (mul_ne_zero (hLdet s hs) (hDdet s hs)) (hLdet s hs))

end Normalize

/-! ### Paths in the general linear group -/

section GenLin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A convex combination of two numbers of the same sign is not zero. -/
theorem convex_ne_zero {a b s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h : 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0) : (1 - s) * a + s * b ≠ 0 := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have := lt_min ha hb
    nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 (min_le_left a b)),
      mul_nonneg hs0 (sub_nonneg.2 (min_le_right a b))]
  · have := max_lt ha hb
    nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 (le_max_left a b)),
      mul_nonneg hs0 (sub_nonneg.2 (le_max_right a b))]

/-- A transvection with its coefficient scaled by `1 - s`. -/
def scaleT (s : ℝ) (t : Matrix.TransvectionStruct ι ℝ) : Matrix.TransvectionStruct ι ℝ :=
  ⟨t.i, t.j, t.hij, (1 - s) * t.c⟩

theorem continuous_transvection_prod (T : List (Matrix.TransvectionStruct ι ℝ)) :
    Continuous fun s => ((T.map (scaleT s)).map Matrix.TransvectionStruct.toMatrix).prod := by
  simp only [List.map_map]
  refine continuous_list_prod T fun t _ => ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Function.comp_apply, scaleT, Matrix.TransvectionStruct.toMatrix_mk,
    Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
  split_ifs <;> fun_prop

theorem transvection_prod_zero (T : List (Matrix.TransvectionStruct ι ℝ)) :
    ((T.map (scaleT 0)).map Matrix.TransvectionStruct.toMatrix).prod =
      (T.map Matrix.TransvectionStruct.toMatrix).prod := by
  have h : T.map (scaleT 0) = T := by
    conv_rhs => rw [← List.map_id T]
    exact List.map_congr_left fun t _ => by cases t; simp [scaleT]
  rw [h]

theorem transvection_prod_one (T : List (Matrix.TransvectionStruct ι ℝ)) :
    ((T.map (scaleT 1)).map Matrix.TransvectionStruct.toMatrix).prod = 1 := by
  simp [scaleT, List.map_map, Function.comp_def]

/-- **Every invertible matrix is joined, through invertible matrices, to a diagonal matrix
with entries `± 1`**: write it as transvections times a diagonal matrix times transvections
and shrink the transvections to the identity and the diagonal entries to their signs. -/
theorem exists_path_to_sign {M : Matrix ι ι ℝ} (hM : M.det ≠ 0) :
    ∃ L : ℝ → Matrix ι ι ℝ, Continuous L ∧ L 0 = M ∧ (∀ s ∈ Set.Icc (0 : ℝ) 1, (L s).det ≠ 0) ∧
      ∃ σ : ι → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧ L 1 = Matrix.diagonal σ := by
  obtain ⟨T, T', D, hMD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hD : ∀ i, D i ≠ 0 := by
    rw [hMD, Matrix.det_mul, Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod,
      Matrix.TransvectionStruct.det_toMatrix_prod, Matrix.det_diagonal, one_mul, mul_one] at hM
    exact fun i => Finset.prod_ne_zero_iff.1 hM i (Finset.mem_univ _)
  set σ : ι → ℝ := fun i => if 0 < D i then 1 else -1
  refine ⟨fun s => ((T.map (scaleT s)).map Matrix.TransvectionStruct.toMatrix).prod *
      Matrix.diagonal (fun i => (1 - s) * D i + s * σ i) *
      ((T'.map (scaleT s)).map Matrix.TransvectionStruct.toMatrix).prod, ?_, ?_, ?_,
      σ, fun i => by simp only [σ]; split_ifs <;> simp, ?_⟩
  · refine ((continuous_transvection_prod T).mul ?_).mul (continuous_transvection_prod T')
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.diagonal_apply]
    split_ifs <;> fun_prop
  · simp only [transvection_prod_zero, sub_zero, one_mul, zero_mul, add_zero]
    exact hMD.symm
  · intro s ⟨hs0, hs1⟩
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod,
      Matrix.TransvectionStruct.det_toMatrix_prod, Matrix.det_diagonal, one_mul, mul_one]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    simp only [σ]
    split_ifs with h
    · exact convex_ne_zero hs0 hs1 (.inl ⟨h, one_pos⟩)
    · exact convex_ne_zero hs0 hs1 (.inr ⟨lt_of_le_of_ne (not_lt.1 h) (hD i), by norm_num⟩)
  · simp only [transvection_prod_one, sub_self, zero_mul, one_mul, zero_add, Matrix.mul_one]

omit [DecidableEq ι] in
/-- Two vectors of signs with the same number of `-1` differ by a permutation. -/
theorem exists_perm_of_card_neg {σ σ' : ι → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (hσ' : ∀ i, σ' i = 1 ∨ σ' i = -1)
    (hcard : (Finset.univ.filter fun i => σ i < 0).card =
      (Finset.univ.filter fun i => σ' i < 0).card) :
    ∃ e : Equiv.Perm ι, ∀ i, σ' i = σ (e i) := by
  have h₁ : Fintype.card {i // σ' i < 0} = Fintype.card {i // σ i < 0} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, hcard]
  have h₂ : Fintype.card {i // ¬ σ' i < 0} = Fintype.card {i // ¬ σ i < 0} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h₁]
  let e₁ := Fintype.equivOfCardEq h₁
  let e₂ := Fintype.equivOfCardEq h₂
  refine ⟨(Equiv.sumCompl fun i => σ' i < 0).symm.trans
    ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl fun i => σ i < 0)), fun i => ?_⟩
  have neg : ∀ {x : ℝ}, (x = 1 ∨ x = -1) → x < 0 → x = -1 := fun h hx => by
    rcases h with h | h <;> [linarith; exact h]
  have pos : ∀ {x : ℝ}, (x = 1 ∨ x = -1) → ¬ x < 0 → x = 1 := fun h hx => by
    rcases h with h | h <;> [exact h; (rw [h] at hx; norm_num at hx)]
  by_cases hi : σ' i < 0
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun i => σ' i < 0) hi,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl,
      neg (hσ' i) hi, neg (hσ _) (e₁ ⟨i, hi⟩).2]
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun i => σ' i < 0) hi,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr,
      pos (hσ' i) hi, pos (hσ _) (e₂ ⟨i, hi⟩).2]

/-- Conjugating a diagonal matrix by a permutation matrix permutes its entries. -/
theorem permMatrix_transpose_mul_diagonal_mul (e : Equiv.Perm ι) (σ : ι → ℝ) :
    ((1 : Matrix ι ι ℝ).submatrix id e)ᵀ * Matrix.diagonal σ * (1 : Matrix ι ι ℝ).submatrix id e
      = Matrix.diagonal (σ ∘ e) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
    Matrix.one_apply, Matrix.diagonal_apply, Function.comp_apply]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h, e.injective.eq_iff]

end GenLin

/-! ### Reduction to a diagonal matrix of signs -/

section Reduction

/-- A diagonal matrix of signs is admissible. -/
theorem isSmallSymm_sign {σ : Fin n ⊕ Fin n → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    IsSmallSymm (Matrix.diagonal σ) := by
  refine ⟨Matrix.diagonal_transpose _, ?_, fun c hc => ?_⟩
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by rcases hσ i with h | h <;> rw [h] <;> norm_num
  · -- a diagonal matrix of signs has the eigenvalues `± 1`
    have hd : Matrix.diagonal σ - c • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
        Matrix.diagonal fun i => σ i - c := by
      ext i j; by_cases h : i = j <;> simp [h]
    rw [hd, Matrix.det_diagonal] at hc
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hc
    rw [← sub_eq_zero.1 hi]
    have := Real.pi_gt_three
    rcases hσ i with h' | h' <;> rw [h'] <;> norm_num <;> linarith

/-- Two diagonal matrices of signs with the same number of `-1` give the same index. -/
theorem maslovIndex_expPath_sign_eq {σ σ' : Fin n ⊕ Fin n → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (hσ' : ∀ i, σ' i = 1 ∨ σ' i = -1)
    (hcard : (Finset.univ.filter fun i => σ i < 0).card =
      (Finset.univ.filter fun i => σ' i < 0).card) :
    maslovIndex n (expPath (Matrix.diagonal σ')) = maslovIndex n (expPath (Matrix.diagonal σ)) := by
  obtain ⟨e, he⟩ := exists_perm_of_card_neg hσ hσ' hcard
  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := (1 : Matrix _ _ ℝ).submatrix id e
  have hP : P.det ≠ 0 := by
    rw [Matrix.det_permute', Matrix.det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
  obtain ⟨L, hL, hL0, hLdet, τ, hτ, hL1⟩ := exists_path_to_sign hP
  have hdσ : (Matrix.diagonal σ).det ≠ 0 := (isSmallSymm_sign hσ).det_ne
  have h := maslovIndex_congr_path hL continuous_const hLdet
    (fun _ _ => Matrix.diagonal_transpose σ) (fun _ _ => hdσ)
  rw [hL0, hL1, permMatrix_transpose_mul_diagonal_mul, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal] at h
  have hττ : (fun i => τ i * σ i * τ i) = σ := funext fun i => by
    rcases hτ i with h | h <;> rw [h] <;> ring
  have hσe : σ ∘ e = σ' := funext fun i => (he i).symm
  rw [hττ, hσe] at h
  exact maslovIndex_expPath_of_normalize (isSmallSymm_sign hσ') (isSmallSymm_sign hσ) h

/-- **Every admissible `S` has the index of a diagonal matrix of signs** with as many `-1` as
`S` has negative eigenvalues. -/
theorem exists_sign_of_isSmallSymm {S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hS : IsSmallSymm S) :
    ∃ σ : Fin n ⊕ Fin n → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
      (Finset.univ.filter fun i => σ i < 0).card = negEigenCount S ∧
      maslovIndex n (expPath S) = maslovIndex n (expPath (Matrix.diagonal σ)) := by
  -- the spectral theorem: `S = U diag(λ) Uᵀ`
  have hH : S.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hS.symm]
  set U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := hH.eigenvectorUnitary.val
  set lam := hH.eigenvalues
  have hSU : S = (Uᵀ)ᵀ * Matrix.diagonal lam * Uᵀ := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Matrix.transpose_transpose, Unitary.conjStarAlgAut_apply]
    simp [U, lam, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hUU : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hUdet : (Uᵀ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hUU
    rw [Matrix.det_mul, Matrix.det_one, h0, mul_zero] at this
    exact zero_ne_one this
  have hlam : ∀ i, lam i ≠ 0 := by
    intro i h0
    apply hS.det_ne
    rw [hSU, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero, zero_mul]
  set σ : Fin n ⊕ Fin n → ℝ := fun i => if 0 < lam i then 1 else -1
  have hσ : ∀ i, σ i = 1 ∨ σ i = -1 := fun i => by simp only [σ]; split_ifs <;> simp
  refine ⟨σ, hσ, ?_, ?_⟩
  · -- the negative eigenvalues of `S` are those of `λ`
    rw [negEigenCount, hH.roots_charpoly_eq_eigenvalues, Multiset.countP_map,
      Finset.card_def, Finset.filter_val]
    congr 1
    refine Multiset.filter_congr fun i _ => ?_
    simp only [σ, Function.comp_apply, RCLike.ofReal_real_eq_id, id]
    split_ifs with h
    · exact iff_of_false (by norm_num) (not_lt.2 h.le)
    · exact iff_of_true (by norm_num) (lt_of_le_of_ne (not_lt.1 h) (hlam i))
  · -- first move the eigenvalues to their signs, then `Uᵀ` to a diagonal matrix of signs
    have hA := maslovIndex_congr_path (L := fun _ => Uᵀ)
      (D := fun s => Matrix.diagonal fun i => (1 - s) * lam i + s * σ i)
      continuous_const
      (continuous_pi fun a => continuous_pi fun b => by
        simp only [Matrix.diagonal_apply]; split_ifs <;> fun_prop)
      (fun _ _ => hUdet) (fun _ _ => Matrix.diagonal_transpose _) fun s ⟨hs0, hs1⟩ => by
        rw [Matrix.det_diagonal]
        refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
        simp only [σ]
        split_ifs with h
        · exact convex_ne_zero hs0 hs1 (.inl ⟨h, one_pos⟩)
        · exact convex_ne_zero hs0 hs1
            (.inr ⟨lt_of_le_of_ne (not_lt.1 h) (hlam i), by norm_num⟩)
    simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add] at hA
    obtain ⟨L, hL, hL0, hLdet, τ, hτ, hL1⟩ := exists_path_to_sign hUdet
    have hB := maslovIndex_congr_path hL continuous_const hLdet
      (fun _ _ => Matrix.diagonal_transpose σ) (fun _ _ => (isSmallSymm_sign hσ).det_ne)
    rw [hL0, hL1, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal] at hB
    have hττ : (fun i => τ i * σ i * τ i) = σ := funext fun i => by
      rcases hτ i with h | h <;> rw [h] <;> ring
    rw [hττ] at hB
    rw [maslovIndex_expPath_normalize hS, hSU, hA, hB,
      ← maslovIndex_expPath_normalize (isSmallSymm_sign hσ)]

end Reduction

/-! ### Diagonal matrices of signs, and the normalisation -/

section Signs

/-- The number of negative entries of a vector. -/
noncomputable def negCount {ι : Type*} [Fintype ι] (σ : ι → ℝ) : ℕ :=
  (Finset.univ.filter fun i => σ i < 0).card

theorem negCount_le {ι : Type*} [Fintype ι] (σ : ι → ℝ) : negCount σ ≤ Fintype.card ι :=
  Finset.card_filter_le _ _

theorem blockSum_diagonal {m k : ℕ} (d₁ : Fin m ⊕ Fin m → ℝ) (d₂ : Fin k ⊕ Fin k → ℝ) :
    blockSum (Matrix.diagonal d₁) (Matrix.diagonal d₂) =
      Matrix.diagonal (Sum.elim d₁ d₂ ∘ (blockSumEquiv m k).symm) := by
  rw [blockSum, Matrix.fromBlocks_diagonal, Matrix.reindex_apply,
    Matrix.submatrix_diagonal_equiv]

theorem negCount_blockSum {m k : ℕ} (d₁ : Fin m ⊕ Fin m → ℝ) (d₂ : Fin k ⊕ Fin k → ℝ) :
    negCount (Sum.elim d₁ d₂ ∘ (blockSumEquiv m k).symm) = negCount d₁ + negCount d₂ := by
  simp only [negCount, Finset.card_filter]
  rw [← Equiv.sum_comp (blockSumEquiv m k), Fintype.sum_sum_type]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

theorem sign_blockSum {m k : ℕ} {d₁ : Fin m ⊕ Fin m → ℝ} {d₂ : Fin k ⊕ Fin k → ℝ}
    (h₁ : ∀ i, d₁ i = 1 ∨ d₁ i = -1) (h₂ : ∀ i, d₂ i = 1 ∨ d₂ i = -1) (i) :
    (Sum.elim d₁ d₂ ∘ (blockSumEquiv m k).symm) i = 1 ∨
      (Sum.elim d₁ d₂ ∘ (blockSumEquiv m k).symm) i = -1 := by
  simp only [Function.comp_apply]
  rcases (blockSumEquiv m k).symm i with j | j
  · exact h₁ j
  · exact h₂ j

/-- For a diagonal matrix of signs with an even number `2b` of `-1`, the index is `2b - N`:
permute it to `Id_a ⊕ (-Id_b)` and add the indices of the two rotations. -/
theorem maslovIndex_expPath_sign_even {N b : ℕ} {σ : Fin N ⊕ Fin N → ℝ}
    (hσ : ∀ i, σ i = 1 ∨ σ i = -1) (hb : negCount σ = 2 * b) :
    maslovIndex N (expPath (Matrix.diagonal σ)) = 2 * (b : ℤ) - N := by
  have hle : b ≤ N := by
    have := negCount_le σ
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  obtain ⟨a, rfl⟩ : ∃ a, N = a + b := ⟨N - b, by omega⟩
  set ρ := Sum.elim (fun _ : Fin a ⊕ Fin a => (1 : ℝ)) (fun _ : Fin b ⊕ Fin b => (-1 : ℝ)) ∘
    (blockSumEquiv a b).symm
  have hρ : ∀ i, ρ i = 1 ∨ ρ i = -1 :=
    sign_blockSum (fun _ => .inl rfl) (fun _ => .inr rfl)
  have hcount : negCount ρ = 2 * b := by
    rw [negCount_blockSum]
    simp [negCount, Finset.filter_true_of_mem, Finset.filter_false_of_mem]
    ring
  have hπ := Real.pi_gt_three
  have h₁ := isSmallSymm_smul_one (n := a) (c := 1) one_ne_zero (by rw [abs_one]; linarith)
  have h₂ := isSmallSymm_smul_one (n := b) (c := -1) (by norm_num) (by norm_num; linarith)
  have hsum := maslovIndex_blockSum (isAdmissiblePath_expPath h₁.symm h₁.det_ne h₁.bound)
    (isAdmissiblePath_expPath h₂.symm h₂.det_ne h₂.bound)
  rw [← expPath_blockSum, maslovIndex_expPath_smul_one one_ne_zero (by rw [abs_one]; linarith),
    maslovIndex_expPath_smul_one (by norm_num) (by norm_num; linarith),
    Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal, blockSum_diagonal] at hsum
  rw [maslovIndex_expPath_sign_eq hρ hσ (by rw [← negCount, ← negCount, hb, hcount])]
  rw [hsum, if_pos one_pos, if_neg (by norm_num)]
  push_cast; ring

/-- **The index of a diagonal matrix of signs**: the number of `-1` minus `n`, by doubling. -/
theorem maslovIndex_expPath_diagonal_sign {σ : Fin n ⊕ Fin n → ℝ}
    (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    maslovIndex n (expPath (Matrix.diagonal σ)) = (negCount σ : ℤ) - n := by
  have hd := maslovIndex_expPath_sign_even (N := n + n) (b := negCount σ) (sign_blockSum hσ hσ)
    (by rw [negCount_blockSum]; ring)
  have hS := isSmallSymm_sign hσ
  have hadm := isAdmissiblePath_expPath hS.symm hS.det_ne hS.bound
  rw [← blockSum_diagonal, expPath_blockSum, maslovIndex_blockSum hadm hadm] at hd
  push_cast at hd
  linarith

/-- **Proposition 7.2.1, the normalisation**: for `S` symmetric, invertible, with eigenvalues
smaller than `2π` in absolute value, the index of `exp(tJS)` is `Ind(S) - n`. -/
theorem maslovIndex_expPath_eq {S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hS : Sᵀ = S)
    (hdet : S.det ≠ 0) (hb : ∀ c : ℝ, (S - c • 1).det = 0 → |c| < 2 * Real.pi) :
    maslovIndex n (expPath S) = (negEigenCount S : ℤ) - n := by
  obtain ⟨σ, hσ, hcard, hμ⟩ := exists_sign_of_isSmallSymm ⟨hS, hdet, hb⟩
  rw [hμ, maslovIndex_expPath_diagonal_sign hσ, negCount, hcard]

end Signs

end MaslovIndex
end MorseFloer
