import MorseFloer.Part2.UnitaryRotation
import MorseFloer.Part2.MaslovIndex
import MorseFloer.Part2.SardLowDim

/-!
# Loops of unitary matrices

A loop of unitary matrices on which `det` has winding number zero is contractible through
loops (`nullHomotopic_of_windsZero`).

The proof is an induction on the size of the matrices, and uses no fibre bundle. Let `c(t)` be
the column of the loop `f(t)` at a fixed index `i₀`, a loop on the unit sphere.

* It is approximated by a polynomial curve, and the approximation is lifted to the loop by the
  rotations `R(c(t), ·)` of `Part2/UnitaryRotation.lean`. A polynomial curve misses a point of
  the sphere as soon as the dimension is at least two: the cone `(r, t) ↦ r p(t)` is a `C¹`
  image of the plane, hence Lebesgue-null.
* Multiplying on the left by a rotation brings the missed point to `-e_{i₀}`, and the
  rotations `R(c(t), e_{i₀})` then contract the column to `e_{i₀}`.
* The loop now fixes `e_{i₀}`, so it lives in the unitary group of the other indices, and has
  the same determinant.

In size one the loop is `e^{iθ(t)}` with `θ(0) = θ(1)`, and `e^{i(1-s)θ(t)}` contracts it.
-/

open Matrix unitInterval ContinuousMap

namespace MorseFloer
namespace UnitaryLoops

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Unit vectors -/

section Unit

omit [DecidableEq ι] in
theorem herm_self (w : ι → ℂ) : herm w w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
  rw [herm, dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, RCLike.star_def, Complex.normSq_eq_conj_mul_self]

omit [DecidableEq ι] in
theorem eq_zero_of_herm_self (w : ι → ℂ) (h : herm w w = 0) : w = 0 := by
  rw [herm_self, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _] at h
  exact funext fun i => Complex.normSq_eq_zero.1 (h i (Finset.mem_univ _))

omit [DecidableEq ι] in
/-- Two unit vectors with `⟨b, a⟩ = -1` are opposite. -/
theorem eq_neg_of_herm_eq_neg_one {a b : ι → ℂ} (ha : herm a a = 1) (hb : herm b b = 1)
    (h : herm b a = -1) : b = -a := by
  have h' : herm a b = -1 := by rw [← star_herm, h, star_neg, star_one]
  have : herm (a + b) (a + b) = 0 := by
    simp only [herm, add_dotProduct, dotProduct_add, star_add] at ha hb h h' ⊢
    rw [ha, hb, h, h']; ring
  exact eq_neg_of_add_eq_zero_right (eq_zero_of_herm_self _ this)

omit [DecidableEq ι] in
theorem one_add_herm_ne_zero {a b : ι → ℂ} (ha : herm a a = 1) (hb : herm b b = 1)
    (hne : b ≠ -a) : 1 + herm b a ≠ 0 := fun h =>
  hne (eq_neg_of_herm_eq_neg_one ha hb (by linear_combination h))

/-- The Euclidean norm. -/
noncomputable def enorm' (w : ι → ℂ) : ℝ := Real.sqrt (∑ i, Complex.normSq (w i))

/-- The unit vector in the direction of `w`. -/
noncomputable def unitize (w : ι → ℂ) : ι → ℂ := ((enorm' w)⁻¹ : ℂ) • w

omit [DecidableEq ι] in
theorem enorm'_pos {w : ι → ℂ} (hw : w ≠ 0) : 0 < enorm' w := by
  refine Real.sqrt_pos.2 (lt_of_le_of_ne (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
    fun h => hw (eq_zero_of_herm_self w ?_))
  rw [herm_self, ← h, Complex.ofReal_zero]

omit [DecidableEq ι] in
theorem herm_unitize {w : ι → ℂ} (hw : w ≠ 0) : herm (unitize w) (unitize w) = 1 := by
  have hpos := enorm'_pos hw
  have hsq : (enorm' w) ^ 2 = ∑ i, Complex.normSq (w i) :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
  simp only [unitize, herm, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← herm, herm_self, ← hsq, RCLike.star_def, ← Complex.ofReal_inv, Complex.conj_ofReal]
  have hne : ((enorm' w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast
  field_simp

omit [DecidableEq ι] in
theorem unitize_of_herm {w : ι → ℂ} (h : herm w w = 1) : unitize w = w := by
  have h1 : ∑ i, Complex.normSq (w i) = 1 := by
    rw [herm_self] at h; exact_mod_cast h
  rw [unitize, enorm', h1, Real.sqrt_one, Complex.ofReal_one, inv_one, one_smul]

omit [DecidableEq ι] in
theorem continuous_unitize {X : Type*} [TopologicalSpace X] {w : X → ι → ℂ} (hw : Continuous w)
    (h0 : ∀ x, w x ≠ 0) : Continuous fun x => unitize (w x) := by
  have hn : Continuous fun x => enorm' (w x) := by unfold enorm'; fun_prop
  exact ((Complex.continuous_ofReal.comp hn).inv₀ fun x => by
    show ((enorm' (w x) : ℝ) : ℂ) ≠ 0
    exact_mod_cast (enorm'_pos (h0 x)).ne').smul hw

omit [DecidableEq ι] in
/-- A unit vector parallel to `w`, pointing the same way, is `unitize w`. -/
theorem herm_unitize_self {w : ι → ℂ} (hw : w ≠ 0) :
    w = ((enorm' w : ℝ) : ℂ) • unitize w := by
  rw [unitize, smul_smul, mul_inv_cancel₀ (by exact_mod_cast (enorm'_pos hw).ne'), one_smul]

end Unit

/-! ### Loops and their homotopies -/

section Loops

/-- A loop of unitary matrices. -/
def IsULoop (f : C(I, Matrix ι ι ℂ)) : Prop :=
  (∀ t, f t ∈ Matrix.unitaryGroup ι ℂ) ∧ f 0 = f 1

/-- Build a homotopy through loops from a continuous function of `(s, t)`. -/
theorem homotopicWith_of {f g : C(I, Matrix ι ι ℂ)} (H : I × I → Matrix ι ι ℂ)
    (hH : Continuous H) (h0 : ∀ t, H (0, t) = f t) (h1 : ∀ t, H (1, t) = g t)
    (hP : ∀ s, (∀ t, H (s, t) ∈ Matrix.unitaryGroup ι ℂ) ∧ H (s, 0) = H (s, 1)) :
    HomotopicWith f g IsULoop :=
  ⟨{ toFun := H, continuous_toFun := hH, map_zero_left := h0, map_one_left := h1,
     prop' := fun s => hP s }⟩

/-- `det` of the loop has a continuous angle with the same value at both ends. -/
def WindsZero (f : C(I, Matrix ι ι ℂ)) : Prop :=
  ∃ θ : I → ℝ, Continuous θ ∧ θ 0 = θ 1 ∧ ∀ t, Complex.exp (θ t * Complex.I) = (f t).det

theorem continuous_det_comp {X : Type*} [TopologicalSpace X] {F : X → Matrix ι ι ℂ}
    (hF : Continuous F) : Continuous fun x => (F x).det :=
  hF.matrix_det

theorem norm_det_of_mem {A : Matrix ι ι ℂ} (hA : A ∈ Matrix.unitaryGroup ι ℂ) : ‖A.det‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hA)

/-- **The winding of `det` is a homotopy invariant.** -/
theorem WindsZero.of_homotopic {f g : C(I, Matrix ι ι ℂ)} (hfg : HomotopicWith f g IsULoop)
    (hf : WindsZero f) : WindsZero g := by
  obtain ⟨F⟩ := hfg
  obtain ⟨θ, hθc, hθ01, hθe⟩ := hf
  -- extend `det ∘ F` to the plane and lift it
  set π : ℝ → I := Set.projIcc 0 1 zero_le_one
  have hπ : Continuous π := continuous_projIcc
  have hdet : Continuous fun p : ℝ × ℝ => (F (π p.1, π p.2)).det :=
    continuous_det_comp (F.continuous.comp ((hπ.comp continuous_fst).prodMk (hπ.comp continuous_snd)))
  obtain ⟨G, hG, hG0, hGe⟩ := MaslovIndex.exists_lift hdet
    (fun p => norm_det_of_mem ((F.prop (π p.1)).1 (π p.2))) (0, 0) (θ₀ := θ 0) (by
      rw [hθe]; simp [π, F.apply_zero])
  -- `G (s, 1) - G (s, 0)` is a multiple of `2π`, hence constant
  have hmul : ∀ s : ℝ, ∃ k : ℤ, G (s, 1) - G (s, 0) = k * Real.pi := fun s => by
    have h : Complex.exp (G (s, 1) * Complex.I) = Complex.exp (G (s, 0) * Complex.I) := by
      rw [hGe, hGe]
      have := (F.prop (π s)).2
      simp only [π, Set.projIcc_left, Set.projIcc_right]
      exact congrArg Matrix.det this.symm
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    refine ⟨2 * m, ?_⟩
    have := congrArg Complex.im hm
    simp at this
    push_cast; linarith
  have hconst := MaslovIndex.eq_of_exp_two_mul
    ((hG.comp (continuous_id.prodMk continuous_const)).sub
      (hG.comp (continuous_id.prodMk continuous_const))) hmul 0 1
  -- at `s = 0` the lift is `θ`
  have h0 : (fun t : ℝ => G (0, t)) = fun t => θ (π t) :=
    MaslovIndex.lift_unique (hG.comp (continuous_const.prodMk continuous_id))
      (hθc.comp hπ) (fun t => by rw [hGe, hθe]; simp [π, F.apply_zero]) 0 (by simp [π, hG0])
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
  simp [π, F.apply_one]

end Loops


/-! ### The stabiliser of a basis vector -/

section Stabiliser

variable (i₀ : ι)

/-- The indices other than `i₀`. -/
abbrev Cpl := {j : ι // ¬ j = i₀}

/-- `ι` split as `{i₀}` and the rest. -/
def splitEquiv : {j : ι // j = i₀} ⊕ Cpl i₀ ≃ ι := Equiv.sumCompl (· = i₀)

/-- The matrix of `ι` acting as `M` on the indices other than `i₀` and fixing `e_{i₀}`. -/
noncomputable def embed (M : Matrix (Cpl i₀) (Cpl i₀) ℂ) : Matrix ι ι ℂ :=
  Matrix.reindex (splitEquiv i₀) (splitEquiv i₀) (Matrix.fromBlocks 1 0 0 M)

variable {i₀}

omit [Fintype ι] in
theorem embed_one : embed i₀ 1 = 1 := by
  rw [embed, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem embed_mul (A B : Matrix (Cpl i₀) (Cpl i₀) ℂ) :
    embed i₀ (A * B) = embed i₀ A * embed i₀ B := by
  rw [embed, embed, embed, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

omit [Fintype ι] in
theorem embed_conjTranspose (A : Matrix (Cpl i₀) (Cpl i₀) ℂ) :
    (embed i₀ A)ᴴ = embed i₀ Aᴴ := by
  rw [embed, embed, Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]
  simp

theorem det_embed (A : Matrix (Cpl i₀) (Cpl i₀) ℂ) : (embed i₀ A).det = A.det := by
  rw [embed, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

theorem embed_mem_unitaryGroup {A : Matrix (Cpl i₀) (Cpl i₀) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Cpl i₀) ℂ) : embed i₀ A ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hA ⊢
  rw [embed_conjTranspose, ← embed_mul, hA, embed_one]

omit [Fintype ι] in
theorem continuous_embed {X : Type*} [TopologicalSpace X] {A : X → Matrix (Cpl i₀) (Cpl i₀) ℂ}
    (hA : Continuous A) : Continuous fun x => embed i₀ (A x) :=
  (continuous_const.matrix_fromBlocks continuous_const continuous_const hA).matrix_reindex _ _

/-- The restriction of a matrix to the indices other than `i₀`. -/
def restrict (V : Matrix ι ι ℂ) : Matrix (Cpl i₀) (Cpl i₀) ℂ :=
  V.submatrix Subtype.val Subtype.val

omit [Fintype ι] in
theorem embed_apply (A : Matrix (Cpl i₀) (Cpl i₀) ℂ) (i j : ι) :
    embed i₀ A i j = if hi : i = i₀ then (if j = i₀ then 1 else 0) else
      if hj : j = i₀ then 0 else A ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [embed, Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases hi : i = i₀ <;> by_cases hj : j = i₀ <;>
    simp [hi, hj, splitEquiv, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg]

omit [Fintype ι] in
theorem restrict_embed (A : Matrix (Cpl i₀) (Cpl i₀) ℂ) : restrict (embed i₀ A) = A := by
  ext i j
  rw [restrict, Matrix.submatrix_apply, embed_apply, dite_eq_right i.2, dite_eq_right j.2]

/-- A unitary matrix fixing `e_{i₀}` is the embedding of its restriction. -/
theorem embed_restrict {V : Matrix ι ι ℂ} (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (hfix : V *ᵥ Pi.single i₀ 1 = Pi.single i₀ 1) : embed i₀ (restrict V) = V := by
  -- the column of `i₀`
  have hcol : ∀ i, V i i₀ = (Pi.single i₀ 1 : ι → ℂ) i := fun i => by
    have := congrFun hfix i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at this
  -- the row of `i₀`, from `Vᴴ e = Vᴴ V e = e`
  have hrow : ∀ j, V i₀ j = (Pi.single i₀ 1 : ι → ℂ) j := fun j => by
    have h1 : Vᴴ *ᵥ Pi.single i₀ 1 = Pi.single i₀ 1 := by
      conv_lhs => rw [← hfix]
      rw [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
        (Matrix.mem_unitaryGroup_iff').1 hV, Matrix.one_mulVec]
    have := congrFun h1 j
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.conjTranspose_apply] at this
    rw [← star_star (V i₀ j), this]
    by_cases h : j = i₀ <;> simp [h]
  ext i j
  rw [embed_apply]
  by_cases hi : i = i₀
  · subst hi
    rw [dite_eq_left rfl, hrow]
    by_cases hj : j = i <;> simp [hj]
  · rw [dite_eq_right hi]
    by_cases hj : j = i₀
    · rw [dite_eq_left hj, hj, hcol, Pi.single_eq_of_ne hi]
    · rw [dite_eq_right hj]; rfl

theorem restrict_mem_unitaryGroup {V : Matrix ι ι ℂ} (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (hfix : V *ᵥ Pi.single i₀ 1 = Pi.single i₀ 1) :
    restrict V ∈ Matrix.unitaryGroup (Cpl i₀) ℂ := by
  have h := embed_restrict hV hfix
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hV
  rw [← restrict_embed ((restrict V)ᴴ * restrict V), embed_mul, ← embed_conjTranspose, h, hV,
    ← embed_one, restrict_embed]

/-- **A loop fixing `e_{i₀}` reduces to the smaller unitary group.** -/
theorem homotopic_of_fix {f : C(I, Matrix ι ι ℂ)} (hf : IsULoop f)
    (hfix : ∀ t, f t *ᵥ Pi.single i₀ 1 = Pi.single i₀ 1) (hw : WindsZero f)
    (IH : ∀ g : C(I, Matrix (Cpl i₀) (Cpl i₀) ℂ), IsULoop g → WindsZero g →
      HomotopicWith g (ContinuousMap.const I 1) IsULoop) :
    HomotopicWith f (ContinuousMap.const I 1) IsULoop := by
  let g : C(I, Matrix (Cpl i₀) (Cpl i₀) ℂ) :=
    ⟨fun t => restrict (f t), f.continuous.matrix_submatrix _ _⟩
  have hfg : ∀ t, embed i₀ (g t) = f t := fun t => embed_restrict (hf.1 t) (hfix t)
  have hg : IsULoop g :=
    ⟨fun t => restrict_mem_unitaryGroup (hf.1 t) (hfix t),
      show restrict (f 0) = restrict (f 1) by rw [hf.2]⟩
  have hwg : WindsZero g := by
    obtain ⟨θ, hθ, h01, he⟩ := hw
    exact ⟨θ, hθ, h01, fun t => by rw [he, ← hfg t, det_embed]⟩
  obtain ⟨H⟩ := IH g hg hwg
  exact homotopicWith_of (fun p => embed i₀ (H p)) (continuous_embed H.continuous)
    (fun t => by simp [H.apply_zero, hfg]) (fun t => by simp [H.apply_one, embed_one])
    fun s => ⟨fun t => embed_mem_unitaryGroup ((H.prop s).1 t),
      by simpa using congrArg (embed i₀) (H.prop s).2⟩

end Stabiliser

/-! ### Size at most one -/

section Small

/-- **In size at most one**, a loop whose determinant winds zero times is contractible:
it is `e^{iθ(t)} Id` with `θ(0) = θ(1)`. -/
theorem homotopic_of_subsingleton [Subsingleton ι] {f : C(I, Matrix ι ι ℂ)}
    (hw : WindsZero f) : HomotopicWith f (ContinuousMap.const I 1) IsULoop := by
  obtain ⟨θ, hθ, h01, he⟩ := hw
  -- a matrix of size at most one is its determinant times the identity
  have hscal : ∀ A : Matrix ι ι ℂ, A = A.det • (1 : Matrix ι ι ℂ) := fun A => by
    ext i j
    have hij := Subsingleton.elim i j
    subst hij
    have : Unique ι := uniqueOfSubsingleton i
    have : A.det = A i i := by
      rw [Matrix.det_unique, Subsingleton.elim (default : ι) i]
    rw [Matrix.smul_apply, this, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  refine homotopicWith_of (fun p => Complex.exp (((1 - (p.1 : ℝ)) * θ p.2 : ℝ) * Complex.I) • 1)
    (by fun_prop) (fun t => ?_) (fun t => by simp) fun s => ⟨fun t => ?_, ?_⟩
  · simp only [Set.Icc.coe_zero, sub_zero, one_mul]
    rw [he, ← hscal]
  · rw [Matrix.mem_unitaryGroup_iff', star_smul, star_one, smul_mul_smul_comm, mul_one,
      RCLike.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_ofReal]
  · simp [h01]

end Small


/-! ### Unitary matrices preserve the Hermitian product -/

section Herm

theorem herm_mulVec_unitary {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (x y : ι → ℂ) : herm (U *ᵥ x) (U *ᵥ y) = herm x y := by
  rw [herm, herm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').1 hU, Matrix.one_mulVec]

theorem mulVec_injective_unitary {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    {x y : ι → ℂ} (h : U *ᵥ x = U *ᵥ y) : x = y := by
  have := congrArg (fun z => star U *ᵥ z) h
  simpa [Matrix.mulVec_mulVec, (Matrix.mem_unitaryGroup_iff').1 hU] using this

omit [DecidableEq ι] in
theorem norm_le_one_of_herm {c : ι → ℂ} (hc : herm c c = 1) (i : ι) : ‖c i‖ ≤ 1 := by
  have h1 : ∑ j, Complex.normSq (c j) = 1 := by rw [herm_self] at hc; exact_mod_cast hc
  have : Complex.normSq (c i) ≤ 1 :=
    h1 ▸ Finset.single_le_sum (f := fun j => Complex.normSq (c j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [Complex.normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (c i)]

omit [DecidableEq ι] in
/-- A convex combination of `a` and `b` is not a nonnegative multiple of `-a` when
`Re ⟨a, b⟩ > 0`. -/
theorem combo_ne_of_re_pos {a b : ι → ℂ} (ha : herm a a = 1) (hab : 0 < (herm a b).re)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) {r : ℝ} (hr : 0 ≤ r) :
    ((1 - s : ℝ) : ℂ) • a + (s : ℂ) • b ≠ (r : ℂ) • (-a) := fun h => by
  have := congrArg (fun w => (herm a w).re) h
  simp only [herm, dotProduct_add, dotProduct_smul, dotProduct_neg, smul_eq_mul] at this ha hab
  rw [ha] at this
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.neg_re, mul_one, sub_zero, zero_mul] at this
  have h1 : 0 ≤ s * (star a ⬝ᵥ b).re := mul_nonneg hs.1 hab.le
  rcases eq_or_lt_of_le hs.2 with h2 | h2
  · subst h2; linarith
  · linarith

omit [DecidableEq ι] in
/-- A convex combination of unit vectors `a` and `b ≠ -a` is not a nonnegative multiple of
`-a`. -/
theorem combo_ne_of_ne_neg {a b : ι → ℂ} (ha : herm a a = 1) (hb : herm b b = 1) (hne : b ≠ -a)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) {r : ℝ} (hr : 0 ≤ r) :
    ((1 - s : ℝ) : ℂ) • a + (s : ℂ) • b ≠ (r : ℂ) • (-a) := fun h => by
  have ha0 : a ≠ 0 := fun h0 => by simp [h0, herm] at ha
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · -- `s = 0`: then `a = -r a`
    subst hs0
    simp only [sub_zero, Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul,
      add_zero] at h
    have : ((1 + r : ℝ) : ℂ) • a = 0 := by
      rw [Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
      nth_rewrite 1 [h]
      rw [smul_neg, neg_add_cancel]
    rcases smul_eq_zero.1 this with h1 | h1
    · have : (1 + r : ℝ) = 0 := by exact_mod_cast h1
      linarith
    · exact ha0 h1
  · -- `s > 0`: then `b = -k a` with `k ≥ 0`, and `k = 1` since `b` is a unit vector
    set k : ℝ := (r + 1 - s) / s
    have hk : 0 ≤ k := div_nonneg (by linarith [hs.2]) hs0.le
    have hb' : b = ((-k : ℝ) : ℂ) • a := by
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      have : (s : ℂ) • b = ((-(r + 1 - s) : ℝ) : ℂ) • a := by
        rw [← sub_eq_iff_eq_add'.2 h.symm]; push_cast; module
      rw [← smul_right_inj hs', this, smul_smul]
      congr 1
      simp only [k]; push_cast; field_simp
    have hk1 : k = 1 := by
      have := hb
      rw [hb'] at this
      simp only [herm, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at this ha
      rw [ha] at this
      simp only [RCLike.star_def, Complex.conj_ofReal, mul_one] at this
      have : k * k = 1 := by
        have h2 : ((-k : ℝ) : ℂ) * ((-k : ℝ) : ℂ) = 1 := this
        exact_mod_cast (by push_cast at h2 ⊢; linear_combination h2 : ((k * k : ℝ) : ℂ) = 1)
      nlinarith
    apply hne
    rw [hb', hk1]
    simp

end Herm

/-! ### Rotating the column of a loop -/

section Rotate

/-- **Rotating a column.** For loops `a`, `b` of unit vectors such that no convex combination
of `a t` and `b t` points along `-a t`, the loop `f` is homotopic to `R(a, b) f`. -/
theorem homotopic_rotate {f : C(I, Matrix ι ι ℂ)} (hf : IsULoop f) {a b : C(I, ι → ℂ)}
    (ha : ∀ t, herm (a t) (a t) = 1) (hb : ∀ t, herm (b t) (b t) = 1) (ha01 : a 0 = a 1)
    (hb01 : b 0 = b 1)
    (hne : ∀ (s : I) (t : I) (r : ℝ), 0 ≤ r →
      ((1 - s : ℝ) : ℂ) • a t + ((s : ℝ) : ℂ) • b t ≠ (r : ℂ) • (-a t)) :
    ∃ g : C(I, Matrix ι ι ℂ), (∀ t, g t = rot (a t) (b t) * f t) ∧ IsULoop g ∧
      HomotopicWith f g IsULoop := by
  set w : I × I → ι → ℂ := fun p => ((1 - p.1 : ℝ) : ℂ) • a p.2 + ((p.1 : ℝ) : ℂ) • b p.2
  have hw : Continuous w := by
    simp only [w]
    fun_prop
  have hw0 : ∀ p, w p ≠ 0 := fun p h => hne p.1 p.2 0 le_rfl (by
    rw [Complex.ofReal_zero, zero_smul]; exact h)
  have hba : ∀ t, b t ≠ -a t := fun t h => hne 1 t 1 zero_le_one (by simp [h])
  have hab1 : ∀ t, 1 + herm (b t) (a t) ≠ 0 := fun t =>
    one_add_herm_ne_zero (ha t) (hb t) (hba t)
  -- the rotated direction is never opposite to `a`
  have hwa : ∀ p, unitize (w p) ≠ -a p.2 := fun p h => by
    apply hne p.1 p.2 (enorm' (w p)) (enorm'_pos (hw0 p)).le
    rw [← h]
    exact herm_unitize_self (hw0 p)
  have hrot : ∀ p, 1 + herm (unitize (w p)) (a p.2) ≠ 0 := fun p =>
    one_add_herm_ne_zero (ha p.2) (herm_unitize (hw0 p)) (hwa p)
  have hcont : Continuous fun p : I × I => rot (a p.2) (unitize (w p)) * f p.2 :=
    (continuous_rot (a.continuous.comp continuous_snd) (continuous_unitize hw hw0) hrot).mul
      (f.continuous.comp continuous_snd)
  have hmem : ∀ p : I × I, rot (a p.2) (unitize (w p)) * f p.2 ∈ Matrix.unitaryGroup ι ℂ :=
    fun p => Submonoid.mul_mem _
      (rot_mem_unitaryGroup (ha p.2) (herm_unitize (hw0 p)) (hrot p)) (hf.1 p.2)
  have hw1 : ∀ t, unitize (w (1, t)) = b t := fun t => by
    simp only [w, Set.Icc.coe_one, sub_self, Complex.ofReal_zero, zero_smul, zero_add,
      Complex.ofReal_one, one_smul]
    exact unitize_of_herm (hb t)
  refine ⟨⟨fun t => rot (a t) (b t) * f t,
      (continuous_rot a.continuous b.continuous hab1).mul f.continuous⟩, fun t => rfl, ?_, ?_⟩
  · refine ⟨fun t => ?_, ?_⟩
    · exact Submonoid.mul_mem _ (rot_mem_unitaryGroup (ha t) (hb t) (hab1 t)) (hf.1 t)
    · simp only [ContinuousMap.coe_mk]; rw [ha01, hb01, hf.2]
  · refine homotopicWith_of _ hcont (fun t => ?_) (fun t => ?_) fun s => ⟨fun t => hmem (s, t), ?_⟩
    · simp only [w, Set.Icc.coe_zero, sub_zero, Complex.ofReal_one, one_smul, Complex.ofReal_zero,
        zero_smul, add_zero]
      rw [unitize_of_herm (ha t), rot_self (ha t), Matrix.one_mul]
    · simp only [ContinuousMap.coe_mk]; rw [hw1]
    · simp only [w]; rw [ha01, hb01, hf.2]

end Rotate

/-! ### A smooth curve misses a point of the sphere -/

section Approximation

omit [DecidableEq ι] in
/-- **Weierstrass for curves in `ℂ^ι`**, keeping both endpoints. -/
theorem exists_contDiff_near (c : C(I, ι → ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℝ → ι → ℂ, ContDiff ℝ 1 P ∧ P 0 = c 0 ∧ P 1 = c 1 ∧
      ∀ (t : I) (i : ι), ‖P t i - c t i‖ < ε := by
  have hε6 : 0 < ε / 6 := by positivity
  have hre : ∀ i, ∃ p : Polynomial ℝ, ‖p.toContinuousMapOn (Set.Icc (0 : ℝ) 1) -
      ⟨fun t : I => (c t i).re, by fun_prop⟩‖ < ε / 6 :=
    fun i => exists_polynomial_near_continuousMap 0 1 _ _ hε6
  have him : ∀ i, ∃ p : Polynomial ℝ, ‖p.toContinuousMapOn (Set.Icc (0 : ℝ) 1) -
      ⟨fun t : I => (c t i).im, by fun_prop⟩‖ < ε / 6 :=
    fun i => exists_polynomial_near_continuousMap 0 1 _ _ hε6
  choose pr hpr using hre
  choose pm hpm using him
  have hpoly : ∀ p : Polynomial ℝ, ContDiff ℝ 1 fun t : ℝ => ((p.eval t : ℝ) : ℂ) := fun p => by
    have := Polynomial.contDiff_aeval (𝕜 := ℝ) p 1
    simp only [Polynomial.coe_aeval_eq_eval] at this
    exact Complex.ofRealCLM.contDiff.comp this
  set Q : ℝ → ι → ℂ := fun t i => (((pr i).eval t : ℝ) : ℂ) + (((pm i).eval t : ℝ) : ℂ) * Complex.I
  have hQ : ContDiff ℝ 1 Q :=
    contDiff_pi.2 fun i => (hpoly (pr i)).add ((hpoly (pm i)).mul contDiff_const)
  -- pointwise bounds from the sup norm
  have hQc : ∀ (t : I) i, ‖Q t i - c t i‖ < ε / 3 := fun t i => by
    have h1 := (ContinuousMap.norm_coe_le_norm _ t).trans_lt (hpr i)
    have h2 := (ContinuousMap.norm_coe_le_norm _ t).trans_lt (hpm i)
    simp only [ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply,
      Polynomial.toContinuousMap_apply, ContinuousMap.coe_mk, Real.norm_eq_abs] at h1 h2
    calc ‖Q t i - c t i‖ ≤ |(Q t i - c t i).re| + |(Q t i - c t i).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ < ε / 6 + ε / 6 := by
          simp only [Q, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero,
            Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add]
          exact add_lt_add h1 h2
      _ = ε / 3 := by ring
  refine ⟨fun t => Q t + ((1 - t : ℝ) : ℂ) • (c 0 - Q 0) + ((t : ℝ) : ℂ) • (c 1 - Q 1), ?_, ?_, ?_,
    fun t i => ?_⟩
  · exact (hQ.add ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub contDiff_id)).smul
      contDiff_const)).add ((Complex.ofRealCLM.contDiff.comp contDiff_id).smul contDiff_const)
  · simp
  · simp
  · have ht0 := t.2.1
    have ht1 := t.2.2
    have e0 := hQc 0 i
    have e1 := hQc 1 i
    simp only [Set.Icc.coe_zero, Set.Icc.coe_one] at e0 e1
    have : ‖(Q t + ((1 - t : ℝ) : ℂ) • (c 0 - Q 0) + ((t : ℝ) : ℂ) • (c 1 - Q 1)) i - c t i‖ ≤
        ‖Q t i - c t i‖ + (1 - t) * ‖c 0 i - Q 0 i‖ + t * ‖c 1 i - Q 1 i‖ := by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      calc _ = ‖(Q t i - c t i) + ((1 - t : ℝ) : ℂ) * (c 0 i - Q 0 i) +
            ((t : ℝ) : ℂ) * (c 1 i - Q 1 i)‖ := by ring_nf
        _ ≤ _ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add le_rfl ?_)) ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [norm_sub_rev (c 0 i)] at this
    rw [norm_sub_rev (c 1 i)] at this
    nlinarith [hQc t i, norm_nonneg (Q 0 i - c 0 i), norm_nonneg (Q 1 i - c 1 i)]

/-- **A `C¹` curve in `ℂ^ι`, `|ι| ≥ 2`, misses a direction**, which can be taken with negative
real part at `i₀`: the cone `(r, t) ↦ r P(t)` is a `C¹` image of the plane, hence null. -/
theorem exists_missed [Nontrivial ι] (i₀ : ι) {P : ℝ → ι → ℂ} (hP : ContDiff ℝ 1 P) :
    ∃ q : ι → ℂ, herm q q = 1 ∧ (q i₀).re < 0 ∧ ∀ (t r : ℝ), 0 < r → P t ≠ (r : ℂ) • q := by
  set F : ℝ × ℝ → ι → ℂ := fun p => (p.1 : ℂ) • P p.2
  have hF : ContDiff ℝ 1 F :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst).smul (hP.comp contDiff_snd)
  have hdim : Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ (ι → ℂ) := by
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have := Fintype.one_lt_card (α := ι)
    omega
  have hnull : (MeasureTheory.volume : MeasureTheory.Measure (ι → ℂ)) (Set.range F) = 0 := by
    rw [← Set.image_univ]
    exact measure_image_eq_zero_of_finrank_lt _ hF Set.univ hdim
  set e : ι → ℂ := Pi.single i₀ 1
  obtain ⟨x, hxB, hxF⟩ : ∃ x ∈ Metric.ball (-e) (1 / 2), x ∉ Set.range F := by
    by_contra h
    push Not at h
    have hpos : 0 < (MeasureTheory.volume : MeasureTheory.Measure (ι → ℂ))
        (Metric.ball (-e) (1 / 2)) := Metric.measure_ball_pos _ _ (by norm_num)
    exact hpos.ne' (MeasureTheory.measure_mono_null (fun x hx => h x hx) hnull)
  have hx0 : (x i₀).re < -1 / 2 := by
    have h1 := (dist_le_pi_dist x (-e) i₀).trans_lt (Metric.mem_ball.1 hxB)
    simp only [e, Pi.neg_apply, Pi.single_eq_same, dist_eq_norm, sub_neg_eq_add] at h1
    have := Complex.abs_re_le_norm (x i₀ + 1)
    rw [Complex.add_re, Complex.one_re] at this
    linarith [le_abs_self ((x i₀).re + 1)]
  have hxne : x ≠ 0 := fun h => by rw [h] at hx0; simp at hx0; linarith
  refine ⟨unitize x, herm_unitize hxne, ?_, fun t r hr h => hxF ⟨(enorm' x / r, t), ?_⟩⟩
  · simp only [unitize, Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.2 (enorm'_pos hxne)) (by linarith)
  · simp only [F, h, smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ hr.ne']
    exact (herm_unitize_self hxne).symm

end Approximation

/-! ### The induction -/

section Induction

/-- The column `e_{i₀}` of a loop. -/
noncomputable def col (i₀ : ι) (f : C(I, Matrix ι ι ℂ)) : C(I, ι → ℂ) :=
  ⟨fun t => f t *ᵥ Pi.single i₀ 1, f.continuous.matrix_mulVec continuous_const⟩

theorem herm_single (i₀ : ι) : herm (Pi.single i₀ (1 : ℂ)) (Pi.single i₀ 1) = 1 := by
  simp [herm]

/-- **The induction step**, `|ι| ≥ 2`: the loop is homotopic to one fixing `e_{i₀}`. -/
theorem homotopic_of_windsZero_step [Nontrivial ι] (i₀ : ι) {f : C(I, Matrix ι ι ℂ)}
    (hf : IsULoop f) (hw : WindsZero f)
    (IH : ∀ g : C(I, Matrix (Cpl i₀) (Cpl i₀) ℂ), IsULoop g → WindsZero g →
      HomotopicWith g (ContinuousMap.const I 1) IsULoop) :
    HomotopicWith f (ContinuousMap.const I 1) IsULoop := by
  set e : ι → ℂ := Pi.single i₀ 1
  have he : herm e e = 1 := herm_single i₀
  set c := col i₀ f
  have hc : ∀ t, herm (c t) (c t) = 1 := fun t => by
    simp only [c, col, ContinuousMap.coe_mk]
    rw [herm_mulVec_unitary (hf.1 t), he]
  have hc01 : c 0 = c 1 := by simp only [c, col, ContinuousMap.coe_mk, hf.2]
  -- 1. approximate the column by a `C¹` curve
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  obtain ⟨P, hP, hP0, hP1, hPc⟩ := exists_contDiff_near c (ε := 1 / (2 * Fintype.card ι))
    (by positivity)
  have hre : ∀ t : I, 1 / 2 ≤ (herm (c t) (P t)).re := fun t => by
    have hsplit : herm (c t) (P t) = 1 + ∑ i, star (c t i) * (P t i - c t i) := by
      rw [← hc t]
      simp only [herm, dotProduct, Pi.star_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hbound : ‖∑ i, star (c t i) * (P t i - c t i)‖ ≤ 1 / 2 := by
      calc _ ≤ ∑ i, ‖star (c t i) * (P t i - c t i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : ι, 1 / (2 * (Fintype.card ι : ℝ)) := Finset.sum_le_sum
            (f := fun i => ‖star (c t i) * (P t i - c t i)‖)
            (g := fun _ => 1 / (2 * (Fintype.card ι : ℝ))) fun i _ => by
            rw [norm_mul, norm_star]
            calc ‖c t i‖ * ‖P t i - c t i‖ ≤ 1 * ‖P t i - c t i‖ :=
                  mul_le_mul_of_nonneg_right (norm_le_one_of_herm (hc t) i) (norm_nonneg _)
              _ ≤ _ := by rw [one_mul]; exact (hPc t i).le
        _ = 1 / 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
    rw [hsplit, Complex.add_re, Complex.one_re]
    linarith [neg_abs_le (∑ i, star (c t i) * (P t i - c t i)).re,
      Complex.abs_re_le_norm (∑ i, star (c t i) * (P t i - c t i))]
  have hP0' : ∀ t : I, P t ≠ 0 := fun t h => by
    have := hre t; rw [h] at this; simp [herm] at this; linarith
  set c' : C(I, ι → ℂ) := ⟨fun t => unitize (P t),
    continuous_unitize (hP.continuous.comp continuous_subtype_val) hP0'⟩
  have hc' : ∀ t, herm (c' t) (c' t) = 1 := fun t => herm_unitize (hP0' t)
  have hc'01 : c' 0 = c' 1 := by
    simp only [c', ContinuousMap.coe_mk, Set.Icc.coe_zero, Set.Icc.coe_one, hP0, hP1, hc01]
  have hcc' : ∀ t, 0 < (herm (c t) (c' t)).re := fun t => by
    simp only [c', ContinuousMap.coe_mk, unitize, herm, dotProduct_smul, smul_eq_mul,
      ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    exact mul_pos (inv_pos.2 (enorm'_pos (hP0' t))) (by have := hre t; simp only [herm] at this; linarith)
  obtain ⟨f₁, hf₁, hf₁U, hff₁⟩ := homotopic_rotate hf hc hc' hc01 hc'01
    fun s t r hr => combo_ne_of_re_pos (hc t) (hcc' t) s.2 hr
  have hcol₁ : ∀ t, f₁ t *ᵥ e = c' t := fun t => by
    rw [hf₁, ← Matrix.mulVec_mulVec]
    exact rot_mulVec_self (hc t)
  -- 2. a direction missed by the new column, moved to `-e`
  obtain ⟨q, hq, hqre, hqP⟩ := exists_missed i₀ hP
  have hc'q : ∀ t, c' t ≠ q := fun t h => by
    apply hqP t (enorm' (P t)) (enorm'_pos (hP0' t))
    rw [← h]
    exact herm_unitize_self (hP0' t)
  have hne' : herm (-e) (-e) = 1 := by
    simp only [herm, star_neg, neg_dotProduct, dotProduct_neg, neg_neg]; exact he
  have hqe : 0 < (herm q (-e)).re := by
    simp only [herm, e, dotProduct_neg, dotProduct_single, mul_one, Pi.star_apply,
      RCLike.star_def, Complex.neg_re, Complex.conj_re]
    linarith
  obtain ⟨f₂, hf₂, hf₂U, hf₁f₂⟩ := homotopic_rotate hf₁U (a := ContinuousMap.const I q)
    (b := ContinuousMap.const I (-e)) (fun _ => hq) (fun _ => hne') rfl rfl
    fun s t r hr => combo_ne_of_re_pos hq hqe s.2 hr
  set d := col i₀ f₂
  have hgq : rot q (-e) *ᵥ q = -e := rot_mulVec_self hq
  have hgU : rot q (-e) ∈ Matrix.unitaryGroup ι ℂ :=
    rot_mem_unitaryGroup hq hne' (one_add_herm_ne_zero hq hne' fun h => by
      have hqe' : q = e := (neg_inj.1 h).symm
      have := congrArg (fun v => (v i₀).re) hqe'
      simp only [e, Pi.single_eq_same, Complex.one_re] at this
      linarith)
  have hd : ∀ t, d t = rot q (-e) *ᵥ c' t := fun t => by
    simp only [d, col, ContinuousMap.coe_mk, hf₂, ContinuousMap.const_apply]
    rw [← Matrix.mulVec_mulVec, hcol₁]
  have hdne : ∀ t, e ≠ -d t := fun t h => by
    apply hc'q t
    apply mulVec_injective_unitary hgU
    rw [← hd, hgq, h, neg_neg]
  have hdu : ∀ t, herm (d t) (d t) = 1 := fun t => by
    rw [hd, herm_mulVec_unitary hgU, hc']
  have hd01 : d 0 = d 1 := by simp only [d, col, ContinuousMap.coe_mk, hf₂U.2]
  -- 3. contract the column to `e`
  obtain ⟨f₃, hf₃, hf₃U, hf₂f₃⟩ := homotopic_rotate hf₂U (a := d)
    (b := ContinuousMap.const I e) hdu (fun _ => he) hd01 rfl
    fun s t r hr => combo_ne_of_ne_neg (hdu t) he (hdne t) s.2 hr
  have hfix : ∀ t, f₃ t *ᵥ e = e := fun t => by
    rw [hf₃, ← Matrix.mulVec_mulVec]
    exact rot_mulVec_self (hdu t)
  have hw₃ := ((hw.of_homotopic hff₁).of_homotopic hf₁f₂).of_homotopic hf₂f₃
  exact (hff₁.trans hf₁f₂).trans (hf₂f₃.trans (homotopic_of_fix hf₃U hfix hw₃ IH))

/-- **A loop of unitary matrices on which `det` winds zero times is contractible through
loops.** -/
theorem nullHomotopic_of_windsZero {f : C(I, Matrix ι ι ℂ)} (hf : IsULoop f)
    (hw : WindsZero f) : HomotopicWith f (ContinuousMap.const I 1) IsULoop := by
  refine Finite.induction_subsingleton_or_nontrivial
    (P := fun β => ∀ [Fintype β] [DecidableEq β] (g : C(I, Matrix β β ℂ)), IsULoop g →
      WindsZero g → HomotopicWith g (ContinuousMap.const I 1) IsULoop) ι ?_ ?_ f hf hw
  · intro β _ _ _ _ g _ hwg
    exact homotopic_of_subsingleton hwg
  · intro β _ _ IH _ _ g hg hwg
    obtain ⟨i₀⟩ : Nonempty β := inferInstance
    exact homotopic_of_windsZero_step i₀ hg hwg fun g' hg' hwg' =>
      IH (Cpl i₀) (Finite.card_subtype_lt (p := fun j => ¬ j = i₀) (x := i₀) (by simp)) g' hg'
        hwg'

end Induction

end UnitaryLoops
end MorseFloer
