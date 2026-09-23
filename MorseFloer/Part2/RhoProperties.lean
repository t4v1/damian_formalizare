import MorseFloer.Part2.Rho

/-!
# Properties of `ρ`: the norm and the inverse

Two clauses of Theorem 7.1.3 for the map `ρ` of `Part2/Rho.lean`: `ρ` takes its values in the
unit circle (`norm_rho`), every factor having norm one; and `ρ(A⁻¹) = conj ρ(A)` (`rho_inv`).
The second rests on three facts about a symplectic `A`: `cpx A⁻¹ = (cpx A)⁻¹`; the
characteristic polynomial of `A⁻¹` is that of `A` (the spectrum is stable under inversion,
`charpoly_cpx_inv`); and the generalised eigenspace of `A⁻¹` at `μ` is that of `A` at `1/μ`
(`E_cpx_inv`).  So the factor of `μ` in `ρ(A⁻¹)` is `μ^{σ(μ̄)}` on the circle, and it remains to
know that `σ(μ̄) = -σ(μ)` — Remark 5.6.8: conjugation `X ↦ X̄` maps `E_μ` onto `E_μ̄` and
changes the sign of `Q`, so it exchanges the positive and negative parts
(`posIndex_add_posIndex_star`, a general statement about Hermitian forms, and `mPos_conj_add`).
-/

open Polynomial Matrix Module

namespace MorseFloer
namespace Rho

open Chapter7 SymplecticEigen SymplecticSpectrum EigenDecomp EigenMult HermitianIndex
  SignatureContinuity

/-! ### The norm -/

variable {l : Type*} [DecidableEq l] [Fintype l]

theorem norm_factor (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) : ‖factor M μ‖ = 1 := by
  unfold factor
  split_ifs with h1 h2 h3
  · rw [norm_zpow, h1.1, _root_.one_zpow]
  · rw [norm_pow, norm_neg, norm_one, one_pow]
  · rw [norm_pow, norm_neg, norm_one, one_pow]
  · exact norm_one

theorem norm_rhoC (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) : ‖rhoC M‖ = 1 := by
  rw [rhoC, Complex.norm_prod]
  exact Finset.prod_eq_one fun μ _ => norm_factor M μ

/-- **`ρ` takes its values in the unit circle** (Theorem 7.1.3). -/
theorem norm_rho (n : ℕ) (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) : ‖rho n A‖ = 1 :=
  norm_rhoC _

/-! ### Conjugation exchanges the positive and negative parts -/

section Star

variable {m : Type*} [Fintype m]

omit [Fintype m] in
theorem star_sum_smul {k : ℕ} (c : Fin k → ℂ) (f : Fin k → (m → ℂ)) :
    star (∑ j, c j • f j) = ∑ j, starRingEnd ℂ (c j) • star (f j) := by
  funext i
  simp [Finset.sum_apply, Pi.star_apply, star_sum, star_mul']

/-- If `star` maps `V` onto `W` and `G(x̄, ȳ) = -conj G(x, y)`, then the positive index of `G`
on `W` is the negative index of `G` on `V`: for `G` nondegenerate on `V`, the two positive
indices add up to `dim V`. -/
theorem posIndex_add_posIndex_star {G : (m → ℂ) → (m → ℂ) → ℂ} (hG : IsHermForm G)
    (hstar : ∀ x y, G (star x) (star y) = -starRingEnd ℂ (G x y))
    {V W : Submodule ℂ (m → ℂ)} (hVW : ∀ x ∈ V, star x ∈ W) (hWV : ∀ y ∈ W, star y ∈ V)
    (hnd : ∀ v ∈ V, (∀ w ∈ V, G v w = 0) → v = 0) :
    posIndex G W + posIndex G V = finrank ℂ V := by
  classical
  obtain ⟨e, he, heV⟩ := exists_basis_family V
  obtain ⟨f, d, hf, hfspan, hre, -, hdet⟩ := exists_eigen_family hG he heV
  have hfV : ∀ j, f j ∈ V := fun j => hfspan ▸ Submodule.subset_span ⟨j, rfl⟩
  -- the conjugate family
  set f' : Fin (finrank ℂ V) → (m → ℂ) := fun j => star (f j) with hf'
  have hf'_indep : LinearIndependent ℂ f' := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : ∑ j, starRingEnd ℂ (c j) • f j = 0 := by
      have := congrArg star hc
      rw [star_sum_smul, star_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hf', star_star]
    intro j
    exact (_root_.map_eq_zero _).1 (Fintype.linearIndependent_iff.1 hf _ h1 j)
  have hf'_span : Submodule.span ℂ (Set.range f') = W := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hVW _ (hfV j))
    · intro y hy
      have : star y ∈ Submodule.span ℂ (Set.range f) := by rw [hfspan]; exact hWV y hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 this
      have e : y = ∑ j, starRingEnd ℂ (c j) • f' j := by
        rw [hf']
        show y = ∑ j, starRingEnd ℂ (c j) • star (f j)
        rw [← star_sum_smul, hc, star_star]
      rw [e]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hre' : ∀ c : Fin (finrank ℂ V) → ℂ,
      (G (∑ j, c j • f' j) (∑ j, c j • f' j)).re = ∑ j, ‖c j‖ ^ 2 * (-d j) := by
    intro c
    have e : ∑ j, c j • f' j = star (∑ j, starRingEnd ℂ (c j) • f j) := by
      rw [star_sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.conj_conj, hf']
    rw [e, hstar, Complex.neg_re, Complex.conj_re, hre, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.norm_conj]
    ring
  have hd : ∀ j, d j ≠ 0 := by
    intro j hj
    apply det_gram_ne_zero hG he heV hnd
    rw [hdet]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  rw [posIndex_eq_card_of_family hf'_indep hf'_span hre', posIndex_eq_card_of_family hf hfspan hre]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (finrank ℂ V)))) (fun j => 0 < d j)
  have h' : (Finset.univ.filter fun j => 0 < -d j) = Finset.univ.filter fun j => ¬0 < d j := by
    apply Finset.filter_congr
    intro j _
    rw [neg_pos, not_lt]
    exact ⟨fun h1 => h1.le, fun h1 => lt_of_le_of_ne h1 (hd j)⟩
  rw [h', add_comm, h, Finset.card_univ, Fintype.card_fin]

end Star

theorem GForm_star (X Y : (l ⊕ l) → ℂ) :
    GForm (star X) (star Y) = -starRingEnd ℂ (GForm X Y) := by
  rw [GForm, GForm, HForm, HForm, ← conjVec_eq_star, ← conjVec_eq_star, conjVec_conjVec,
    map_mul, map_neg, Complex.conj_I, ← stdFormC_conjVec, conjVec_conjVec]
  ring

omit [DecidableEq l] [Fintype l] in
theorem cpx_map_conj (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    (cpx A).map (starRingEnd ℂ) = cpx A := by
  rw [cpx, Matrix.map_map]
  congr 1
  funext x
  simp

omit [Fintype l] in
theorem sub_smul_one_map_conj (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) (μ : ℂ) :
    (cpx A - μ • (1 : Matrix (l ⊕ l) (l ⊕ l) ℂ)).map (starRingEnd ℂ)
      = cpx A - starRingEnd ℂ μ • 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [cpx]
  · simp [cpx, h]

/-- Conjugation maps `E_μ(A)` into `E_μ̄(A)`. -/
theorem inGen_star {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} {μ : ℂ} {k : ℕ} {X : (l ⊕ l) → ℂ}
    (h : InGen (cpx A) μ k X) : InGen (cpx A) (starRingEnd ℂ μ) k (star X) := by
  unfold InGen at *
  have e : (cpx A - starRingEnd ℂ μ • (1 : Matrix (l ⊕ l) (l ⊕ l) ℂ)) ^ k
      = ((cpx A - μ • 1) ^ k).map (starRingEnd ℂ) := by
    rw [← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply, sub_smul_one_map_conj]
  have e2 : ((cpx A - μ • 1) ^ k).map (starRingEnd ℂ) *ᵥ star X
      = star (((cpx A - μ • 1) ^ k) *ᵥ X) := by
    funext i
    exact (RingHom.map_mulVec (starRingEnd ℂ) _ X i).symm
  rw [e, e2, h, star_zero]

theorem mem_E_star_iff {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} {μ : ℂ} {X : (l ⊕ l) → ℂ} :
    X ∈ E (cpx A) μ ↔ star X ∈ E (cpx A) (starRingEnd ℂ μ) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (mem_E_iff _ _ _).1 h
    exact (mem_E_iff _ _ _).2 ⟨k, inGen_star hk⟩
  · intro h
    obtain ⟨k, hk⟩ := (mem_E_iff _ _ _).1 h
    have := inGen_star hk
    rw [star_star, Complex.conj_conj] at this
    exact (mem_E_iff _ _ _).2 ⟨k, this⟩

theorem inv_conj_of_norm_one {μ : ℂ} (h : ‖μ‖ = 1) : (starRingEnd ℂ μ)⁻¹ = μ := by
  have h1 : μ * starRingEnd ℂ μ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
    norm_num
  exact (eq_inv_of_mul_eq_one_left h1).symm

theorem inv_eq_conj_of_norm_one {μ : ℂ} (h : ‖μ‖ = 1) : μ⁻¹ = starRingEnd ℂ μ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

open Classical in
/-- **Remark 5.6.8, for the indices.**  On the unit circle, `m₊(μ̄) + m₊(μ) = m(μ)`, i.e.
`m₊(μ̄) = m₋(μ)`. -/
theorem mPos_conj_add {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    {μ : ℂ} (hμ : ‖μ‖ = 1) :
    mPos (cpx A) (starRingEnd ℂ μ) + mPos (cpx A) μ = (cpx A).charpoly.roots.count μ := by
  rw [mPos, mPos, ← finrank_E]
  refine posIndex_add_posIndex_star isHermForm_GForm GForm_star
    (fun x hx => mem_E_star_iff.1 hx) (fun y hy => ?_) ?_
  · have := (mem_E_star_iff (μ := starRingEnd ℂ μ)).1 hy
    rwa [Complex.conj_conj] at this
  · intro v hv h
    rw [← kerAeval_pow_count, ← fS_eq_pow_count] at hv h
    refine eq_zero_of_mem_kerAeval_fS_of_forall (· = μ) (HForm_cpx hA) ?_ hv fun w hw => ?_
    · rintro z _ rfl
      exact inv_conj_of_norm_one hμ
    · rw [← GForm_eq_zero_iff]
      exact h w hw

open Classical in
theorem sigma_conj {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    {μ : ℂ} (hμ : ‖μ‖ = 1) : sigma (cpx A) (starRingEnd ℂ μ) = -sigma (cpx A) μ := by
  unfold sigma
  rw [count_conj]
  have := mPos_conj_add hA hμ
  omega

/-! ### The inverse -/

theorem isUnit_det_cpx {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    IsUnit (cpx A).det := by
  rw [det_cpx_eq_one hA]
  exact isUnit_one

theorem cpx_inv {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    cpx A⁻¹ = (cpx A)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  have hdet : IsUnit A.det := by
    rw [SymplecticGroup.det_eq_one hA]
    exact isUnit_one
  rw [cpx, cpx, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem det_cpx_inv {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    (cpx A)⁻¹.det = 1 := by
  rw [Matrix.det_nonsing_inv, det_cpx_eq_one hA, Ring.inverse_one]

/-- **The spectrum of `A⁻¹` is that of `A`**, with multiplicities. -/
theorem charpoly_cpx_inv {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    (cpx A)⁻¹.charpoly = (cpx A).charpoly := by
  refine eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono ?_)
  intro t ht
  rw [Set.mem_compl_singleton_iff] at ht
  show eval t _ = eval t _
  rw [charpoly_eval_inv hA ht, charpoly_eval, charpoly_eval]
  have e : (cpx A)⁻¹ - t • (1 : Matrix (l ⊕ l) (l ⊕ l) ℂ)
      = (-t) • ((cpx A)⁻¹ * (cpx A - t⁻¹ • 1)) := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ (isUnit_det_cpx hA), Matrix.mul_smul,
      Matrix.mul_one, smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ ht]
    simp only [neg_smul, one_smul]
    abel
  rw [e, Matrix.det_smul, Matrix.det_mul, det_cpx_inv hA, one_mul, even_card.neg_pow]

/-- **`E_μ(A⁻¹) = E_{1/μ}(A)`.** -/
theorem E_cpx_inv {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ) {μ : ℂ}
    (hμ : μ ≠ 0) : E (cpx A)⁻¹ μ = E (cpx A) μ⁻¹ := by
  set M := cpx A with hM
  have hunit := isUnit_det_cpx hA
  have e1 : ((-μ) • M⁻¹) * (M - μ⁻¹ • 1) = M⁻¹ - μ • 1 := by
    rw [Matrix.smul_mul, Matrix.mul_sub, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_smul,
      Matrix.mul_one, smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hμ]
    simp only [neg_smul, one_smul]
    abel
  have e1' : (M - μ⁻¹ • 1) * ((-μ) • M⁻¹) = M⁻¹ - μ • 1 := by
    rw [Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_nonsing_inv _ hunit, Matrix.smul_mul,
      Matrix.one_mul, smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hμ]
    simp only [neg_smul, one_smul]
    abel
  have hcomm : Commute ((-μ) • M⁻¹) (M - μ⁻¹ • 1) := e1.trans e1'.symm
  have e : ∀ k : ℕ, (M⁻¹ - μ • 1) ^ k = ((-μ) ^ k • M⁻¹ ^ k) * (M - μ⁻¹ • 1) ^ k := by
    intro k
    rw [← e1, hcomm.mul_pow, _root_.smul_pow]
  have hkill : ∀ (k : ℕ) (Y : (l ⊕ l) → ℂ), M⁻¹ ^ k *ᵥ Y = 0 → Y = 0 := by
    intro k Y hY
    have hk : IsUnit (M ^ k).det := by
      rw [Matrix.det_pow]
      exact hunit.pow k
    calc Y = (M ^ k * M⁻¹ ^ k) *ᵥ Y := by
          rw [Matrix.inv_pow', Matrix.mul_nonsing_inv _ hk, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hY, Matrix.mulVec_zero]
  ext X
  rw [mem_E_iff, mem_E_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    unfold InGen at *
    rw [e, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, smul_eq_zero] at hk
    rcases hk with hk | hk
    · exact absurd hk (pow_ne_zero _ (neg_ne_zero.2 hμ))
    · exact hkill k _ hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    unfold InGen at *
    rw [e, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_zero]

open Classical in
theorem sigma_cpx_inv {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    {μ : ℂ} (hμ : μ ≠ 0) : sigma (cpx A)⁻¹ μ = sigma (cpx A) μ⁻¹ := by
  unfold sigma mPos
  rw [E_cpx_inv hA hμ, charpoly_cpx_inv hA, count_inv hA]

open Classical in
theorem factor_cpx_inv {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    {μ : ℂ} (hμ : μ ≠ 0) : factor (cpx A)⁻¹ μ = starRingEnd ℂ (factor (cpx A) μ) := by
  unfold factor
  rw [charpoly_cpx_inv hA]
  split_ifs with h1 h2 h3
  · have hz : ‖μ ^ sigma (cpx A) μ‖ = 1 := by rw [norm_zpow, h1.1, _root_.one_zpow]
    rw [sigma_cpx_inv hA hμ, inv_eq_conj_of_norm_one h1.1, sigma_conj hA h1.1, _root_.zpow_neg,
      ← inv_eq_conj_of_norm_one hz]
  · rw [map_pow, map_neg, map_one]
  · rw [map_pow, map_neg, map_one]
  · rw [map_one]

theorem rhoC_cpx_inv {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    rhoC (cpx A)⁻¹ = starRingEnd ℂ (rhoC (cpx A)) := by
  classical
  rw [rhoC, rhoC, charpoly_cpx_inv hA, map_prod]
  refine Finset.prod_congr rfl fun μ hμ => ?_
  have hμ0 : μ ≠ 0 := fun h => zero_notMem_roots hA (h ▸ Multiset.mem_toFinset.1 hμ)
  exact factor_cpx_inv hA hμ0

/-- **`ρ(A⁻¹) = conj ρ(A)`** (Theorem 7.1.3). -/
theorem rho_inv (n : ℕ) {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ) : rho n A⁻¹ = starRingEnd ℂ (rho n A) := by
  rw [rho, rho, cpx_inv hA, rhoC_cpx_inv hA]

end Rho
end MorseFloer
