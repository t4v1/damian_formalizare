import MorseFloer.Part2.RhoBlockSum

/-!
# Properties of `ρ`: the unitary determinant

The last clause of Theorem 7.1.3 for the map `ρ` of `Part2/Rho.lean`: on `U(n) = Sp(2n) ∩ O(2n)`,
i.e. on the matrices `A = [[X, -Y], [Y, X]]` that are orthogonal, `ρ(A) = det(X + iY)`
(`rho_det_unitary`).

The proof does not diagonalise the unitary matrix `U = X + iY`.  The complexification
`ℂ²ⁿ = V₊ ⊕ V₋` splits into the eigenspaces of the complex structure `J` for `±i`, spanned by the
vectors `ι₊ p = (p, -ip)` and `ι₋ p = (p, ip)`; `A` acts on `V₊` as `U` and on `V₋` as `Ū`
(`M_mulVec_ιp`, `M_mulVec_ιm`), so `E_μ(A) = ι₊ E_μ(U) ⊕ ι₋ E_μ(Ū)` (`E_M_eq`).  The form `Q` is
positive definite on `V₊`, negative definite on `V₋`, and the two are orthogonal
(`GForm_ιp`, `GForm_ιm`, `GForm_ιp_ιm`), so `m₊(μ) = m_U(μ)`, the multiplicity of `μ` in `U`, and
`σ(μ) = m_U(μ) - m_U(μ̄)`.  The eigenvalues of the unitary `U` lie on the unit circle
(`norm_eq_one_of_mem_roots_unitary`), and `det U = ∏ μ^{m_U(μ)}`; grouping the eigenvalues of
`A` into the pairs `μ, μ̄` with `μ̄ = 1/μ` gives `ρ(A) = det U`.
-/

open Polynomial Matrix Module

namespace MorseFloer
namespace Rho

open Chapter7 SymplecticEigen SymplecticSpectrum EigenDecomp EigenMult HermitianIndex
  SignatureContinuity

/-! ### Generalised eigenspaces over an arbitrary index type -/

section General

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem mem_E_iff' (M : Matrix m m ℂ) (μ : ℂ) (x : m → ℂ) :
    x ∈ E M μ ↔ ∃ k : ℕ, ((M - μ • 1) ^ k) *ᵥ x = 0 := by
  rw [E, Module.End.mem_maxGenEigenspace]
  have e : ∀ k : ℕ, ((Matrix.toLin' M - μ • (1 : Module.End ℂ (m → ℂ))) ^ k) x
      = ((M - μ • 1) ^ k) *ᵥ x := by
    intro k
    have h1 : Matrix.toLin' M - μ • (1 : Module.End ℂ (m → ℂ)) = Matrix.toLin' (M - μ • 1) := by
      rw [map_sub, map_smul, Matrix.toLin'_one]
      rfl
    rw [h1, ← Matrix.toLin'_pow, Matrix.toLin'_apply]
  simp only [e]

variable {m₁ m₂ : Type*} [Fintype m₁] [DecidableEq m₁] [Fintype m₂] [DecidableEq m₂]

theorem pow_sub_mulVec_map' {M : Matrix m₁ m₁ ℂ} {M' : Matrix m₂ m₂ ℂ}
    (ι : (m₁ → ℂ) →ₗ[ℂ] (m₂ → ℂ)) (hι : ∀ x, M' *ᵥ ι x = ι (M *ᵥ x)) (μ : ℂ) (k : ℕ)
    (x : m₁ → ℂ) : ((M' - μ • 1) ^ k) *ᵥ ι x = ι (((M - μ • 1) ^ k) *ᵥ x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have h1 : (M' - μ • 1) *ᵥ ι x = ι ((M - μ • 1) *ᵥ x) := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, Matrix.one_mulVec, hι, map_sub, map_smul]
    rw [pow_succ, ← Matrix.mulVec_mulVec, pow_succ, ← Matrix.mulVec_mulVec, h1, ih]

theorem E_map_le' {M : Matrix m₁ m₁ ℂ} {M' : Matrix m₂ m₂ ℂ}
    (ι : (m₁ → ℂ) →ₗ[ℂ] (m₂ → ℂ)) (hι : ∀ x, M' *ᵥ ι x = ι (M *ᵥ x)) (μ : ℂ) :
    (E M μ).map ι ≤ E M' μ := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := (mem_E_iff' _ _ _).1 hx
  refine (mem_E_iff' _ _ _).2 ⟨k, ?_⟩
  rw [pow_sub_mulVec_map' ι hι, hk, map_zero]

omit [Fintype m₁] [DecidableEq m₁] [Fintype m₂] [DecidableEq m₂] in
theorem finrank_map_of_ker_eq_bot (T : (m₁ → ℂ) →ₗ[ℂ] (m₂ → ℂ)) (hT : LinearMap.ker T = ⊥)
    (V : Submodule ℂ (m₁ → ℂ)) : finrank ℂ (V.map T) = finrank ℂ V :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective T (LinearMap.ker_eq_bot.1 hT) V)).symm

omit [DecidableEq m] in
theorem posIndex_eq_finrank_of_posDef {G : (m → ℂ) → (m → ℂ) → ℂ} {W : Submodule ℂ (m → ℂ)}
    (h : PosDefOn G W) : posIndex G W = finrank ℂ W :=
  le_antisymm (posIndex_le_finrank _ _) (le_posIndex le_rfl h)

omit [DecidableEq m] in
theorem posIndex_eq_zero_of_nonpos {G : (m → ℂ) → (m → ℂ) → ℂ} {W : Submodule ℂ (m → ℂ)}
    (h : ∀ x ∈ W, (G x x).re ≤ 0) : posIndex G W = 0 := by
  have := posIndex_add_finrank_le (G := G) (V := W) (U := W) le_rfl h
  omega

omit [DecidableEq m] in
theorem re_dotProduct_star_self (a : m → ℂ) :
    (a ⬝ᵥ star a).re = ∑ i, Complex.normSq (a i) := by
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

omit [DecidableEq m] in
theorem re_dotProduct_star_self_pos {a : m → ℂ} (ha : a ≠ 0) : 0 < (a ⬝ᵥ star a).re := by
  rw [re_dotProduct_star_self]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩

/-- The eigenvalues of a unitary matrix lie on the unit circle. -/
theorem norm_eq_one_of_mem_roots_unitary {U : Matrix m m ℂ} (hU : star U * U = 1) {μ : ℂ}
    (hμ : μ ∈ U.charpoly.roots) : ‖μ‖ = 1 := by
  rw [mem_roots (charpoly_monic _).ne_zero, IsRoot.def, Matrix.eval_charpoly] at hμ
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hμ
  have hUw : U *ᵥ w = μ • w := by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at hw
    exact hw.symm
  have h1 : star (U *ᵥ w) ⬝ᵥ (U *ᵥ w) = star w ⬝ᵥ w := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, hU, Matrix.vecMul_one]
  rw [hUw, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    at h1
  have hne : star w ⬝ᵥ w ≠ 0 := by
    intro h
    have := re_dotProduct_star_self_pos hw0
    rw [dotProduct_comm, h, Complex.zero_re] at this
    exact lt_irrefl _ this
  have h2 : star μ * μ = 1 := by
    have := mul_right_cancel₀ hne (h1.trans (one_mul _).symm)
    exact this
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ((‖μ‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [h2]; simp
  have h4 : ‖μ‖ ^ 2 = 1 := Complex.ofReal_injective h3
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [h4, one_pow])

end General

/-! ### The unitary matrix `U = X + iY` and the splitting `ℂ²ⁿ = V₊ ⊕ V₋` -/

section Unitary

variable {n : ℕ}

/-- The first embedding, `p ↦ (p, -ip)`, onto the `i`-eigenspace of `J`. -/
def ιp (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] ((Fin n ⊕ Fin n) → ℂ) where
  toFun p := Sum.elim p (-(Complex.I • p))
  map_add' x y := by
    funext k
    rcases k with i | i
    · simp
    · simp
      ring
  map_smul' a x := by
    funext k
    rcases k with i | i
    · simp
    · simp
      ring

/-- The second embedding, `p ↦ (p, ip)`, onto the `-i`-eigenspace of `J`. -/
def ιm (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] ((Fin n ⊕ Fin n) → ℂ) where
  toFun p := Sum.elim p (Complex.I • p)
  map_add' x y := by
    funext k
    rcases k with i | i <;> simp
  map_smul' a x := by
    funext k
    rcases k with i | i
    · simp
    · simp
      ring

theorem ιp_apply (p : Fin n → ℂ) : ιp n p = Sum.elim p (-(Complex.I • p)) := rfl

theorem ιm_apply (p : Fin n → ℂ) : ιm n p = Sum.elim p (Complex.I • p) := rfl

theorem ker_ιp : LinearMap.ker (ιp n) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro p hp
  funext i
  exact congrFun hp (Sum.inl i)

theorem ker_ιm : LinearMap.ker (ιm n) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro p hp
  funext i
  exact congrFun hp (Sum.inl i)

variable (X Y : Matrix (Fin n) (Fin n) ℝ)

/-- The complexified blocks. -/
abbrev cX : Matrix (Fin n) (Fin n) ℂ := X.map Complex.ofRealHom

/-- `U = X + iY`. -/
noncomputable abbrev Umat : Matrix (Fin n) (Fin n) ℂ := cX X + Complex.I • cX Y

/-- `Ū = X - iY`. -/
noncomputable abbrev Ubar : Matrix (Fin n) (Fin n) ℂ := cX X - Complex.I • cX Y

theorem cpx_fromBlocks :
    cpx (Matrix.fromBlocks X (-Y) Y X) = Matrix.fromBlocks (cX X) (-(cX Y)) (cX Y) (cX X) := by
  rw [cpx, Matrix.fromBlocks_map]
  congr 1
  ext i j
  simp

theorem M_mulVec_ιp (p : Fin n → ℂ) :
    cpx (Matrix.fromBlocks X (-Y) Y X) *ᵥ ιp n p = ιp n (Umat X Y *ᵥ p) := by
  rw [cpx_fromBlocks, ιp_apply, ιp_apply, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.neg_mulVec, Matrix.mulVec_neg,
    Matrix.mulVec_smul, Matrix.add_mulVec, Matrix.smul_mulVec]
  funext k
  rcases k with i | i <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  · ring
  · linear_combination ((cX Y *ᵥ p) i) * Complex.I_sq

theorem M_mulVec_ιm (p : Fin n → ℂ) :
    cpx (Matrix.fromBlocks X (-Y) Y X) *ᵥ ιm n p = ιm n (Ubar X Y *ᵥ p) := by
  rw [cpx_fromBlocks, ιm_apply, ιm_apply, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.neg_mulVec, Matrix.mulVec_smul,
    Matrix.sub_mulVec, Matrix.smul_mulVec]
  funext k
  rcases k with i | i <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
  · ring
  · linear_combination ((cX Y *ᵥ p) i) * Complex.I_sq

/-- Every vector splits along `V₊ ⊕ V₋`. -/
theorem decomp (z : (Fin n ⊕ Fin n) → ℂ) :
    z = ιp n ((1 / 2 : ℂ) • (z ∘ Sum.inl + Complex.I • (z ∘ Sum.inr)))
      + ιm n ((1 / 2 : ℂ) • (z ∘ Sum.inl - Complex.I • (z ∘ Sum.inr))) := by
  funext k
  rcases k with i | i
  · simp only [ιp_apply, ιm_apply, Pi.add_apply, Sum.elim_inl, Pi.smul_apply, Pi.sub_apply,
      Function.comp_apply, smul_eq_mul]
    ring
  · simp only [ιp_apply, ιm_apply, Pi.add_apply, Sum.elim_inr, Pi.smul_apply, Pi.sub_apply,
      Pi.neg_apply, Function.comp_apply, smul_eq_mul]
    linear_combination (z (Sum.inr i)) * Complex.I_sq

/-- Two components that add up to zero in both coordinates vanish. -/
theorem eq_zero_of_ιp_add_ιm {a b : Fin n → ℂ} (h : ιp n a + ιm n b = 0) : a = 0 ∧ b = 0 := by
  have h1 : ∀ i, a i + b i = 0 := fun i => congrFun h (Sum.inl i)
  have h2 : ∀ i, -(Complex.I * a i) + Complex.I * b i = 0 := fun i => by
    have := congrFun h (Sum.inr i)
    simpa [ιp_apply, ιm_apply] using this
  constructor
  · funext i
    simp only [Pi.zero_apply]
    linear_combination (1 / 2 : ℂ) * h1 i + (Complex.I / 2) * h2 i + ((a i - b i) / 2) * Complex.I_sq
  · funext i
    simp only [Pi.zero_apply]
    linear_combination (1 / 2 : ℂ) * h1 i - (Complex.I / 2) * h2 i + ((b i - a i) / 2) * Complex.I_sq

/-- **`E_μ(A) = ι₊ E_μ(U) ⊕ ι₋ E_μ(Ū)`.** -/
theorem E_M_eq (μ : ℂ) :
    E (cpx (Matrix.fromBlocks X (-Y) Y X)) μ = (E (Umat X Y) μ).map (ιp n) ⊔ (E (Ubar X Y) μ).map (ιm n) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨k, hk⟩ := (mem_E_iff' _ _ _).1 hz
    rw [decomp z] at hk ⊢
    set a := (1 / 2 : ℂ) • (z ∘ Sum.inl + Complex.I • (z ∘ Sum.inr)) with ha
    set b := (1 / 2 : ℂ) • (z ∘ Sum.inl - Complex.I • (z ∘ Sum.inr)) with hb
    rw [Matrix.mulVec_add, pow_sub_mulVec_map' (ιp n) (M_mulVec_ιp X Y),
      pow_sub_mulVec_map' (ιm n) (M_mulVec_ιm X Y)] at hk
    obtain ⟨ha0, hb0⟩ := eq_zero_of_ιp_add_ιm hk
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem ((mem_E_iff' _ _ _).2 ⟨k, ha0⟩))
      (Submodule.mem_map_of_mem ((mem_E_iff' _ _ _).2 ⟨k, hb0⟩))
  · exact sup_le (E_map_le' (ιp n) (M_mulVec_ιp X Y) μ) (E_map_le' (ιm n) (M_mulVec_ιm X Y) μ)

theorem map_ιp_inf_map_ιm (V W : Submodule ℂ (Fin n → ℂ)) :
    V.map (ιp n) ⊓ W.map (ιm n) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Submodule.mem_inf] at hz
  obtain ⟨⟨a, -, rfl⟩, ⟨b, -, hb⟩⟩ := hz
  rw [Submodule.mem_bot]
  have h : ιp n a + ιm n (-b) = 0 := by rw [map_neg, hb, add_neg_cancel]
  rw [(eq_zero_of_ιp_add_ιm h).1, map_zero]

/-! ### The form `Q` on `V₊` and `V₋` -/

theorem negJ_mulVec_elim (c d : Fin n → ℂ) :
    (-(Matrix.J (Fin n) ℂ)) *ᵥ Sum.elim c d = Sum.elim d (-c) := by
  rw [Matrix.J, Matrix.fromBlocks_neg, Matrix.fromBlocks_mulVec]
  funext k
  rcases k with i | i <;> simp [Matrix.neg_mulVec]

theorem conjVec_elim' (b c : Fin n → ℂ) :
    conjVec (Sum.elim b c) = Sum.elim (star b) (star c) := by
  funext k
  rcases k with i | i <;> simp [conjVec]

theorem GForm_elim' (a a' b b' : Fin n → ℂ) :
    GForm (Sum.elim a a') (Sum.elim b b')
      = -Complex.I * (a ⬝ᵥ star b' - a' ⬝ᵥ star b) := by
  rw [GForm, HForm, stdFormC_apply, conjVec_elim', negJ_mulVec_elim, sumElim_dotProduct_sumElim,
    dotProduct_neg, sub_eq_add_neg]

theorem GForm_ιp (a b : Fin n → ℂ) : GForm (ιp n a) (ιp n b) = 2 * (a ⬝ᵥ star b) := by
  rw [ιp_apply, ιp_apply, GForm_elim']
  simp only [star_neg, star_smul, Complex.star_def, Complex.conj_I, neg_smul, neg_neg,
    dotProduct_smul, neg_dotProduct, smul_dotProduct, smul_eq_mul]
  linear_combination (-2 * (a ⬝ᵥ star b)) * Complex.I_sq

theorem GForm_ιm (a b : Fin n → ℂ) : GForm (ιm n a) (ιm n b) = -2 * (a ⬝ᵥ star b) := by
  rw [ιm_apply, ιm_apply, GForm_elim']
  simp only [star_smul, Complex.star_def, Complex.conj_I, neg_smul, dotProduct_smul,
    smul_dotProduct, dotProduct_neg, smul_eq_mul]
  linear_combination (2 * (a ⬝ᵥ star b)) * Complex.I_sq

theorem GForm_ιp_ιm (a b : Fin n → ℂ) : GForm (ιp n a) (ιm n b) = 0 := by
  rw [ιp_apply, ιm_apply, GForm_elim']
  simp only [star_smul, Complex.star_def, Complex.conj_I, neg_smul, dotProduct_smul,
    neg_dotProduct, smul_dotProduct, dotProduct_neg, smul_eq_mul]
  ring

/-- **`m₊(μ) = m_U(μ)`.** -/
theorem mPos_eq_count (μ : ℂ) :
    mPos (cpx (Matrix.fromBlocks X (-Y) Y X)) μ = finrank ℂ (E (Umat X Y) μ) := by
  rw [mPos, E_M_eq, posIndex_sup isHermForm_GForm (map_ιp_inf_map_ιm _ _)
    (by rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩; exact GForm_ιp_ιm a b)]
  have h1 : posIndex GForm ((E (Umat X Y) μ).map (ιp n)) = finrank ℂ (E (Umat X Y) μ) := by
    rw [posIndex_eq_finrank_of_posDef, finrank_map_of_ker_eq_bot _ ker_ιp]
    rintro _ ⟨a, -, rfl⟩ hne
    have ha : a ≠ 0 := fun h => hne (by rw [h, map_zero])
    rw [GForm_ιp, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    linarith [re_dotProduct_star_self_pos ha]
  have h2 : posIndex GForm ((E (Ubar X Y) μ).map (ιm n)) = 0 := by
    refine posIndex_eq_zero_of_nonpos ?_
    rintro _ ⟨a, -, rfl⟩
    rw [GForm_ιm]
    have : (-2 * (a ⬝ᵥ star a)).re = -2 * (a ⬝ᵥ star a).re := by
      rw [show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    rw [this, re_dotProduct_star_self]
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => Complex.normSq_nonneg (a i)
    linarith
  rw [h1, h2, add_zero]

/-! ### The spectra of `A`, `U` and `Ū` -/

open Classical in
theorem count_roots_M (μ : ℂ) :
    (cpx (Matrix.fromBlocks X (-Y) Y X)).charpoly.roots.count μ
      = (Umat X Y).charpoly.roots.count μ + (Ubar X Y).charpoly.roots.count μ := by
  rw [← finrank_E, ← finrank_E, ← finrank_E, E_M_eq]
  have h := Submodule.finrank_sup_add_finrank_inf_eq ((E (Umat X Y) μ).map (ιp n))
    ((E (Ubar X Y) μ).map (ιm n))
  rw [map_ιp_inf_map_ιm, finrank_bot, add_zero, finrank_map_of_ker_eq_bot _ ker_ιp,
    finrank_map_of_ker_eq_bot _ ker_ιm] at h
  exact h

theorem Ubar_eq_map : Ubar X Y = (Umat X Y).map (starRingEnd ℂ) := by
  ext i j
  simp [sub_eq_add_neg]

theorem roots_Ubar :
    (Ubar X Y).charpoly.roots = (Umat X Y).charpoly.roots.map (starRingEnd ℂ) := by
  rw [Ubar_eq_map, Matrix.charpoly_map,
    ← roots_map_of_injective_of_card_eq_natDegree (RingHom.injective _)
      IsAlgClosed.card_roots_eq_natDegree]

open Classical in
theorem count_roots_Ubar (μ : ℂ) :
    (Ubar X Y).charpoly.roots.count μ = (Umat X Y).charpoly.roots.count (starRingEnd ℂ μ) := by
  rw [roots_Ubar]
  conv_lhs => rw [← Complex.conj_conj μ]
  exact Multiset.count_map_eq_count' _ _ (RingHom.injective _) _

open Classical in
theorem sigma_M (μ : ℂ) :
    sigma (cpx (Matrix.fromBlocks X (-Y) Y X)) μ
      = ((Umat X Y).charpoly.roots.count μ : ℤ)
        - ((Umat X Y).charpoly.roots.count (starRingEnd ℂ μ) : ℤ) := by
  unfold sigma
  rw [mPos_eq_count, finrank_E, count_roots_M, count_roots_Ubar]
  push_cast
  ring

theorem roots_M_eq :
    (cpx (Matrix.fromBlocks X (-Y) Y X)).charpoly.roots
      = (Umat X Y).charpoly.roots + (Umat X Y).charpoly.roots.map (starRingEnd ℂ) := by
  classical
  ext μ
  rw [Multiset.count_add, count_roots_M, ← roots_Ubar, count_roots_Ubar, ← count_roots_Ubar]

/-! ### Orthogonality makes `U` unitary -/

theorem conjTranspose_cX : (cX X)ᴴ = cX Xᵀ := by
  ext i j
  simp

theorem star_U_mul_U (hO : Chapter5.IsOrthogonalMat (Matrix.fromBlocks X (-Y) Y X)) :
    star (Umat X Y) * Umat X Y = 1 := by
  have h := hO
  unfold Chapter5.IsOrthogonalMat at h
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_inj] at h
  obtain ⟨h11, h12, -, -⟩ := h
  have e1 : cX Xᵀ * cX X + cX Yᵀ * cX Y = 1 := by
    have := congrArg (RingHom.mapMatrix Complex.ofRealHom) h11
    simp only [map_add, map_mul, map_one, RingHom.mapMatrix_apply] at this
    exact this
  have e2 : cX Xᵀ * cX Y = cX Yᵀ * cX X := by
    have := congrArg (RingHom.mapMatrix Complex.ofRealHom) h12
    simp only [map_add, map_mul, map_neg, map_zero, RingHom.mapMatrix_apply, Matrix.mul_neg]
      at this
    exact neg_add_eq_zero.1 this
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    conjTranspose_cX, conjTranspose_cX, Complex.star_def, Complex.conj_I]
  have key : (cX Xᵀ + -Complex.I • cX Yᵀ) * (cX X + Complex.I • cX Y)
      = (cX Xᵀ * cX X + cX Yᵀ * cX Y) + Complex.I • (cX Xᵀ * cX Y - cX Yᵀ * cX X) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    simp only [neg_smul, smul_sub]
    abel
  rw [key, e1, e2, sub_self, smul_zero, add_zero]

/-! ### `ρ(A) = det U` -/

theorem norm_eq_one_of_mem_roots_M (hO : Chapter5.IsOrthogonalMat (Matrix.fromBlocks X (-Y) Y X))
    {μ : ℂ} (hμ : μ ∈ (cpx (Matrix.fromBlocks X (-Y) Y X)).charpoly.roots) : ‖μ‖ = 1 := by
  rw [roots_M_eq, Multiset.mem_add] at hμ
  rcases hμ with h | h
  · exact norm_eq_one_of_mem_roots_unitary (star_U_mul_U X Y hO) h
  · obtain ⟨ν, hν, rfl⟩ := Multiset.mem_map.1 h
    rw [Complex.norm_conj]
    exact norm_eq_one_of_mem_roots_unitary (star_U_mul_U X Y hO) hν

theorem eq_one_or_neg_one_of_im_eq_zero {μ : ℂ} (hμ : ‖μ‖ = 1) (him : μ.im = 0) :
    μ = 1 ∨ μ = -1 := by
  have e : μ = (μ.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [e, Complex.norm_real, Real.norm_eq_abs] at hμ
  rcases (abs_eq (zero_le_one' ℝ)).1 hμ with h | h
  · left; rw [e, h]; simp
  · right; rw [e, h]; simp

open Classical in
/-- **The unitary determinant: `ρ(A) = det(X + iY)` on `U(n)`** (Theorem 7.1.3). -/
theorem rhoC_eq_det (hO : Chapter5.IsOrthogonalMat (Matrix.fromBlocks X (-Y) Y X)) :
    rhoC (cpx (Matrix.fromBlocks X (-Y) Y X)) = (Umat X Y).det := by
  set M := cpx (Matrix.fromBlocks X (-Y) Y X) with hMdef
  set S := (Umat X Y).charpoly.roots with hS
  set g : ℂ → ℂ := fun μ => μ ^ S.count μ with hg
  have hcirc : ∀ μ ∈ M.charpoly.roots, ‖μ‖ = 1 := fun μ hμ => norm_eq_one_of_mem_roots_M X Y hO hμ
  have hconj_mem : ∀ μ, starRingEnd ℂ μ ∈ M.charpoly.roots ↔ μ ∈ M.charpoly.roots := by
    intro μ
    constructor
    · intro h
      rw [← roots_map_conj (Matrix.fromBlocks X (-Y) Y X)] at h
      obtain ⟨ν, hν, hνμ⟩ := Multiset.mem_map.1 h
      have : ν = μ := by
        have := congrArg (starRingEnd ℂ) hνμ
        rwa [Complex.conj_conj, Complex.conj_conj] at this
      rwa [← this]
    · intro h
      rw [← roots_map_conj (Matrix.fromBlocks X (-Y) Y X)]
      exact Multiset.mem_map_of_mem _ h
  -- `det U` as a product over the distinct eigenvalues of `A`
  have hdet : (Umat X Y).det = ∏ μ ∈ M.charpoly.roots.toFinset, g μ := by
    rw [Matrix.det_eq_prod_roots_charpoly, ← hS, Finset.prod_multiset_count]
    refine Finset.prod_subset (fun μ hμ => ?_) fun μ _ hμ => ?_
    · rw [Multiset.mem_toFinset] at hμ ⊢
      rw [roots_M_eq, Multiset.mem_add]
      exact Or.inl hμ
    · show μ ^ S.count μ = 1
      rw [Multiset.count_eq_zero.2 (fun h => hμ (Multiset.mem_toFinset.2 h)), pow_zero]
  rw [hdet, rhoC]
  -- split both products along the sign of the imaginary part
  have hsplit : ∀ f : ℂ → ℂ, ∏ μ ∈ M.charpoly.roots.toFinset, f μ
      = (∏ μ ∈ M.charpoly.roots.toFinset.filter (fun z => 0 < z.im), f μ)
        * (∏ μ ∈ M.charpoly.roots.toFinset.filter (fun z => z.im < 0), f μ)
        * ∏ μ ∈ M.charpoly.roots.toFinset.filter (fun z => z.im = 0), f μ := by
    intro f
    rw [← Finset.prod_filter_mul_prod_filter_not M.charpoly.roots.toFinset (fun z => 0 < z.im),
      ← Finset.prod_filter_mul_prod_filter_not (M.charpoly.roots.toFinset.filter
        (fun z => ¬0 < z.im)) (fun z => z.im < 0), Finset.filter_filter, Finset.filter_filter,
      mul_assoc]
    congr 1
    congr 1
    · exact Finset.prod_congr (Finset.filter_congr fun z _ =>
        ⟨fun h => h.2, fun h => ⟨by linarith, h⟩⟩) fun _ _ => rfl
    · exact Finset.prod_congr (Finset.filter_congr fun z _ =>
        ⟨fun h => le_antisymm (not_lt.1 h.1) (not_lt.1 h.2),
          fun h => ⟨by rw [h]; exact lt_irrefl _, by rw [h]; exact lt_irrefl _⟩⟩) fun _ _ => rfl
  rw [hsplit, hsplit g]
  -- the negative half is the conjugate of the positive half
  have himage : (M.charpoly.roots.toFinset.filter (fun z => 0 < z.im)).image (starRingEnd ℂ)
      = M.charpoly.roots.toFinset.filter (fun z => z.im < 0) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter, Multiset.mem_toFinset]
    constructor
    · rintro ⟨w, ⟨hw, hw0⟩, rfl⟩
      exact ⟨(hconj_mem w).2 hw, by rw [Complex.conj_im]; linarith⟩
    · rintro ⟨hz, hz0⟩
      refine ⟨starRingEnd ℂ z, ⟨(hconj_mem z).2 hz, by rw [Complex.conj_im]; linarith⟩, ?_⟩
      rw [Complex.conj_conj]
  have hneg : ∏ μ ∈ M.charpoly.roots.toFinset.filter (fun z => z.im < 0), g μ
      = ∏ μ ∈ M.charpoly.roots.toFinset.filter (fun z => 0 < z.im), g (starRingEnd ℂ μ) := by
    rw [← himage, Finset.prod_image (fun _ _ _ _ h => (RingHom.injective _) h)]
  rw [hneg]
  -- the factors on the negative half are `1`
  have hnegf : ∏ μ ∈ M.charpoly.roots.toFinset.filter (fun z => z.im < 0), factor M μ = 1 := by
    refine Finset.prod_eq_one fun μ hμ => ?_
    rw [Finset.mem_filter] at hμ
    refine factor_eq_one (fun h => by linarith [h.2, hμ.2]) (fun h => ?_) (fun h => by linarith [h.1, hμ.2])
    rw [h] at hμ
    simp at hμ
  rw [hnegf, mul_one, ← Finset.prod_mul_distrib]
  congr 1
  · -- the positive half: `μ^{σ(μ)} = μ^{m_U(μ)} μ̄^{m_U(μ̄)}`
    refine Finset.prod_congr rfl fun μ hμ => ?_
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hμ
    have hμ1 : ‖μ‖ = 1 := hcirc μ hμ.1
    rw [factor_of_circle ⟨hμ1, hμ.2⟩, sigma_M, hg]
    show μ ^ ((S.count μ : ℤ) - (S.count (starRingEnd ℂ μ) : ℤ))
      = μ ^ S.count μ * (starRingEnd ℂ μ) ^ S.count (starRingEnd ℂ μ)
    have hμ0 : μ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hμ1
      exact zero_ne_one hμ1
    rw [zpow_sub₀ hμ0, zpow_natCast, zpow_natCast, ← inv_eq_conj_of_norm_one hμ1, inv_pow,
      div_eq_mul_inv]
  · -- the real eigenvalues: `±1`
    refine Finset.prod_congr rfl fun μ hμ => ?_
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hμ
    have hμ1 : ‖μ‖ = 1 := hcirc μ hμ.1
    rcases eq_one_or_neg_one_of_im_eq_zero hμ1 hμ.2 with h | h
    · rw [h, hg]
      show factor M 1 = 1 ^ S.count 1
      rw [one_pow]
      exact factor_eq_one (by simp) (by norm_num) (by simp)
    · rw [h, factor_neg_one, hg]
      show (-1 : ℂ) ^ (M.charpoly.roots.count (-1) / 2) = (-1) ^ S.count (-1)
      rw [count_roots_M, count_roots_Ubar]
      congr 1
      have : starRingEnd ℂ (-1 : ℂ) = -1 := by simp
      rw [this, hS]
      omega

/-- **Theorem 7.1.3, the determinant clause**: on `U(n)`, `ρ(A) = det(X + iY)`. -/
theorem rho_det_unitary (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℝ)
    (hO : Chapter5.IsOrthogonalMat (Matrix.fromBlocks X (-Y) Y X)) :
    rho n (Matrix.fromBlocks X (-Y) Y X)
      = (X.map (fun r : ℝ => (r : ℂ)) + Complex.I • Y.map (fun r : ℝ => (r : ℂ))).det :=
  rhoC_eq_det X Y hO

end Unitary

end Rho
end MorseFloer
