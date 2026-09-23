import Mathlib

/-!
# The positive index of a Hermitian form on a complex subspace

A brick for the map `ρ` of Chapter 7: the numbers `m₊(λ)`, `m₋(λ)` of §7.3.b are the maximal
complex dimensions of subspaces of the generalised eigenspace `E_λ` on which the form `Q` is
positive, resp. negative, definite.  This file defines that index intrinsically for a Hermitian
sesquilinear form `G` on `ℂᵐ` restricted to a subspace `V` (`posIndex`), and proves the
uniqueness part of **Sylvester's law of inertia** for it: for any basis of `V`, the index is the
number of positive eigenvalues of the Gram matrix of `G` (`posIndex_eq_countP`), read as the
number of roots of its characteristic polynomial with positive real part.  That is the form in
which the continuity of `ρ` is proved: the Gram matrix of a continuously varying basis is
continuous, and the count of its roots in a half-plane is locally constant.

The argument is Mathlib's for real quadratic forms (`QuadraticForm.sigPos`), redone for
Hermitian forms: the index plus the dimension of any nonpositive subspace is at most the
dimension of the space, and the orthonormal eigenvector basis of the Gram matrix produces a
positive subspace and a nonpositive one of the right dimensions.
-/

open Matrix Module

namespace MorseFloer
namespace HermitianIndex

variable {m : Type*}

/-- A Hermitian sesquilinear form on `m → ℂ`, linear in the first slot. -/
structure IsHermForm (G : (m → ℂ) → (m → ℂ) → ℂ) : Prop where
  add_left : ∀ x y z, G (x + y) z = G x z + G y z
  smul_left : ∀ (a : ℂ) (x y), G (a • x) y = a * G x y
  conj_symm : ∀ x y, G y x = starRingEnd ℂ (G x y)

namespace IsHermForm

variable {G : (m → ℂ) → (m → ℂ) → ℂ} (hG : IsHermForm G)
include hG

theorem add_right (x y z : m → ℂ) : G x (y + z) = G x y + G x z := by
  rw [hG.conj_symm, hG.add_left, map_add, ← hG.conj_symm, ← hG.conj_symm]

theorem smul_right (a : ℂ) (x y : m → ℂ) : G x (a • y) = starRingEnd ℂ a * G x y := by
  rw [hG.conj_symm, hG.smul_left, map_mul, ← hG.conj_symm]

theorem zero_left (y : m → ℂ) : G 0 y = 0 := by
  have := hG.add_left 0 0 y
  rw [add_zero] at this
  linear_combination -this

theorem zero_right (x : m → ℂ) : G x 0 = 0 := by
  rw [hG.conj_symm, hG.zero_left, map_zero]

theorem sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → (m → ℂ)) (y : m → ℂ) :
    G (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * G (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hG.zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hG.add_left, hG.smul_left, ih]

theorem sum_right {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → (m → ℂ)) (x : m → ℂ) :
    G x (∑ i ∈ s, c i • v i) = ∑ i ∈ s, starRingEnd ℂ (c i) * G x (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hG.zero_right]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hG.add_right, hG.smul_right, ih]

/-- `G x x` is real. -/
theorem im_self (x : m → ℂ) : (G x x).im = 0 := by
  have := hG.conj_symm x x
  have h := congrArg Complex.im this
  rw [Complex.conj_im] at h
  linarith

end IsHermForm

/-- `G` is positive definite on the subspace `W`. -/
def PosDefOn (G : (m → ℂ) → (m → ℂ) → ℂ) (W : Submodule ℂ (m → ℂ)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → 0 < (G x x).re

variable [Fintype m]

open scoped Classical in
/-- The positive index of `G` on `V`: the maximal dimension of a subspace of `V` on which `G` is
positive definite. -/
noncomputable def posIndex (G : (m → ℂ) → (m → ℂ) → ℂ) (V : Submodule ℂ (m → ℂ)) : ℕ :=
  ((Finset.range (finrank ℂ V + 1)).filter fun r =>
    ∃ W : Submodule ℂ (m → ℂ), W ≤ V ∧ finrank ℂ W = r ∧ PosDefOn G W).max'
    ⟨0, by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_range.2 (Nat.succ_pos _), ⊥, bot_le, finrank_bot ℂ (m → ℂ), ?_⟩
      intro x hx hx0
      exact absurd ((Submodule.mem_bot ℂ).1 hx) hx0⟩

open scoped Classical in
theorem le_posIndex {G : (m → ℂ) → (m → ℂ) → ℂ} {V W : Submodule ℂ (m → ℂ)} (hW : W ≤ V)
    (hpos : PosDefOn G W) : finrank ℂ W ≤ posIndex G V := by
  unfold posIndex
  refine Finset.le_max' _ _ ?_
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (Submodule.finrank_mono hW)), W, hW, rfl, hpos⟩

open scoped Classical in
omit [Fintype m] in
theorem exists_posIndex (G : (m → ℂ) → (m → ℂ) → ℂ) (V : Submodule ℂ (m → ℂ)) :
    ∃ W : Submodule ℂ (m → ℂ), W ≤ V ∧ finrank ℂ W = posIndex G V ∧ PosDefOn G W := by
  have h : posIndex G V ∈ (Finset.range (finrank ℂ V + 1)).filter fun r =>
      ∃ W : Submodule ℂ (m → ℂ), W ≤ V ∧ finrank ℂ W = r ∧ PosDefOn G W := by
    unfold posIndex
    exact Finset.max'_mem _ _
  rw [Finset.mem_filter] at h
  exact h.2

/-- **Sylvester's bound.**  The index plus the dimension of a nonpositive subspace of `V` is at
most the dimension of `V`. -/
theorem posIndex_add_finrank_le {G : (m → ℂ) → (m → ℂ) → ℂ} {V U : Submodule ℂ (m → ℂ)}
    (hU : U ≤ V) (hnonpos : ∀ x ∈ U, (G x x).re ≤ 0) :
    posIndex G V + finrank ℂ U ≤ finrank ℂ V := by
  obtain ⟨W, hWV, hWr, hWpos⟩ := exists_posIndex G V
  have hinf : W ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    rw [Submodule.mem_bot]
    by_contra hx0
    have h1 := hWpos x hx.1 hx0
    have h2 := hnonpos x hx.2
    linarith
  have h := Submodule.finrank_sup_add_finrank_inf_eq W U
  rw [hinf, finrank_bot, add_zero, hWr] at h
  rw [← h]
  exact Submodule.finrank_mono (sup_le hWV hU)

/-! ### The index through a Gram matrix -/

section Gram

/-- The Gram matrix of `G` on a family, `Γ i j = G (b j) (b i)`, so that
`(Γ *ᵥ x) i = G (∑ x j • b j) (b i)`. -/
noncomputable def gram (G : (m → ℂ) → (m → ℂ) → ℂ) {k : ℕ} (b : Fin k → (m → ℂ)) :
    Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => G (b j) (b i)

omit [Fintype m] in
theorem isHermitian_gram {G : (m → ℂ) → (m → ℂ) → ℂ} (hG : IsHermForm G) {k : ℕ}
    (b : Fin k → (m → ℂ)) : (gram G b).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, gram, Matrix.of_apply, Matrix.of_apply, Complex.star_def,
    ← hG.conj_symm]

omit [Fintype m] in
theorem gram_mulVec {G : (m → ℂ) → (m → ℂ) → ℂ} (hG : IsHermForm G) {k : ℕ}
    (b : Fin k → (m → ℂ)) (x : Fin k → ℂ) (i : Fin k) :
    (gram G b *ᵥ x) i = G (∑ j, x j • b j) (b i) := by
  rw [hG.sum_left, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gram, Matrix.of_apply, mul_comm]

omit [Fintype m] in
/-- `G` on two combinations of the family, through the Gram matrix. -/
theorem gram_form {G : (m → ℂ) → (m → ℂ) → ℂ} (hG : IsHermForm G) {k : ℕ}
    (b : Fin k → (m → ℂ)) (x y : Fin k → ℂ) :
    G (∑ j, x j • b j) (∑ j, y j • b j) = star y ⬝ᵥ (gram G b *ᵥ x) := by
  rw [hG.sum_right, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gram_mulVec hG, Pi.star_apply, Complex.star_def]

/-- **Sylvester's law of inertia for Hermitian forms.**  For a linearly independent family `b`
spanning `V`, the positive index of `G` on `V` is the number of positive eigenvalues of the Gram
matrix, i.e. the number of roots of its characteristic polynomial with positive real part. -/
theorem posIndex_eq_countP {G : (m → ℂ) → (m → ℂ) → ℂ} (hG : IsHermForm G)
    {V : Submodule ℂ (m → ℂ)} {k : ℕ} {b : Fin k → (m → ℂ)} (hb : LinearIndependent ℂ b)
    (hspan : Submodule.span ℂ (Set.range b) = V) :
    posIndex G V = (gram G b).charpoly.roots.countP fun z => 0 < z.re := by
  classical
  set Γ := gram G b with hΓdef
  have hΓ : Γ.IsHermitian := isHermitian_gram hG b
  set d : Fin k → ℝ := hΓ.eigenvalues with hd
  set u : Fin k → (Fin k → ℂ) := fun j => ⇑(hΓ.eigenvectorBasis j) with hu
  have hΓu : ∀ j, Γ *ᵥ u j = (d j : ℂ) • u j := fun j => by
    have := hΓ.mulVec_eigenvectorBasis j
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at this
    exact this
  have huu : ∀ i j, u j ⬝ᵥ star (u i) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    have := (orthonormal_iff_ite.1 hΓ.eigenvectorBasis.orthonormal) i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    exact this
  -- the `G`-orthogonal family
  set f : Fin k → (m → ℂ) := fun j => ∑ i, u j i • b i with hf
  have hGff : ∀ j l, G (f j) (f l) = if l = j then (d j : ℂ) else 0 := by
    intro j l
    rw [hf]
    show G (∑ i, u j i • b i) (∑ i, u l i • b i) = _
    rw [gram_form hG, hΓu, dotProduct_smul, dotProduct_comm, huu, smul_eq_mul]
    split_ifs <;> simp
  have hfV : ∀ j, f j ∈ V := fun j => by
    rw [← hspan]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- `G` on a combination of the `f j`
  have hGcomb : ∀ c : Fin k → ℂ, G (∑ j, c j • f j) (∑ j, c j • f j)
      = ∑ j, (c j * starRingEnd ℂ (c j)) * (d j : ℂ) := by
    intro c
    rw [hG.sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hG.sum_right, Finset.sum_eq_single j]
    · rw [hGff, if_pos rfl]
      ring
    · intro l _ hl
      rw [hGff, if_neg hl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hre : ∀ c : Fin k → ℂ, (G (∑ j, c j • f j) (∑ j, c j • f j)).re
      = ∑ j, ‖c j‖ ^ 2 * d j := by
    intro c
    rw [hGcomb, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  -- linear independence of the `f j`
  have hf_indep : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : ∑ i, (∑ j, c j * u j i) • b i = 0 := by
      rw [← hc]
      simp only [hf, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have hcoef : ∀ i, ∑ j, c j * u j i = 0 := Fintype.linearIndependent_iff.1 hb _ hsum
    intro l
    have hvec : (∑ j, c j • u j) = 0 := funext fun i => by
      rw [Finset.sum_apply]
      simpa [smul_eq_mul] using hcoef i
    have h := congrArg (fun v : Fin k → ℂ => v ⬝ᵥ star (u l)) hvec
    simp only [sum_dotProduct, smul_dotProduct, huu, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_dotProduct] at h
    exact h
  -- the positive and the nonpositive subspaces spanned by the `f j`
  set S : Finset (Fin k) := Finset.univ.filter fun j => 0 < d j with hS
  have hsub_mem : ∀ (T : Finset (Fin k)) (x : m → ℂ),
      x ∈ Submodule.span ℂ (Set.range fun j : {j // j ∈ T} => f j) →
        ∃ c : Fin k → ℂ, (∀ j, j ∉ T → c j = 0) ∧ ∑ j, c j • f j = x := by
    intro T x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
    refine ⟨fun j => if h : j ∈ T then c ⟨j, h⟩ else 0, fun j hj => dif_neg hj, ?_⟩
    rw [← hc]
    set c' : Fin k → ℂ := fun j => if h : j ∈ T then c ⟨j, h⟩ else 0 with hc'
    calc ∑ j, c' j • f j = ∑ j ∈ T, c' j • f j := by
          symm
          apply Finset.sum_subset (Finset.subset_univ T)
          intro j _ hj
          simp [hc', hj]
      _ = ∑ i : {j // j ∈ T}, c' i • f i := (Finset.sum_coe_sort T fun j => c' j • f j).symm
      _ = ∑ i : {j // j ∈ T}, c i • f i := Finset.sum_congr rfl fun i _ => by simp [hc', i.2]
  have hcomb_mem : ∀ (T : Finset (Fin k)) (c : Fin k → ℂ), (∀ j, j ∉ T → c j = 0) →
      ∑ j, c j • f j ∈ Submodule.span ℂ (Set.range fun j : {j // j ∈ T} => f j) := by
    intro T c _
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j ∈ T
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · rw [‹∀ j, j ∉ T → c j = 0› j hj, zero_smul]
      exact Submodule.zero_mem _
  have hpos : PosDefOn G (Submodule.span ℂ (Set.range fun j : {j // j ∈ S} => f j)) := by
    intro x hx hx0
    obtain ⟨c, hc0, rfl⟩ := hsub_mem S x hx
    rw [hre]
    have hne : ∃ j, c j ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hx0
      simp [hall]
    obtain ⟨j₀, hj₀⟩ := hne
    have hj₀S : j₀ ∈ S := by
      by_contra h
      exact hj₀ (hc0 j₀ h)
    refine Finset.sum_pos' (fun j _ => ?_) ⟨j₀, Finset.mem_univ _, ?_⟩
    · by_cases hj : j ∈ S
      · rw [hS, Finset.mem_filter] at hj
        exact mul_nonneg (by positivity) hj.2.le
      · rw [hc0 j hj]
        simp
    · rw [hS, Finset.mem_filter] at hj₀S
      exact mul_pos (by positivity) hj₀S.2
  have hneg : ∀ x ∈ Submodule.span ℂ (Set.range fun j : {j // j ∈ Sᶜ} => f j), (G x x).re ≤ 0 := by
    intro x hx
    obtain ⟨c, hc0, rfl⟩ := hsub_mem Sᶜ x hx
    rw [hre]
    refine Finset.sum_nonpos fun j _ => ?_
    by_cases hj : j ∈ Sᶜ
    · rw [Finset.mem_compl, hS, Finset.mem_filter, not_and, not_lt] at hj
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hj (Finset.mem_univ _))
    · rw [hc0 j hj]
      simp
  -- the dimensions
  have hV_rank : finrank ℂ V = k := by
    rw [← hspan, finrank_span_eq_card hb, Fintype.card_fin]
  have hWp_rank : finrank ℂ (Submodule.span ℂ (Set.range fun j : {j // j ∈ S} => f j)) = S.card := by
    have hli : LinearIndependent ℂ (fun j : {j // j ∈ S} => f j) :=
      hf_indep.comp _ Subtype.val_injective
    rw [finrank_span_eq_card hli]
    simp
  have hWn_rank : finrank ℂ (Submodule.span ℂ (Set.range fun j : {j // j ∈ Sᶜ} => f j))
      = k - S.card := by
    have hli : LinearIndependent ℂ (fun j : {j // j ∈ Sᶜ} => f j) :=
      hf_indep.comp _ Subtype.val_injective
    rw [finrank_span_eq_card hli]
    simp
  have hle : S.card ≤ posIndex G V := by
    have := le_posIndex (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hfV j)) hpos
    rwa [hWp_rank] at this
  have hge : posIndex G V + (k - S.card) ≤ k := by
    have := posIndex_add_finrank_le (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hfV j)) hneg
    rwa [hWn_rank, hV_rank] at this
  have hScard : S.card ≤ k := by
    have := Finset.card_le_univ S
    rwa [Fintype.card_fin] at this
  have hindex : posIndex G V = S.card := by omega
  -- the count of positive eigenvalues
  rw [hindex, hΓ.roots_charpoly_eq_eigenvalues, Multiset.countP_map, hS, Finset.card_def,
    Finset.filter_val]
  congr 1

/-- Every subspace is spanned by a linearly independent family indexed by `Fin (finrank)`. -/
theorem exists_basis_family (V : Submodule ℂ (m → ℂ)) :
    ∃ e : Fin (finrank ℂ V) → (m → ℂ), LinearIndependent ℂ e ∧ Submodule.span ℂ (Set.range e) = V := by
  refine ⟨fun i => (Module.finBasis ℂ V i : m → ℂ), ?_, ?_⟩
  · exact (Module.finBasis ℂ V).linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · have e : (fun i => (Module.finBasis ℂ V i : m → ℂ)) = V.subtype ∘ Module.finBasis ℂ V := rfl
    rw [e, Set.range_comp, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top,
      Submodule.range_subtype]

omit [Fintype m] in
/-- If `G` is nondegenerate on `V`, the Gram matrix of a basis of `V` is invertible. -/
theorem det_gram_ne_zero {G : (m → ℂ) → (m → ℂ) → ℂ} (hG : IsHermForm G)
    {V : Submodule ℂ (m → ℂ)} {k : ℕ} {b : Fin k → (m → ℂ)} (hb : LinearIndependent ℂ b)
    (hspan : Submodule.span ℂ (Set.range b) = V)
    (hnd : ∀ v ∈ V, (∀ w ∈ V, G v w = 0) → v = 0) : (gram G b).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hv : ∑ j, x j • b j = 0 := by
    refine hnd _ ?_ fun w hw => ?_
    · rw [← hspan]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [← hspan] at hw
      obtain ⟨y, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hw
      rw [gram_form hG, hx, dotProduct_zero]
  exact hx0 (funext (Fintype.linearIndependent_iff.1 hb x hv))

end Gram

end HermitianIndex
end MorseFloer
