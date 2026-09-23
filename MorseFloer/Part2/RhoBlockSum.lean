import MorseFloer.Part2.RhoNormalisation

/-!
# Properties of `ρ`: block sums

The product clause of Theorem 7.1.3 for the map `ρ` of `Part2/Rho.lean`:
`ρ(A ⊕ B) = ρ(A) ρ(B)` for symplectic `A`, `B` (`rho_blockSum`), where `A ⊕ B` is the block sum
`Chapter7.blockSum`, read in the standard symplectic coordinates through `blockSumEquiv`.

The spectrum of `A ⊕ B` is the union of the spectra with multiplicities (`charpoly_blockSum`),
and its generalised eigenspace at `μ` is `E_μ(A) ⊕ E_μ(B)` (`E_blockSum`), the two summands
embedded by `ι₁`, `ι₂` (extension by zero) and `ω`-orthogonal, since `J` splits along the
block sum (`negJ_blockSum`).  The positive index is additive on orthogonal sums and invariant
under the isometric embeddings, so `m₊`, `m` and `σ` add up, and the factor of `μ` in `ρ(A ⊕ B)`
is the product of its factors in `ρ(A)` and `ρ(B)` (the parity of `m(-1)` entering at `-1`).
-/

open Polynomial Matrix Module

namespace MorseFloer
namespace Rho

open Chapter7 SymplecticEigen SymplecticSpectrum EigenDecomp EigenMult HermitianIndex
  SignatureContinuity

/-! ### The index under an isometric embedding -/

section Isometry

variable {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]

/-- The positive index is invariant under an injective linear map preserving the forms. -/
theorem posIndex_map_of_isometry' {G₁ : (m₁ → ℂ) → (m₁ → ℂ) → ℂ}
    {G₂ : (m₂ → ℂ) → (m₂ → ℂ) → ℂ} (hG₁ : IsHermForm G₁) (hG₂ : IsHermForm G₂)
    (T : (m₁ → ℂ) →ₗ[ℂ] (m₂ → ℂ)) (hT : LinearMap.ker T = ⊥)
    (hiso : ∀ x y, G₂ (T x) (T y) = G₁ x y) (V : Submodule ℂ (m₁ → ℂ)) :
    posIndex G₂ (V.map T) = posIndex G₁ V := by
  classical
  obtain ⟨e, he, heV⟩ := exists_basis_family V
  have he' : LinearIndependent ℂ (T ∘ e) := he.map' T hT
  have hspan' : Submodule.span ℂ (Set.range (T ∘ e)) = V.map T := by
    rw [Set.range_comp, Submodule.span_image, heV]
  rw [posIndex_eq_countP hG₂ he' hspan', posIndex_eq_countP hG₁ he heV]
  have hgram : HermitianIndex.gram G₂ (T ∘ e) = HermitianIndex.gram G₁ e := by
    ext i j
    simp only [HermitianIndex.gram, Matrix.of_apply, Function.comp, hiso]
  rw [hgram]

end Isometry

/-! ### Transport of generalised eigenspaces along an intertwining map -/

section Transport

variable {l₁ l₂ : Type*} [DecidableEq l₁] [Fintype l₁] [DecidableEq l₂] [Fintype l₂]

theorem pow_sub_mulVec_map {M : Matrix (l₁ ⊕ l₁) (l₁ ⊕ l₁) ℂ}
    {M' : Matrix (l₂ ⊕ l₂) (l₂ ⊕ l₂) ℂ} (ι : ((l₁ ⊕ l₁) → ℂ) →ₗ[ℂ] ((l₂ ⊕ l₂) → ℂ))
    (hι : ∀ x, M' *ᵥ ι x = ι (M *ᵥ x)) (μ : ℂ) (k : ℕ) (x : (l₁ ⊕ l₁) → ℂ) :
    ((M' - μ • 1) ^ k) *ᵥ ι x = ι (((M - μ • 1) ^ k) *ᵥ x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have h1 : (M' - μ • 1) *ᵥ ι x = ι ((M - μ • 1) *ᵥ x) := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, Matrix.one_mulVec, hι, map_sub, map_smul]
    rw [pow_succ, ← Matrix.mulVec_mulVec, pow_succ, ← Matrix.mulVec_mulVec, h1, ih]

theorem E_map_le {M : Matrix (l₁ ⊕ l₁) (l₁ ⊕ l₁) ℂ} {M' : Matrix (l₂ ⊕ l₂) (l₂ ⊕ l₂) ℂ}
    (ι : ((l₁ ⊕ l₁) → ℂ) →ₗ[ℂ] ((l₂ ⊕ l₂) → ℂ)) (hι : ∀ x, M' *ᵥ ι x = ι (M *ᵥ x)) (μ : ℂ) :
    (E M μ).map ι ≤ E M' μ := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := (mem_E_iff _ _ _).1 hx
  refine (mem_E_iff _ _ _).2 ⟨k, ?_⟩
  unfold InGen at *
  rw [pow_sub_mulVec_map ι hι, hk, map_zero]

end Transport

/-! ### The block sum in symplectic coordinates -/

section BlockSum

variable {m n : ℕ}

theorem blockSumEquiv_inl_inl (i : Fin m) :
    blockSumEquiv m n (Sum.inl (Sum.inl i)) = Sum.inl (Fin.castAdd n i) := rfl

theorem blockSumEquiv_inl_inr (i : Fin m) :
    blockSumEquiv m n (Sum.inl (Sum.inr i)) = Sum.inr (Fin.castAdd n i) := rfl

theorem blockSumEquiv_inr_inl (j : Fin n) :
    blockSumEquiv m n (Sum.inr (Sum.inl j)) = Sum.inl (Fin.natAdd m j) := rfl

theorem blockSumEquiv_inr_inr (j : Fin n) :
    blockSumEquiv m n (Sum.inr (Sum.inr j)) = Sum.inr (Fin.natAdd m j) := rfl

/-- `-J` splits along the block sum. -/
theorem negJ_blockSum :
    -(Matrix.J (Fin (m + n)) ℂ) = Matrix.reindex (blockSumEquiv m n) (blockSumEquiv m n)
      (Matrix.fromBlocks (-(Matrix.J (Fin m) ℂ)) 0 0 (-(Matrix.J (Fin n) ℂ))) := by
  ext k k'
  obtain ⟨i, rfl⟩ := (blockSumEquiv m n).surjective k
  obtain ⟨j, rfl⟩ := (blockSumEquiv m n).surjective k'
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
    simp [blockSumEquiv_inl_inl, blockSumEquiv_inl_inr, blockSumEquiv_inr_inl,
      blockSumEquiv_inr_inr, Matrix.J, Matrix.one_apply, Fin.ext_iff] <;> omega

/-- A vector on the block sum, from its two components. -/
theorem elim_comp_symm_apply (u : (Fin m ⊕ Fin m) → ℂ) (v : (Fin n ⊕ Fin n) → ℂ)
    (j : (Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n)) :
    (Sum.elim u v ∘ (blockSumEquiv m n).symm) (blockSumEquiv m n j) = Sum.elim u v j := by
  simp

theorem elim_comp_symm_eq (u : (Fin m ⊕ Fin m) → ℂ) (v : (Fin n ⊕ Fin n) → ℂ)
    (z : (Fin (m + n) ⊕ Fin (m + n)) → ℂ) (h : ∀ j, z (blockSumEquiv m n j) = Sum.elim u v j) :
    z = Sum.elim u v ∘ (blockSumEquiv m n).symm := by
  funext k
  obtain ⟨j, rfl⟩ := (blockSumEquiv m n).surjective k
  rw [elim_comp_symm_apply, h]

/-- A block-diagonal matrix, reindexed, acts componentwise. -/
theorem reindex_fromBlocks_mulVec (P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (u : (Fin m ⊕ Fin m) → ℂ)
    (v : (Fin n ⊕ Fin n) → ℂ) :
    Matrix.reindex (blockSumEquiv m n) (blockSumEquiv m n) (Matrix.fromBlocks P 0 0 Q)
        *ᵥ (Sum.elim u v ∘ (blockSumEquiv m n).symm)
      = Sum.elim (P *ᵥ u) (Q *ᵥ v) ∘ (blockSumEquiv m n).symm := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, Matrix.fromBlocks_mulVec]
  congr 1
  simp

/-- `ω` splits along the block sum. -/
theorem stdFormC_elim (x y : (Fin m ⊕ Fin m) → ℂ) (x' y' : (Fin n ⊕ Fin n) → ℂ) :
    stdFormC (Fin (m + n)) (Sum.elim x x' ∘ (blockSumEquiv m n).symm)
        (Sum.elim y y' ∘ (blockSumEquiv m n).symm)
      = stdFormC (Fin m) x y + stdFormC (Fin n) x' y' := by
  rw [stdFormC_apply, stdFormC_apply, stdFormC_apply, negJ_blockSum, reindex_fromBlocks_mulVec,
    comp_equiv_symm_dotProduct, Function.comp_assoc, Equiv.symm_comp_self,
    Function.comp_id, sumElim_dotProduct_sumElim]

theorem conjVec_elim (y : (Fin m ⊕ Fin m) → ℂ) (y' : (Fin n ⊕ Fin n) → ℂ) :
    conjVec (Sum.elim y y' ∘ (blockSumEquiv m n).symm)
      = Sum.elim (conjVec y) (conjVec y') ∘ (blockSumEquiv m n).symm := by
  funext k
  obtain ⟨j, rfl⟩ := (blockSumEquiv m n).surjective k
  rcases j with j | j <;> simp [conjVec]

theorem HForm_elim (x y : (Fin m ⊕ Fin m) → ℂ) (x' y' : (Fin n ⊕ Fin n) → ℂ) :
    HForm (Sum.elim x x' ∘ (blockSumEquiv m n).symm) (Sum.elim y y' ∘ (blockSumEquiv m n).symm)
      = HForm x y + HForm x' y' := by
  rw [HForm, HForm, HForm, conjVec_elim, stdFormC_elim]

theorem GForm_elim (x y : (Fin m ⊕ Fin m) → ℂ) (x' y' : (Fin n ⊕ Fin n) → ℂ) :
    GForm (Sum.elim x x' ∘ (blockSumEquiv m n).symm) (Sum.elim y y' ∘ (blockSumEquiv m n).symm)
      = GForm x y + GForm x' y' := by
  rw [GForm, GForm, GForm, HForm_elim, mul_add]

/-- The first embedding `x ↦ (x, 0)`. -/
def ι₁ (m n : ℕ) : ((Fin m ⊕ Fin m) → ℂ) →ₗ[ℂ] ((Fin (m + n) ⊕ Fin (m + n)) → ℂ) where
  toFun x := Sum.elim x 0 ∘ (blockSumEquiv m n).symm
  map_add' x y := by
    funext k
    obtain ⟨j, rfl⟩ := (blockSumEquiv m n).surjective k
    rcases j with i | i <;> simp
  map_smul' a x := by
    funext k
    obtain ⟨j, rfl⟩ := (blockSumEquiv m n).surjective k
    rcases j with i | i <;> simp

/-- The second embedding `y ↦ (0, y)`. -/
def ι₂ (m n : ℕ) : ((Fin n ⊕ Fin n) → ℂ) →ₗ[ℂ] ((Fin (m + n) ⊕ Fin (m + n)) → ℂ) where
  toFun y := Sum.elim 0 y ∘ (blockSumEquiv m n).symm
  map_add' x y := by
    funext k
    obtain ⟨j, rfl⟩ := (blockSumEquiv m n).surjective k
    rcases j with i | i <;> simp
  map_smul' a x := by
    funext k
    obtain ⟨j, rfl⟩ := (blockSumEquiv m n).surjective k
    rcases j with i | i <;> simp

theorem ι₁_apply (x : (Fin m ⊕ Fin m) → ℂ) :
    ι₁ m n x = Sum.elim x (0 : (Fin n ⊕ Fin n) → ℂ) ∘ (blockSumEquiv m n).symm :=
  rfl

theorem ι₂_apply (y : (Fin n ⊕ Fin n) → ℂ) :
    ι₂ m n y = Sum.elim (0 : (Fin m ⊕ Fin m) → ℂ) y ∘ (blockSumEquiv m n).symm :=
  rfl

theorem ι₁_add_ι₂ (u : (Fin m ⊕ Fin m) → ℂ) (v : (Fin n ⊕ Fin n) → ℂ) :
    ι₁ m n u + ι₂ m n v = Sum.elim u v ∘ (blockSumEquiv m n).symm := by
  funext k
  obtain ⟨j, rfl⟩ := (blockSumEquiv m n).surjective k
  rcases j with j | j <;> simp [ι₁_apply, ι₂_apply]

theorem ι₁_apply_inl (x : (Fin m ⊕ Fin m) → ℂ) (i : Fin m ⊕ Fin m) :
    ι₁ m n x (blockSumEquiv m n (Sum.inl i)) = x i := by
  simp [ι₁_apply]

theorem ι₂_apply_inl (y : (Fin n ⊕ Fin n) → ℂ) (i : Fin m ⊕ Fin m) :
    ι₂ m n y (blockSumEquiv m n (Sum.inl i)) = 0 := by
  simp [ι₂_apply]

theorem ι₂_apply_inr (y : (Fin n ⊕ Fin n) → ℂ) (j : Fin n ⊕ Fin n) :
    ι₂ m n y (blockSumEquiv m n (Sum.inr j)) = y j := by
  simp [ι₂_apply]

theorem ker_ι₁ : LinearMap.ker (ι₁ m n) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  funext i
  have := congrFun hx (blockSumEquiv m n (Sum.inl i))
  rwa [ι₁_apply_inl] at this

theorem ker_ι₂ : LinearMap.ker (ι₂ m n) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro y hy
  funext j
  have := congrFun hy (blockSumEquiv m n (Sum.inr j))
  rwa [ι₂_apply_inr] at this

theorem GForm_ι₁ (x y : (Fin m ⊕ Fin m) → ℂ) : GForm (ι₁ m n x) (ι₁ m n y) = GForm x y := by
  rw [ι₁_apply, ι₁_apply, GForm_elim, isHermForm_GForm.zero_left, add_zero]

theorem GForm_ι₂ (x y : (Fin n ⊕ Fin n) → ℂ) : GForm (ι₂ m n x) (ι₂ m n y) = GForm x y := by
  rw [ι₂_apply, ι₂_apply, GForm_elim, isHermForm_GForm.zero_left, zero_add]

theorem GForm_ι₁_ι₂ (x : (Fin m ⊕ Fin m) → ℂ) (y : (Fin n ⊕ Fin n) → ℂ) :
    GForm (ι₁ m n x) (ι₂ m n y) = 0 := by
  rw [ι₁_apply, ι₂_apply, GForm_elim, isHermForm_GForm.zero_left, isHermForm_GForm.zero_right,
    add_zero]

/-! ### The spectral data of the block sum -/

variable (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)

theorem cpx_blockSum :
    cpx (blockSum A B) = Matrix.reindex (blockSumEquiv m n) (blockSumEquiv m n)
      (Matrix.fromBlocks (cpx A) 0 0 (cpx B)) := by
  unfold cpx blockSum
  rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]

theorem charpoly_blockSum : (cpx (blockSum A B)).charpoly = (cpx A).charpoly * (cpx B).charpoly := by
  rw [cpx_blockSum, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂]

theorem roots_blockSum :
    (cpx (blockSum A B)).charpoly.roots = (cpx A).charpoly.roots + (cpx B).charpoly.roots := by
  rw [charpoly_blockSum, roots_mul (mul_ne_zero (charpoly_monic _).ne_zero (charpoly_monic _).ne_zero)]

theorem blockSum_mulVec (u : (Fin m ⊕ Fin m) → ℂ) (v : (Fin n ⊕ Fin n) → ℂ) :
    cpx (blockSum A B) *ᵥ (ι₁ m n u + ι₂ m n v) = ι₁ m n (cpx A *ᵥ u) + ι₂ m n (cpx B *ᵥ v) := by
  rw [ι₁_add_ι₂, ι₁_add_ι₂, cpx_blockSum, reindex_fromBlocks_mulVec]

theorem blockSum_mulVec_ι₁ (u : (Fin m ⊕ Fin m) → ℂ) :
    cpx (blockSum A B) *ᵥ ι₁ m n u = ι₁ m n (cpx A *ᵥ u) := by
  have := blockSum_mulVec A B u 0
  rwa [map_zero, add_zero, Matrix.mulVec_zero, map_zero, add_zero] at this

theorem blockSum_mulVec_ι₂ (v : (Fin n ⊕ Fin n) → ℂ) :
    cpx (blockSum A B) *ᵥ ι₂ m n v = ι₂ m n (cpx B *ᵥ v) := by
  have := blockSum_mulVec A B 0 v
  rwa [map_zero, zero_add, Matrix.mulVec_zero, map_zero, zero_add] at this

/-- **`E_μ(A ⊕ B) = E_μ(A) ⊕ E_μ(B)`.** -/
theorem E_blockSum (μ : ℂ) :
    E (cpx (blockSum A B)) μ = (E (cpx A) μ).map (ι₁ m n) ⊔ (E (cpx B) μ).map (ι₂ m n) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨k, hk⟩ := (mem_E_iff _ _ _).1 hz
    unfold InGen at hk
    set u : (Fin m ⊕ Fin m) → ℂ := fun i => z (blockSumEquiv m n (Sum.inl i)) with hu
    set v : (Fin n ⊕ Fin n) → ℂ := fun j => z (blockSumEquiv m n (Sum.inr j)) with hv
    have hz' : z = ι₁ m n u + ι₂ m n v := by
      rw [ι₁_add_ι₂]
      refine elim_comp_symm_eq u v z fun j => ?_
      rcases j with j | j <;> rfl
    have hpow : ∀ k : ℕ, ((cpx (blockSum A B) - μ • 1) ^ k) *ᵥ (ι₁ m n u + ι₂ m n v)
        = ι₁ m n (((cpx A - μ • 1) ^ k) *ᵥ u) + ι₂ m n (((cpx B - μ • 1) ^ k) *ᵥ v) := by
      intro k
      rw [Matrix.mulVec_add, pow_sub_mulVec_map (ι₁ m n) (blockSum_mulVec_ι₁ A B),
        pow_sub_mulVec_map (ι₂ m n) (blockSum_mulVec_ι₂ A B)]
    rw [hz', hpow] at hk
    have hu0 : ((cpx A - μ • 1) ^ k) *ᵥ u = 0 := by
      funext i
      have := congrFun hk (blockSumEquiv m n (Sum.inl i))
      rwa [Pi.add_apply, ι₁_apply_inl, ι₂_apply_inl, add_zero] at this
    have hv0 : ((cpx B - μ • 1) ^ k) *ᵥ v = 0 := by
      funext j
      have := congrFun hk (blockSumEquiv m n (Sum.inr j))
      rw [Pi.add_apply, ι₂_apply_inr] at this
      have h1 : ι₁ m n (((cpx A - μ • 1) ^ k) *ᵥ u) (blockSumEquiv m n (Sum.inr j)) = 0 := by
        simp [ι₁_apply]
      rwa [h1, zero_add] at this
    rw [hz']
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem ((mem_E_iff _ _ _).2 ⟨k, hu0⟩))
      (Submodule.mem_map_of_mem ((mem_E_iff _ _ _).2 ⟨k, hv0⟩))
  · exact sup_le (E_map_le (ι₁ m n) (blockSum_mulVec_ι₁ A B) μ)
      (E_map_le (ι₂ m n) (blockSum_mulVec_ι₂ A B) μ)

theorem map_ι₁_inf_map_ι₂ (V : Submodule ℂ ((Fin m ⊕ Fin m) → ℂ))
    (W : Submodule ℂ ((Fin n ⊕ Fin n) → ℂ)) : V.map (ι₁ m n) ⊓ W.map (ι₂ m n) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Submodule.mem_inf] at hz
  obtain ⟨⟨x, -, rfl⟩, ⟨y, -, hy⟩⟩ := hz
  rw [Submodule.mem_bot]
  have hx : x = 0 := by
    funext i
    have := congrFun hy (blockSumEquiv m n (Sum.inl i))
    rwa [ι₂_apply_inl, ι₁_apply_inl, eq_comm] at this
  rw [hx, map_zero]

theorem mPos_blockSum (μ : ℂ) :
    mPos (cpx (blockSum A B)) μ = mPos (cpx A) μ + mPos (cpx B) μ := by
  rw [mPos, mPos, mPos, E_blockSum, posIndex_sup isHermForm_GForm (map_ι₁_inf_map_ι₂ _ _)
    (by rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩; exact GForm_ι₁_ι₂ x y),
    posIndex_map_of_isometry' isHermForm_GForm isHermForm_GForm _ ker_ι₁ (GForm_ι₁),
    posIndex_map_of_isometry' isHermForm_GForm isHermForm_GForm _ ker_ι₂ (GForm_ι₂)]

open Classical in
theorem sigma_blockSum (μ : ℂ) :
    sigma (cpx (blockSum A B)) μ = sigma (cpx A) μ + sigma (cpx B) μ := by
  unfold sigma
  rw [mPos_blockSum, roots_blockSum, Multiset.count_add]
  push_cast
  ring

open Classical in
/-- The factor of an eigenvalue that is not one is `1`. -/
theorem factor_eq_one_of_not_mem {l : Type*} [DecidableEq l] [Fintype l]
    (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) {μ : ℂ}
    (hμ : μ ∉ M.charpoly.roots) : factor M μ = 1 := by
  have hcount : M.charpoly.roots.count μ = 0 := Multiset.count_eq_zero.2 hμ
  have hsigma : sigma M μ = 0 := by
    unfold sigma mPos
    rw [E_eq_bot_of_not_mem_roots hμ, hcount]
    have := posIndex_le_finrank (GForm (l := l)) ⊥
    rw [finrank_bot] at this
    omega
  unfold factor
  rw [hsigma, hcount]
  split_ifs <;> simp

open Classical in
theorem factor_blockSum (hA : A ∈ Matrix.symplecticGroup (Fin m) ℝ)
    (hB : B ∈ Matrix.symplecticGroup (Fin n) ℝ) (μ : ℂ) :
    factor (cpx (blockSum A B)) μ = factor (cpx A) μ * factor (cpx B) μ := by
  unfold factor
  rw [sigma_blockSum, roots_blockSum, Multiset.count_add]
  split_ifs with h1 h2 h3
  · have hμ0 : μ ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      exact zero_ne_one h1.1
    exact zpow_add₀ hμ0 _ _
  · obtain ⟨a, ha⟩ := even_count_neg_one hA
    obtain ⟨b, hb⟩ := even_count_neg_one hB
    subst h2
    rw [← pow_add]
    congr 1
    omega
  · rw [pow_add]
  · rw [mul_one]

theorem rhoC_blockSum (hA : A ∈ Matrix.symplecticGroup (Fin m) ℝ)
    (hB : B ∈ Matrix.symplecticGroup (Fin n) ℝ) :
    rhoC (cpx (blockSum A B)) = rhoC (cpx A) * rhoC (cpx B) := by
  classical
  rw [rhoC, rhoC, rhoC, roots_blockSum, Multiset.toFinset_add]
  rw [Finset.prod_congr rfl fun μ _ => factor_blockSum A B hA hB μ, Finset.prod_mul_distrib]
  congr 1
  · symm
    refine Finset.prod_subset Finset.subset_union_left fun μ _ hμ => ?_
    exact factor_eq_one_of_not_mem _ (fun h => hμ (Multiset.mem_toFinset.2 h))
  · symm
    refine Finset.prod_subset Finset.subset_union_right fun μ _ hμ => ?_
    exact factor_eq_one_of_not_mem _ (fun h => hμ (Multiset.mem_toFinset.2 h))

/-- **`ρ(A ⊕ B) = ρ(A) ρ(B)`** (Theorem 7.1.3). -/
theorem rho_blockSum (hA : A ∈ Matrix.symplecticGroup (Fin m) ℝ)
    (hB : B ∈ Matrix.symplecticGroup (Fin n) ℝ) :
    rho (m + n) (blockSum A B) = rho m A * rho n B :=
  rhoC_blockSum A B hA hB

end BlockSum

end Rho
end MorseFloer
