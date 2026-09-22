import MorseFloer.Part2.Ch7

/-!
# The form `H(X, Y) = ω(X, Ȳ)` on the generalised eigenspaces of a symplectic matrix

The third brick for the map `ρ : Sp(2n) → S¹` of Chapter 7 — the content of Lemma 7.3.3 and
Corollary 7.3.4, stated for the sesquilinear form `H(X, Y) = ω(X, Ȳ)` on `ℂ²ⁿ`, of which the
real form `B = Im H` of §7.3.a is the imaginary part.

* A real symplectic matrix, complexified, preserves `H` (`HForm_cpx`): it preserves `ω` and
  commutes with conjugation.
* **Lemma 7.3.3** (`HForm_eq_zero_of_inGen`): if `A` preserves `H`, the generalised
  eigenspaces `E_μ` and `E_ν` are `H`-orthogonal whenever `μ ν̄ ≠ 1`.  The proof is the
  book's: for `X ∈ ker (A - μ)^k` and `Y ∈ ker (A - ν)^l`, write `AX = μX + X'` and
  `AY = νY + Y'` with `X'`, `Y'` one level down, expand `H(X, Y) = H(AX, AY)`, and induct.
* **Corollary 7.3.4** (`HForm_eq_zero_of_inGen_self`): `E_μ` is `H`-isotropic when `|μ| ≠ 1`.
* `H` is nondegenerate on `ℂ²ⁿ` (`eq_zero_of_forall_HForm_eq_zero`), and therefore
  (`eq_zero_of_inGen_of_forall_HForm_eq_zero`) **nondegenerate on `E_ν` when `|ν| = 1`**: a
  vector of `E_ν` orthogonal to `E_ν` is orthogonal to every other `E_μ` by Lemma 7.3.3, hence
  to everything, since the generalised eigenspaces span `ℂ²ⁿ`.  This is the fact that makes
  the signature `m₊(ν)` of `Q` on `E_ν` meaningful.
-/

open Matrix Module

namespace MorseFloer
namespace SymplecticEigen

open Chapter7

variable {l : Type*} [DecidableEq l] [Fintype l]

/-! ### The complexification and the form `H` -/

/-- The complexification of a real matrix. -/
def cpx (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℂ := A.map Complex.ofRealHom

/-- The sesquilinear form `H(X, Y) = ω(X, Ȳ)`, whose imaginary part is `B`. -/
noncomputable def HForm (X Y : (l ⊕ l) → ℂ) : ℂ := stdFormC l X (conjVec Y)

theorem BForm_eq_im (X Y : (l ⊕ l) → ℂ) : BForm X Y = (HForm X Y).im := rfl

omit [DecidableEq l] [Fintype l] in
theorem conjVec_add (X Y : (l ⊕ l) → ℂ) : conjVec (X + Y) = conjVec X + conjVec Y := by
  funext i; simp [conjVec]

omit [DecidableEq l] [Fintype l] in
theorem conjVec_smul (a : ℂ) (X : (l ⊕ l) → ℂ) :
    conjVec (a • X) = (starRingEnd ℂ a) • conjVec X := by
  funext i; simp [conjVec]

omit [DecidableEq l] [Fintype l] in
theorem conjVec_zero : conjVec (0 : (l ⊕ l) → ℂ) = 0 := by
  funext i; simp [conjVec]

theorem HForm_add_left (X Y Z : (l ⊕ l) → ℂ) : HForm (X + Y) Z = HForm X Z + HForm Y Z := by
  simp [HForm]

theorem HForm_add_right (X Y Z : (l ⊕ l) → ℂ) : HForm X (Y + Z) = HForm X Y + HForm X Z := by
  simp [HForm, conjVec_add]

theorem HForm_smul_left (a : ℂ) (X Y : (l ⊕ l) → ℂ) : HForm (a • X) Y = a * HForm X Y := by
  simp [HForm]

theorem HForm_smul_right (a : ℂ) (X Y : (l ⊕ l) → ℂ) :
    HForm X (a • Y) = starRingEnd ℂ a * HForm X Y := by
  simp [HForm, conjVec_smul]

theorem HForm_zero_left (Y : (l ⊕ l) → ℂ) : HForm 0 Y = 0 := by simp [HForm]

theorem HForm_zero_right (X : (l ⊕ l) → ℂ) : HForm X 0 = 0 := by simp [HForm, conjVec_zero]

/-- `H` is nondegenerate: `ω` is, and conjugation is a bijection. -/
theorem eq_zero_of_forall_HForm_eq_zero {X : (l ⊕ l) → ℂ} (h : ∀ Y, HForm X Y = 0) : X = 0 := by
  refine (stdFormC_nondegenerate (l := l)).1 X fun Z => ?_
  have := h (conjVec Z)
  rwa [HForm, conjVec_conjVec] at this

/-! ### Symplectic matrices preserve `H` -/

omit [Fintype l] in
theorem J_map : (Matrix.J l ℝ).map Complex.ofRealHom = Matrix.J l ℂ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.J, Matrix.one_apply, Matrix.map_apply]
  split_ifs <;> simp

theorem cpx_symplectic {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    (cpx A)ᵀ * Matrix.J l ℂ * cpx A = Matrix.J l ℂ := by
  have h := SymplecticGroup.mem_iff'.1 hA
  have h' : (Aᵀ * Matrix.J l ℝ * A).map Complex.ofRealHom
      = (Matrix.J l ℝ).map Complex.ofRealHom := by rw [h]
  rw [Matrix.map_mul, Matrix.map_mul, J_map] at h'
  have ht : (Aᵀ).map Complex.ofRealHom = (cpx A)ᵀ := by
    ext i j
    simp [cpx, Matrix.map_apply]
  rw [ht] at h'
  exact h'

theorem stdFormC_cpx {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    (X Y : (l ⊕ l) → ℂ) : stdFormC l (cpx A *ᵥ X) (cpx A *ᵥ Y) = stdFormC l X Y := by
  have hM : (cpx A)ᵀ * (-(Matrix.J l ℂ)) * cpx A = -(Matrix.J l ℂ) := by
    rw [Matrix.mul_neg, Matrix.neg_mul, cpx_symplectic hA]
  rw [stdFormC_apply, stdFormC_apply, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hM,
    ← Matrix.dotProduct_mulVec]

omit [DecidableEq l] in
theorem conjVec_cpx_mulVec (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) (Y : (l ⊕ l) → ℂ) :
    conjVec (cpx A *ᵥ Y) = cpx A *ᵥ conjVec Y := by
  funext i
  have h := RingHom.map_mulVec (starRingEnd ℂ) (cpx A) Y i
  have hmap : (cpx A).map (starRingEnd ℂ) = cpx A := by
    ext i j
    simp [cpx, Matrix.map_apply]
  rw [hmap] at h
  exact h

/-- **A symplectic matrix preserves `H`.** -/
theorem HForm_cpx {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    (X Y : (l ⊕ l) → ℂ) : HForm (cpx A *ᵥ X) (cpx A *ᵥ Y) = HForm X Y := by
  rw [HForm, conjVec_cpx_mulVec, stdFormC_cpx hA]
  rfl

/-! ### Generalised eigenspaces -/

/-- `X` lies in the generalised eigenspace of level `k` for the eigenvalue `μ`. -/
def InGen (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) (k : ℕ) (X : (l ⊕ l) → ℂ) : Prop :=
  ((M - μ • 1) ^ k) *ᵥ X = 0

theorem inGen_zero_iff {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} {X : (l ⊕ l) → ℂ} :
    InGen M μ 0 X ↔ X = 0 := by
  simp [InGen]

theorem InGen.succ {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} {k : ℕ} {X : (l ⊕ l) → ℂ}
    (h : InGen M μ (k + 1) X) : InGen M μ k ((M - μ • 1) *ᵥ X) := by
  unfold InGen at *
  rw [Matrix.mulVec_mulVec, ← pow_succ]
  exact h

theorem mulVec_eq_smul_add (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) (X : (l ⊕ l) → ℂ) :
    M *ᵥ X = μ • X + (M - μ • 1) *ᵥ X := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  abel

/-- Membership in Mathlib's maximal generalised eigenspace, in matrix terms. -/
theorem mem_maxGenEigenspace_iff (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) (X : (l ⊕ l) → ℂ) :
    X ∈ Module.End.maxGenEigenspace (Matrix.toLin' M) μ ↔ ∃ k, InGen M μ k X := by
  rw [Module.End.mem_maxGenEigenspace]
  have e : ∀ k : ℕ, ((Matrix.toLin' M - μ • (1 : Module.End ℂ ((l ⊕ l) → ℂ))) ^ k) X
      = ((M - μ • 1) ^ k) *ᵥ X := by
    intro k
    have h1 : Matrix.toLin' M - μ • (1 : Module.End ℂ ((l ⊕ l) → ℂ)) = Matrix.toLin' (M - μ • 1) := by
      rw [map_sub, map_smul, Matrix.toLin'_one]
      rfl
    rw [h1, ← Matrix.toLin'_pow, Matrix.toLin'_apply]
  simp only [e]
  rfl

/-! ### Lemma 7.3.3 and its consequences -/

/-- **Lemma 7.3.3.**  If `M` preserves `H`, then `E_μ ⊥_H E_ν` whenever `μ ν̄ ≠ 1`. -/
theorem HForm_eq_zero_of_inGen {M : Matrix (l ⊕ l) (l ⊕ l) ℂ}
    (hM : ∀ X Y, HForm (M *ᵥ X) (M *ᵥ Y) = HForm X Y) {μ ν : ℂ}
    (hμν : μ * starRingEnd ℂ ν ≠ 1) :
    ∀ k m (X Y : (l ⊕ l) → ℂ), InGen M μ k X → InGen M ν m Y → HForm X Y = 0 := by
  intro k
  induction k with
  | zero =>
    intro m X Y hX _
    rw [inGen_zero_iff.1 hX, HForm_zero_left]
  | succ k ih =>
    intro m
    induction m with
    | zero =>
      intro X Y _ hY
      rw [inGen_zero_iff.1 hY, HForm_zero_right]
    | succ m ih' =>
      intro X Y hX hY
      have hX' := hX.succ
      have hY' := hY.succ
      have h1 : HForm X ((M - ν • 1) *ᵥ Y) = 0 := ih' X _ hX hY'
      have h2 : HForm ((M - μ • 1) *ᵥ X) Y = 0 := ih (m + 1) _ Y hX' hY
      have h3 : HForm ((M - μ • 1) *ᵥ X) ((M - ν • 1) *ᵥ Y) = 0 := ih m _ _ hX' hY'
      have key := hM X Y
      rw [mulVec_eq_smul_add M μ X, mulVec_eq_smul_add M ν Y, HForm_add_left, HForm_add_right,
        HForm_add_right, HForm_smul_left, HForm_smul_right, HForm_smul_right, HForm_smul_left,
        h1, h2, h3] at key
      have h4 : (μ * starRingEnd ℂ ν - 1) * HForm X Y = 0 := by linear_combination key
      rcases mul_eq_zero.1 h4 with h | h
      · exact absurd (sub_eq_zero.1 h) hμν
      · exact h

/-- **Corollary 7.3.4**, first half: `E_μ` is `H`-isotropic when `|μ| ≠ 1`. -/
theorem HForm_eq_zero_of_inGen_self {M : Matrix (l ⊕ l) (l ⊕ l) ℂ}
    (hM : ∀ X Y, HForm (M *ᵥ X) (M *ᵥ Y) = HForm X Y) {μ : ℂ} (hμ : μ * starRingEnd ℂ μ ≠ 1)
    {k m : ℕ} {X Y : (l ⊕ l) → ℂ} (hX : InGen M μ k X) (hY : InGen M μ m Y) : HForm X Y = 0 :=
  HForm_eq_zero_of_inGen hM hμ k m X Y hX hY

/-- **`H` is nondegenerate on `E_ν` when `|ν| = 1`.**  A vector of `E_ν` which is
`H`-orthogonal to `E_ν` is orthogonal to every generalised eigenspace, by Lemma 7.3.3, hence to
everything, and so vanishes. -/
theorem eq_zero_of_inGen_of_forall_HForm_eq_zero {M : Matrix (l ⊕ l) (l ⊕ l) ℂ}
    (hM : ∀ X Y, HForm (M *ᵥ X) (M *ᵥ Y) = HForm X Y) {ν : ℂ} (hν : ν * starRingEnd ℂ ν = 1)
    {k : ℕ} {X : (l ⊕ l) → ℂ} (hX : InGen M ν k X)
    (h : ∀ m (Y : (l ⊕ l) → ℂ), InGen M ν m Y → HForm X Y = 0) : X = 0 := by
  refine eq_zero_of_forall_HForm_eq_zero fun Z => ?_
  have hZ : Z ∈ ⨆ μ : ℂ, Module.End.maxGenEigenspace (Matrix.toLin' M) μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction (motive := fun Z => HForm X Z = 0) _ hZ ?_ ?_ ?_
  · intro μ Y hY
    rw [mem_maxGenEigenspace_iff] at hY
    obtain ⟨m, hY⟩ := hY
    by_cases hμ : μ = ν
    · subst hμ
      exact h m Y hY
    · refine HForm_eq_zero_of_inGen hM ?_ k m X Y hX hY
      intro hcon
      apply hμ
      have hν0 : ν ≠ 0 := by
        rintro rfl
        simp at hν
      have : starRingEnd ℂ μ = starRingEnd ℂ ν := by
        have h1 : ν * starRingEnd ℂ μ = ν * starRingEnd ℂ ν := by rw [hcon, hν]
        exact mul_left_cancel₀ hν0 h1
      exact (starRingEnd ℂ).injective this
  · exact HForm_zero_right X
  · intro Y Z hY hZ
    rw [HForm_add_right, hY, hZ, add_zero]

/-- The same for the real form `B = Im H`: `B` is nondegenerate on `E_ν` when `|ν| = 1`.
Replacing `Y` by `iY` recovers the real part of `H` from its imaginary part. -/
theorem eq_zero_of_inGen_of_forall_BForm_eq_zero {M : Matrix (l ⊕ l) (l ⊕ l) ℂ}
    (hM : ∀ X Y, HForm (M *ᵥ X) (M *ᵥ Y) = HForm X Y) {ν : ℂ} (hν : ν * starRingEnd ℂ ν = 1)
    {k : ℕ} {X : (l ⊕ l) → ℂ} (hX : InGen M ν k X)
    (h : ∀ m (Y : (l ⊕ l) → ℂ), InGen M ν m Y → BForm X Y = 0) : X = 0 := by
  refine eq_zero_of_inGen_of_forall_HForm_eq_zero hM hν hX fun m Y hY => ?_
  have hI : InGen M ν m (Complex.I • Y) := by
    unfold InGen at *
    rw [Matrix.mulVec_smul, hY, smul_zero]
  have h1 := h m Y hY
  have h2 := h m (Complex.I • Y) hI
  rw [BForm_eq_im] at h1 h2
  rw [HForm_smul_right] at h2
  have h3 : starRingEnd ℂ Complex.I = -Complex.I := Complex.conj_I
  rw [h3, neg_mul, Complex.neg_im, neg_eq_zero, Complex.I_mul_im] at h2
  exact Complex.ext h2 h1

end SymplecticEigen
end MorseFloer
