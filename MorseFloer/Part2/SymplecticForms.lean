import Mathlib

/-!
# The forms of §7.3.a, block sums, and real spectra

The definitions Chapter 7 shares with the bricks of the map `ρ`, kept under the namespace
`Chapter7` so that no name changes: the block sum of two symplectic matrices in the standard
coordinates (`blockSumEquiv`, `blockSum`), the multiplicities of the real eigenvalues and the
predicate "the spectrum is real" (`negEigenCount`, `posEigenCount`, `HasRealSpectrum`), and the
complex symplectic form `ω` on `ℂ²ⁿ` with the real form `B(X, Y) = Im ω(X, Ȳ)` of §7.3.a
(`stdFormC`, `conjVec`, `BForm`, `QForm`), with Lemma 7.3.1.  They are split off from
`Part2/Ch7.lean` so that the construction of `ρ` (`Part2/Rho.lean` and its companions) can be
built without importing the chapter, which then imports the construction to prove Theorem 7.1.3.
-/

open LinearMap (BilinForm)
open scoped Matrix

namespace MorseFloer
namespace Chapter7

/-- The reindexing `(Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n) ≃ Fin (m+n) ⊕ Fin (m+n)`
which turns a pair of symplectic vector spaces into their direct sum, matching
the splitting `p`-coordinates / `q`-coordinates on both sides. -/
def blockSumEquiv (m n : ℕ) :
    (Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n) ≃ Fin (m + n) ⊕ Fin (m + n) :=
  (Equiv.sumSumSumComm (Fin m) (Fin m) (Fin n) (Fin n)).trans
    (finSumFinEquiv.sumCongr finSumFinEquiv)

/-- The block sum `A ⊕ B` of a `2m × 2m` and a `2n × 2n` matrix, read as a
`2(m+n) × 2(m+n)` matrix in the standard symplectic coordinates. -/
def blockSum {m n : ℕ} (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    Matrix (Fin (m + n) ⊕ Fin (m + n)) (Fin (m + n) ⊕ Fin (m + n)) ℝ :=
  Matrix.reindex (blockSumEquiv m n) (blockSumEquiv m n) (Matrix.fromBlocks A 0 0 B)

/-- The total multiplicity of the negative real eigenvalues of a real matrix,
counted on the real characteristic polynomial; this is the `m₀` of §7.3.b. -/
noncomputable def negEigenCount {m : Type*} [DecidableEq m] [Fintype m]
    (A : Matrix m m ℝ) : ℕ :=
  Multiset.countP (fun x : ℝ => x < 0) A.charpoly.roots

/-- The total multiplicity of the positive real eigenvalues of a real matrix. -/
noncomputable def posEigenCount {m : Type*} [DecidableEq m] [Fintype m]
    (A : Matrix m m ℝ) : ℕ :=
  Multiset.countP (fun x : ℝ => 0 < x) A.charpoly.roots

/-- "`Spec A ⊆ ℝ`": the characteristic polynomial splits over `ℝ`, i.e. it has as
many real roots, with multiplicity, as the size of the matrix. -/
def HasRealSpectrum {m : Type*} [DecidableEq m] [Fintype m] (A : Matrix m m ℝ) : Prop :=
  A.charpoly.roots.card = Fintype.card m

/-! ## §7.3.a Preliminaries to the construction of `ρ`

On `ℂ²ⁿ`, the complex bilinear extension `ω` of the standard symplectic form
gives a *real* form `B(X, Y) = Im ω(X, Ȳ)`.  Lemma 7.3.1 says it is
`ℝ`-bilinear, symmetric and nondegenerate, and that it satisfies
`B(iX, iY) = B(X, Y)` and `B(X̄, Ȳ) = −B(X, Y)`.  These are the properties on
which the whole construction of `ρ` rests. -/

section Appendix

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The standard symplectic form of `ℂ²ⁿ`: the complex bilinear extension of the
real one, with the same matrix `−J`. -/
noncomputable def stdFormC (l : Type*) [DecidableEq l] [Fintype l] :
    BilinForm ℂ ((l ⊕ l) → ℂ) :=
  Matrix.toBilin' (-(Matrix.J l ℂ))

theorem stdFormC_apply (X Y : (l ⊕ l) → ℂ) :
    stdFormC l X Y = X ⬝ᵥ (-(Matrix.J l ℂ)) *ᵥ Y :=
  Matrix.toBilin'_apply' _ _ _

/-- Entrywise complex conjugation of a vector. -/
noncomputable def conjVec (X : (l ⊕ l) → ℂ) : (l ⊕ l) → ℂ := fun i => (starRingEnd ℂ) (X i)

omit [DecidableEq l] [Fintype l] in
@[simp] theorem conjVec_conjVec (X : (l ⊕ l) → ℂ) : conjVec (conjVec X) = X := by
  funext i
  simp [conjVec]

/-- `ω` is skew-symmetric on `ℂ²ⁿ`. -/
theorem stdFormC_skew (X Y : (l ⊕ l) → ℂ) : stdFormC l X Y = -stdFormC l Y X := by
  have hT : (-(Matrix.J l ℂ))ᵀ = -(-(Matrix.J l ℂ)) := by
    rw [Matrix.transpose_neg, Matrix.J_transpose]
  rw [stdFormC_apply, stdFormC_apply]
  nth_rewrite 1 [Matrix.dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose, hT, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]

/-- `ω` has real coefficients, so it commutes with complex conjugation. -/
theorem stdFormC_conjVec (X Y : (l ⊕ l) → ℂ) :
    stdFormC l (conjVec X) (conjVec Y) = (starRingEnd ℂ) (stdFormC l X Y) := by
  have hJ : (Matrix.J l ℂ).map (starRingEnd ℂ) = Matrix.J l ℂ := by simp
  have hentry : ∀ i j : l ⊕ l, (starRingEnd ℂ) (Matrix.J l ℂ i j) = Matrix.J l ℂ i j := by
    intro i j
    have h := congrArg (fun M : Matrix (l ⊕ l) (l ⊕ l) ℂ => M i j) hJ
    simpa [Matrix.map_apply] using h
  have hM : (-(Matrix.J l ℂ)).map (starRingEnd ℂ) = -(Matrix.J l ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.neg_apply, map_neg, hentry]
  have h1 : (starRingEnd ℂ) (stdFormC l X Y)
      = ((starRingEnd ℂ) ∘ X) ⬝ᵥ ((starRingEnd ℂ) ∘ ((-(Matrix.J l ℂ)) *ᵥ Y)) := by
    rw [stdFormC_apply]
    exact RingHom.map_dotProduct _ _ _
  have h2 : ((starRingEnd ℂ) ∘ ((-(Matrix.J l ℂ)) *ᵥ Y)) = (-(Matrix.J l ℂ)) *ᵥ conjVec Y := by
    funext i
    have h := RingHom.map_mulVec (starRingEnd ℂ) (-(Matrix.J l ℂ)) Y i
    rw [hM] at h
    exact h
  rw [h1, h2, stdFormC_apply]
  rfl

/-- The form `B(X, Y) = Im ω(X, Ȳ)` of §7.3.a. -/
noncomputable def BForm (X Y : (l ⊕ l) → ℂ) : ℝ := (stdFormC l X (conjVec Y)).im

/-- The quadratic form `Q(X) = B(X, X) = Im ω(X, X̄)` of §7.3.a. -/
noncomputable def QForm (X : (l ⊕ l) → ℂ) : ℝ := BForm X X

/-- **Lemma 7.3.1** (additivity in the first slot). -/
theorem BForm_add_left (X Y Z : (l ⊕ l) → ℂ) :
    BForm (X + Y) Z = BForm X Z + BForm Y Z := by
  simp [BForm, Complex.add_im]

/-- **Lemma 7.3.1** (real homogeneity in the first slot). -/
theorem BForm_smul_left (r : ℝ) (X Y : (l ⊕ l) → ℂ) :
    BForm ((r : ℂ) • X) Y = r * BForm X Y := by
  have hb : stdFormC l ((r : ℂ) • X) (conjVec Y) = (r : ℂ) * stdFormC l X (conjVec Y) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  show (stdFormC l ((r : ℂ) • X) (conjVec Y)).im = r * (stdFormC l X (conjVec Y)).im
  rw [hb, Complex.im_ofReal_mul]

/-- **Lemma 7.3.1** (`B` is symmetric). -/
theorem BForm_symm (X Y : (l ⊕ l) → ℂ) : BForm Y X = BForm X Y := by
  have h2 : stdFormC l (conjVec X) Y = (starRingEnd ℂ) (stdFormC l X (conjVec Y)) := by
    conv_lhs => rw [← conjVec_conjVec Y]
    exact stdFormC_conjVec X (conjVec Y)
  show (stdFormC l Y (conjVec X)).im = (stdFormC l X (conjVec Y)).im
  rw [stdFormC_skew Y (conjVec X), h2]
  simp

/-- **Lemma 7.3.1** (`B(X̄, Ȳ) = −B(X, Y)`). -/
theorem BForm_conjVec (X Y : (l ⊕ l) → ℂ) :
    BForm (conjVec X) (conjVec Y) = -BForm X Y := by
  have h2 : stdFormC l (conjVec X) Y = (starRingEnd ℂ) (stdFormC l X (conjVec Y)) := by
    conv_lhs => rw [← conjVec_conjVec Y]
    exact stdFormC_conjVec X (conjVec Y)
  show (stdFormC l (conjVec X) (conjVec (conjVec Y))).im = -(stdFormC l X (conjVec Y)).im
  rw [conjVec_conjVec, h2]
  simp

/-- **Lemma 7.3.1** (`B(iX, iY) = B(X, Y)`; this is why the subspaces on which
`Q` is definite are complex subspaces). -/
theorem BForm_smul_I (X Y : (l ⊕ l) → ℂ) :
    BForm (Complex.I • X) (Complex.I • Y) = BForm X Y := by
  have hc : conjVec (Complex.I • Y) = (-Complex.I) • conjVec Y := by
    funext i
    simp [conjVec]
  have hII : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have hb : stdFormC l (Complex.I • X) ((-Complex.I) • conjVec Y)
      = stdFormC l X (conjVec Y) := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul, hII, one_smul]
  show (stdFormC l (Complex.I • X) (conjVec (Complex.I • Y))).im
      = (stdFormC l X (conjVec Y)).im
  rw [hc, hb]

/-- `ω` is nondegenerate on `ℂ²ⁿ` (the complexification of Example 5.1.2). -/
theorem stdFormC_nondegenerate : (stdFormC l).Nondegenerate := by
  have hJ : IsUnit (Matrix.J l ℂ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_J l ℂ)
  have hM : (-(Matrix.J l ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hJ.neg).ne_zero
  have hnd : Matrix.Nondegenerate (-(Matrix.J l ℂ)) := Matrix.nondegenerate_of_det_ne_zero hM
  refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
  · refine hnd.eq_zero_of_ortho fun w => ?_
    rw [← Matrix.toBilin'_apply']
    exact hX w
  · refine hnd.eq_zero_of_ortho' fun w => ?_
    rw [← Matrix.toBilin'_apply']
    exact hY w

/-- **Lemma 7.3.1** (`B` is nondegenerate).  If `Im ω(X, Ȳ) = 0` for every `Y`,
then, replacing `Y` by `iY`, also the real part vanishes, so `X = 0`. -/
theorem BForm_eq_zero_of_forall {X : (l ⊕ l) → ℂ} (hX : ∀ Y, BForm X Y = 0) : X = 0 := by
  refine (stdFormC_nondegenerate (l := l)).1 X ?_
  intro Z
  have h1 : (stdFormC l X Z).im = 0 := by
    have h := hX (conjVec Z)
    rwa [BForm, conjVec_conjVec] at h
  have h2 : (stdFormC l X (Complex.I • Z)).im = 0 := by
    have h := hX (conjVec (Complex.I • Z))
    rwa [BForm, conjVec_conjVec] at h
  have h3 : stdFormC l X (Complex.I • Z) = Complex.I * stdFormC l X Z := by
    rw [map_smul, smul_eq_mul]
  rw [h3] at h2
  have h4 : (stdFormC l X Z).re = 0 := by
    simpa [Complex.mul_im] using h2
  exact Complex.ext (by simpa using h4) (by simpa using h1)

end Appendix

end Chapter7
end MorseFloer
