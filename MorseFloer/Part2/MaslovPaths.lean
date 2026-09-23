import MorseFloer.Part2.Ch5
import MorseFloer.Part2.LinearYorke
import MorseFloer.Part2.SymplecticForms

/-!
# Paths of symplectic matrices, and the blocks of Lemma 7.2.4

This file holds the part of §7.1.c and §7.2 of Audin–Damian that speaks only
about matrices and paths of matrices, without the index `μ`:

* the subsets `Sp(2n)⋆`, `Sp(2n)±` and `Σ` of the symplectic group (§7.1.c),
  the admissible paths and the homotopies between them (§7.1.c, §7.2.a), and
  the paths `t ↦ exp(tJS)` of Remark 7.1.2 — all moved here from `Ch7.lean`;
* the *real form* of a complex `n × n` matrix, `X + iY ↦ [[X, −Y], [Y, X]]`,
  a continuous ring homomorphism `M_n(ℂ) → M_{2n}(ℝ)` sending `i·Id` to `J`
  and unitary matrices to symplectic ones, hence commuting with `exp`; it is
  what turns `exp(θ J)` into the rotation `cos θ · Id + sin θ · J`
  (`exp_smul_J`), in every dimension;
* the algebra of block sums: `blockSum` is a continuous ring homomorphism from
  the product, so it commutes with `exp` (`exp_blockSum`) and the path of a
  block sum is the block sum of the paths (`expPath_blockSum`);
* the blocks of Lemma 7.2.4 — the rotation blocks `ℓπ · Id` (`ℓ` odd), whose
  path ends at `−Id`, and the hyperbolic block `diag(1, −1)` — with their
  eigenvalue counts, and the admissibility of their paths;
* the homotopy in `S` on which the computation of Lemma 7.2.4 rests: the
  paths `exp(t(ℓ+2)πJ) ⊕ exp(t(ℓ−2)πJ)` and `exp(tℓπJ) ⊕ exp(tℓπJ)` in `Sp(4)`
  are homotopic through admissible paths (`homotopicInS_rot`).  Both are real
  forms of paths in `U(2)` from `Id` to `−Id`, differing by the loop
  `diag(e^{2πit}, e^{−2πit})` of `SU(2)`, which is contracted explicitly:
  `γ_s(t) = [[e^{2πit} cos θ_s, −sin θ_s], [sin θ_s, e^{−2πit} cos θ_s]] · R_{−θ_s}`
  with `θ_s = sπ/2` runs from that loop (`s = 0`) to the constant loop
  (`s = 1`) through loops based at `Id`.

Chapter 7 uses these, together with the axioms of Proposition 7.2.1, to
compute the index of the paths `exp(tJS_k)` and prove Lemma 7.2.4.  Nothing
here is assumed.
-/

open scoped Matrix
open Complex (I)

namespace MorseFloer
namespace Chapter7

/-! ## §7.1.c The subset `Sp(2n)⋆`

The transformations relevant to the index are the symplectic ones without the
eigenvalue `1`; they form the open set `Sp(2n)⋆`, the complement in `Sp(2n)` of
the "hypersurface" `Σ` of matrices that do have it.  Since `det(A − Id)` is a
continuous nowhere-zero function on `Sp(2n)⋆`, that set is split by its sign
into the two open pieces `Sp(2n)+` and `Sp(2n)−`. -/

section Star

/-- `Sp(2n)⋆`, the symplectic matrices without the eigenvalue `1` (§7.1.c). -/
def symplecticStar (l : Type*) [DecidableEq l] [Fintype l] :
    Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  {A | A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det ≠ 0}

/-- `Sp(2n)+`, the part of `Sp(2n)⋆` where `det(A − Id) > 0` (§7.1.c). -/
def symplecticPlus (l : Type*) [DecidableEq l] [Fintype l] :
    Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  {A | A ∈ Matrix.symplecticGroup l ℝ ∧ 0 < (A - 1).det}

/-- `Sp(2n)−`, the part of `Sp(2n)⋆` where `det(A − Id) < 0` (§7.1.c). -/
def symplecticMinus (l : Type*) [DecidableEq l] [Fintype l] :
    Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  {A | A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det < 0}

/-- `Σ`, the symplectic matrices that *do* have the eigenvalue `1` (§7.1.c). -/
def sigmaSet (l : Type*) [DecidableEq l] [Fintype l] :
    Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  {A | A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det = 0}

variable {l : Type*} [DecidableEq l] [Fintype l] {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}

theorem mem_symplecticStar_iff :
    A ∈ symplecticStar l ↔ A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det ≠ 0 := Iff.rfl

theorem mem_symplecticPlus_iff :
    A ∈ symplecticPlus l ↔ A ∈ Matrix.symplecticGroup l ℝ ∧ 0 < (A - 1).det := Iff.rfl

theorem mem_symplecticMinus_iff :
    A ∈ symplecticMinus l ↔ A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det < 0 := Iff.rfl

theorem mem_sigmaSet_iff :
    A ∈ sigmaSet l ↔ A ∈ Matrix.symplecticGroup l ℝ ∧ (A - 1).det = 0 := Iff.rfl

/-- `Sp(2n)⋆` is the union of the two open pieces `Sp(2n)±`; in particular it is
not connected (§7.1.c). -/
theorem symplecticStar_eq_union :
    symplecticStar l = symplecticPlus l ∪ symplecticMinus l := by
  ext B
  simp only [mem_symplecticStar_iff, mem_symplecticPlus_iff, mem_symplecticMinus_iff,
    Set.mem_union]
  constructor
  · rintro ⟨hB, hne⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr ⟨hB, h⟩
    · exact Or.inl ⟨hB, h⟩
  · rintro (⟨hB, h⟩ | ⟨hB, h⟩)
    · exact ⟨hB, ne_of_gt h⟩
    · exact ⟨hB, ne_of_lt h⟩

/-- The two pieces of `Sp(2n)⋆` are disjoint. -/
theorem disjoint_symplecticPlus_minus :
    Disjoint (symplecticPlus l) (symplecticMinus l) := by
  rw [Set.disjoint_left]
  rintro B ⟨-, h1⟩ ⟨-, h2⟩
  exact absurd h1 (not_lt.mpr h2.le)

/-- `Sp(2n)` is the disjoint union of `Σ` and `Sp(2n)⋆`. -/
theorem symplecticGroup_eq_union :
    (Matrix.symplecticGroup l ℝ : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ))
      = sigmaSet l ∪ symplecticStar l := by
  ext B
  simp only [SetLike.mem_coe, mem_sigmaSet_iff, mem_symplecticStar_iff, Set.mem_union]
  constructor
  · intro hB
    by_cases h : (B - 1).det = 0
    · exact Or.inl ⟨hB, h⟩
    · exact Or.inr ⟨hB, h⟩
  · rintro (⟨hB, -⟩ | ⟨hB, -⟩) <;> exact hB

theorem disjoint_sigmaSet_symplecticStar :
    Disjoint (sigmaSet l) (symplecticStar l) := by
  rw [Set.disjoint_left]
  rintro B ⟨-, h1⟩ ⟨-, h2⟩
  exact h2 h1

/-- The reference matrix `W⁺ = −Id` of §7.2.a lies in `Sp(2n)+`: indeed
`det(−Id − Id) = (−2)^{2n} > 0`. -/
theorem neg_one_mem_symplecticPlus :
    (-1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) ∈ symplecticPlus l := by
  refine mem_symplecticPlus_iff.mpr ⟨SymplecticGroup.neg_mem (Submonoid.one_mem _), ?_⟩
  have h : (-1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) - 1 = (-2 : ℝ) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) := by
    rw [show (-2 : ℝ) = (-1) + (-1) by norm_num, add_smul, neg_one_smul]
    abel
  rw [h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_sum]
  have hne : ((-2 : ℝ) ^ Fintype.card l) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc (0 : ℝ) < ((-2 : ℝ) ^ Fintype.card l) * ((-2 : ℝ) ^ Fintype.card l) :=
        mul_self_pos.mpr hne
    _ = (-2 : ℝ) ^ (Fintype.card l + Fintype.card l) := (pow_add _ _ _).symm

/-- `−Id` lies in `Sp(2n)⋆`. -/
theorem neg_one_mem_symplecticStar :
    (-1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) ∈ symplecticStar l :=
  ⟨neg_one_mem_symplecticPlus.1, ne_of_gt neg_one_mem_symplecticPlus.2⟩

end Star

/-! ## Remark 7.1.2: the paths `exp(tJS)` -/

section ExpPath

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- **Remark 7.1.2.**  For a symmetric `S`, `t ↦ exp(t J S)` is a path in the
symplectic group: this is the linearised flow of an autonomous Hamiltonian at a
critical point, with `S` its Hessian.  It also proves Exercise 15 of the book,
quoted in §7.2.c. -/
theorem exp_smul_J_mul_mem_symplecticGroup {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : Sᵀ = S)
    (t : ℝ) : NormedSpace.exp (t • (Matrix.J l ℝ * S)) ∈ Matrix.symplecticGroup l ℝ := by
  refine Chapter5.exp_mem_symplecticGroup ?_
  have h1 : (Matrix.J l ℝ * S)ᵀ * Matrix.J l ℝ = S := by
    rw [Matrix.transpose_mul, hS, Matrix.J_transpose, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, Matrix.J_squared, Matrix.mul_neg, Matrix.mul_one, neg_neg]
  have h2 : Matrix.J l ℝ * (Matrix.J l ℝ * S) = -S := by
    rw [← Matrix.mul_assoc, Matrix.J_squared, Matrix.neg_mul, Matrix.one_mul]
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, h1, h2, smul_neg,
    add_neg_cancel]

/-- The path of Remark 7.1.2 starts at the identity. -/
theorem exp_smul_J_mul_zero (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    NormedSpace.exp ((0 : ℝ) • (Matrix.J l ℝ * S)) = 1 := by
  rw [zero_smul, NormedSpace.exp_zero]

/-- **Remark 7.1.2** (second half).  If `S` is symmetric, invertible, and all its
eigenvalues have absolute value `< 2π`, then `J S` has no eigenvalue `2ikπ` and
therefore `exp(J S)` does not have the eigenvalue `1`, i.e. the endpoint of the
path lies in `Sp(2n)⋆`.

Proved in `Part2/LinearYorke.lean`, not through the spectrum of `exp` but
through Yorke's theorem (Proposition 6.1.5): a fixed vector `v ≠ 0` of `exp(JS)`
would give a nonconstant `1`-periodic orbit `t ↦ exp(tJS) v` of the linear field
`x ↦ JSx`, whose Lipschitz constant is the Euclidean operator norm
`‖JS‖ = ‖S‖ = max |λ_i(S)| < 2π`; the norm bound comes from Mathlib's spectral
theorem for symmetric matrices. -/
theorem exp_J_mul_mem_symplecticStar {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : Sᵀ = S)
    (hdet : S.det ≠ 0)
    (hnorm : ∀ c : ℝ, (S - c • 1).det = 0 → |c| < 2 * Real.pi) :
    NormedSpace.exp ((1 : ℝ) • (Matrix.J l ℝ * S)) ∈ symplecticStar l := by
  refine ⟨exp_smul_J_mul_mem_symplecticGroup hS 1, ?_⟩
  rw [one_smul]
  have hJdet : (Matrix.J l ℝ).det ≠ 0 := by
    intro h
    have := Matrix.J_det_mul_J_det (l := l) (R := ℝ)
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hJ : (Matrix.J l ℝ)ᵀ * Matrix.J l ℝ = 1 := by
    rw [Matrix.J_transpose, Matrix.neg_mul, Matrix.J_squared, neg_neg]
  refine LinearYorke.det_exp_sub_one_ne_zero ?_ ?_
  · rw [Matrix.det_mul]; exact mul_ne_zero hJdet hdet
  · obtain ⟨M, hM, hbound⟩ :=
      LinearYorke.exists_norm_toEuclideanCLM_apply_le hS Real.two_pi_pos hnorm
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ M.coe_nonneg fun w => ?_) hM
    rw [map_mul, mul_apply_eq_comp, LinearYorke.norm_toEuclideanCLM_apply_of_transpose_mul hJ]
    exact hbound w

/-- The path `t ↦ exp(tJS)` of Remark 7.1.2, as a function on `ℝ`. -/
noncomputable def expPath (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ :=
  fun t => NormedSpace.exp (t • (Matrix.J l ℝ * S))

theorem expPath_apply (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) (t : ℝ) :
    expPath S t = NormedSpace.exp (t • (Matrix.J l ℝ * S)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `t ↦ exp(tX)` is continuous, for any matrix `X`.  The normed-ring structure
that `exp_continuous` asks for is Mathlib's scoped operator norm, whose topology
is the product topology of the statement. -/
theorem continuous_exp_smul (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

theorem continuous_expPath (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Continuous (expPath S) :=
  continuous_exp_smul _

end ExpPath

/-! ## §7.1.c, §7.2.a Admissible paths and homotopies -/

section Index

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The space `S` of §7.1.c: paths of symplectic matrices starting at the
identity and ending in `Sp(2n)⋆`.  Only the values on `[0,1]` matter; the
functions are defined on all of `ℝ` to avoid subtype friction. -/
structure IsAdmissiblePath (ψ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ) : Prop where
  /-- The path is continuous. -/
  continuous : Continuous ψ
  /-- It takes symplectic values. -/
  mem : ∀ t, ψ t ∈ Matrix.symplecticGroup l ℝ
  /-- It starts at the identity. -/
  start : ψ 0 = 1
  /-- Its endpoint has no eigenvalue `1`. -/
  endpoint : ψ 1 ∈ symplecticStar l

/-- Homotopy inside `S`: a continuous family of admissible paths. -/
def HomotopicInS (ψ₀ ψ₁ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ) : Prop :=
  ∃ H : ℝ → ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ,
    Continuous (fun p : ℝ × ℝ => H p.1 p.2) ∧ (∀ s, IsAdmissiblePath (H s)) ∧
      H 0 = ψ₀ ∧ H 1 = ψ₁

/-- The path `exp(tJS)` of a small symmetric invertible `S` is admissible: this
is Remark 7.1.2 in the language of §7.2. -/
theorem isAdmissiblePath_expPath {S : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hS : Sᵀ = S)
    (hdet : S.det ≠ 0)
    (hnorm : ∀ c : ℝ, (S - c • 1).det = 0 → |c| < 2 * Real.pi) :
    IsAdmissiblePath (expPath S) where
  continuous := continuous_expPath S
  mem := exp_smul_J_mul_mem_symplecticGroup hS
  start := exp_smul_J_mul_zero S
  endpoint := exp_J_mul_mem_symplecticStar hS hdet hnorm

end Index

/-! ## The real form of a complex matrix -/

section RealForm

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The real form `[[X, −Y], [Y, X]]` of the complex matrix `X + iY`: the
matrix of multiplication by `X + iY` on `ℂⁿ = ℝⁿ ⊕ iℝⁿ`, in the coordinates in
which `J` is multiplication by `i`. -/
def realForm (M : Matrix l l ℂ) : Matrix (l ⊕ l) (l ⊕ l) ℝ :=
  Matrix.fromBlocks (M.map Complex.re) (-(M.map Complex.im)) (M.map Complex.im)
    (M.map Complex.re)

omit [Fintype l] in
theorem realForm_one : realForm (1 : Matrix l l ℂ) = 1 := by
  have h1 : (1 : Matrix l l ℂ).map Complex.re = 1 :=
    Matrix.map_one _ Complex.zero_re Complex.one_re
  have h2 : (1 : Matrix l l ℂ).map Complex.im = 0 := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [realForm, h1, h2, neg_zero, Matrix.fromBlocks_one]

omit [DecidableEq l] [Fintype l] in
theorem realForm_zero : realForm (0 : Matrix l l ℂ) = 0 := by
  ext (i | i) (j | j) <;> simp [realForm]

omit [DecidableEq l] [Fintype l] in
theorem realForm_add (M N : Matrix l l ℂ) : realForm (M + N) = realForm M + realForm N := by
  ext (i | i) (j | j) <;> simp [realForm]
  ring

omit [DecidableEq l] [Fintype l] in
theorem realForm_neg (M : Matrix l l ℂ) : realForm (-M) = -realForm M := by
  ext (i | i) (j | j) <;> simp [realForm]

omit [DecidableEq l] [Fintype l] in
theorem realForm_smul (r : ℝ) (M : Matrix l l ℂ) : realForm (r • M) = r • realForm M := by
  ext (i | i) (j | j) <;> simp [realForm]

omit [DecidableEq l] in
theorem realForm_mul (M N : Matrix l l ℂ) : realForm (M * N) = realForm M * realForm N := by
  have hre : (M * N).map Complex.re
      = M.map Complex.re * N.map Complex.re - M.map Complex.im * N.map Complex.im := by
    ext i j
    simp [Matrix.mul_apply, Complex.mul_re, Finset.sum_sub_distrib]
  have him : (M * N).map Complex.im
      = M.map Complex.re * N.map Complex.im + M.map Complex.im * N.map Complex.re := by
    ext i j
    simp [Matrix.mul_apply, Complex.mul_im, Finset.sum_add_distrib]
  rw [realForm, realForm, realForm, Matrix.fromBlocks_multiply, hre, him]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    (try simp only [Matrix.neg_mul, Matrix.mul_neg, sub_eq_add_neg, neg_add]) <;> abel

omit [DecidableEq l] [Fintype l] in
/-- The real form of the adjoint is the transpose of the real form. -/
theorem realForm_transpose (M : Matrix l l ℂ) : (realForm M)ᵀ = realForm Mᴴ := by
  have hre : Mᴴ.map Complex.re = (M.map Complex.re)ᵀ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have him : Mᴴ.map Complex.im = -(M.map Complex.im)ᵀ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  rw [realForm, realForm, Matrix.fromBlocks_transpose, hre, him, neg_neg, Matrix.transpose_neg]

omit [Fintype l] in
/-- The real form of `i · Id` is `J`. -/
theorem realForm_I : realForm (I • (1 : Matrix l l ℂ)) = Matrix.J l ℝ := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;>
    simp [realForm, Matrix.J, h]

/-- The real form, as an `ℝ`-algebra homomorphism `M_n(ℂ) → M_{2n}(ℝ)`. -/
def realFormHom : Matrix l l ℂ →ₐ[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ where
  toFun := realForm
  map_one' := realForm_one
  map_mul' := realForm_mul
  map_zero' := realForm_zero
  map_add' := realForm_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, realForm_smul,
      realForm_one]

theorem realFormHom_apply (M : Matrix l l ℂ) : realFormHom M = realForm M := rfl

theorem continuous_realForm : Continuous (realForm : Matrix l l ℂ → Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  LinearMap.continuous_of_finiteDimensional (realFormHom (l := l)).toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- The real form commutes with the exponential, being a continuous ring
homomorphism. -/
theorem exp_realForm (M : Matrix l l ℂ) :
    NormedSpace.exp (realForm M) = realForm (NormedSpace.exp M) := by
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp realFormHom
    (LinearMap.continuous_of_finiteDimensional (realFormHom (l := l)).toLinearMap) M).symm

set_option backward.isDefEq.respectTransparency false in
/-- `exp(z · Id) = e^z · Id`. -/
theorem exp_smul_one (z : ℂ) :
    NormedSpace.exp (z • (1 : Matrix l l ℂ)) = Complex.exp z • (1 : Matrix l l ℂ) := by
  open scoped Matrix.Norms.Operator in
  exact (by
    rw [Complex.exp_eq_exp_ℂ, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one]
    exact (NormedSpace.algebraMap_exp_comm z).symm)

/-- `exp(θ J)` is the real form of `e^{iθ} · Id`, i.e. the rotation
`cos θ · Id + sin θ · J`. -/
theorem exp_smul_J (θ : ℝ) :
    NormedSpace.exp (θ • Matrix.J l ℝ) = realForm (Complex.exp (θ * I) • (1 : Matrix l l ℂ)) := by
  rw [← realForm_I, ← realForm_smul, exp_realForm, ← exp_smul_one]
  congr 2
  rw [mul_smul]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) θ _

/-- The real form of a unitary matrix is symplectic: it is orthogonal and
commutes with `J`. -/
theorem realForm_mem_symplecticGroup {M : Matrix l l ℂ} (hM : M ∈ Matrix.unitaryGroup l ℂ) :
    realForm M ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff, ← realForm_I, realForm_transpose, ← realForm_mul, ← realForm_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff.mp hM]

end RealForm

/-! ## Block sums -/

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

/-- `J` splits along the block sum. -/
theorem J_blockSum : Matrix.J (Fin (m + n)) ℝ = blockSum (Matrix.J (Fin m) ℝ) (Matrix.J (Fin n) ℝ) := by
  ext k k'
  obtain ⟨i, rfl⟩ := (blockSumEquiv m n).surjective k
  obtain ⟨j, rfl⟩ := (blockSumEquiv m n).surjective k'
  rw [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
    simp [blockSumEquiv_inl_inl, blockSumEquiv_inl_inr, blockSumEquiv_inr_inl,
      blockSumEquiv_inr_inr, Matrix.J, Matrix.one_apply, Fin.ext_iff] <;> omega

theorem blockSum_eq (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    blockSum A B = Matrix.reindexAlgEquiv ℝ ℝ (blockSumEquiv m n) (Matrix.fromBlocks A 0 0 B) :=
  (congrFun (Matrix.coe_reindexAlgEquiv ℝ ℝ (blockSumEquiv m n)) _).symm

theorem blockSum_one : blockSum (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) = 1 := by
  rw [blockSum_eq, Matrix.fromBlocks_one, map_one]

theorem blockSum_zero : blockSum (0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) = 0 := by
  rw [blockSum_eq, Matrix.fromBlocks_zero, map_zero]

theorem blockSum_mul (A A' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B B' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    blockSum (A * A') (B * B') = blockSum A B * blockSum A' B' := by
  rw [blockSum_eq, blockSum_eq, blockSum_eq, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem blockSum_add (A A' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B B' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    blockSum (A + A') (B + B') = blockSum A B + blockSum A' B' := by
  rw [blockSum_eq, blockSum_eq, blockSum_eq, ← map_add, Matrix.fromBlocks_add]
  simp only [add_zero]

theorem blockSum_sub (A A' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B B' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    blockSum (A - A') (B - B') = blockSum A B - blockSum A' B' := by
  rw [blockSum_eq, blockSum_eq, blockSum_eq, ← map_sub]
  congr 1
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]

theorem blockSum_smul (r : ℝ) (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    blockSum (r • A) (r • B) = r • blockSum A B := by
  rw [blockSum_eq, blockSum_eq, ← map_smul, Matrix.fromBlocks_smul]
  simp only [smul_zero]

theorem blockSum_transpose (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (blockSum A B)ᵀ = blockSum Aᵀ Bᵀ := by
  simp only [blockSum, Matrix.transpose_reindex, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero]

theorem det_blockSum (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (blockSum A B).det = A.det * B.det := by
  rw [blockSum, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]

theorem blockSum_sub_one (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    blockSum A B - 1 = blockSum (A - 1) (B - 1) := by
  rw [blockSum_sub, blockSum_one]

/-- The block sum of two symplectic matrices is symplectic. -/
theorem blockSum_mem_symplecticGroup {A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ}
    {B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hA : A ∈ Matrix.symplecticGroup (Fin m) ℝ)
    (hB : B ∈ Matrix.symplecticGroup (Fin n) ℝ) :
    blockSum A B ∈ Matrix.symplecticGroup (Fin (m + n)) ℝ := by
  rw [SymplecticGroup.mem_iff, J_blockSum, blockSum_transpose, ← blockSum_mul, ← blockSum_mul,
    SymplecticGroup.mem_iff.mp hA, SymplecticGroup.mem_iff.mp hB]

/-- The block sum, as an `ℝ`-algebra homomorphism from the product. -/
def blockSumHom (m n : ℕ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ × Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ →ₐ[ℝ]
      Matrix (Fin (m + n) ⊕ Fin (m + n)) (Fin (m + n) ⊕ Fin (m + n)) ℝ where
  toFun p := blockSum p.1 p.2
  map_one' := blockSum_one
  map_mul' p q := blockSum_mul _ _ _ _
  map_zero' := blockSum_zero
  map_add' p q := blockSum_add _ _ _ _
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.smul_snd, Prod.fst_one,
      Prod.snd_one]
    rw [blockSum_smul, blockSum_one]

theorem blockSumHom_apply (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ ×
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) : blockSumHom m n p = blockSum p.1 p.2 := rfl

theorem continuous_blockSum :
    Continuous fun p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ ×
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ => blockSum p.1 p.2 :=
  LinearMap.continuous_of_finiteDimensional (blockSumHom m n).toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- The exponential of a block sum is the block sum of the exponentials. -/
theorem exp_blockSum (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    NormedSpace.exp (blockSum X Y) = blockSum (NormedSpace.exp X) (NormedSpace.exp Y) := by
  open scoped Matrix.Norms.Operator in
  exact (by
    have h := NormedSpace.map_exp (blockSumHom m n)
      (LinearMap.continuous_of_finiteDimensional (blockSumHom m n).toLinearMap) (X, Y)
    have hXY : NormedSpace.exp (X, Y) = (NormedSpace.exp X, NormedSpace.exp Y) :=
      Prod.ext (Prod.fst_exp _) (Prod.snd_exp _)
    rw [hXY] at h
    exact h.symm)

/-- The path of a block sum is the block sum of the paths. -/
theorem expPath_blockSum (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    expPath (blockSum S B) = fun t => blockSum (expPath S t) (expPath B t) := by
  funext t
  simp only [expPath_apply]
  rw [J_blockSum, ← blockSum_mul, ← blockSum_smul, exp_blockSum]

/-- The block sum of two admissible paths is admissible. -/
theorem isAdmissiblePath_blockSum {ψ₀ : ℝ → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ}
    {ψ₁ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (h₀ : IsAdmissiblePath ψ₀)
    (h₁ : IsAdmissiblePath ψ₁) : IsAdmissiblePath (fun t => blockSum (ψ₀ t) (ψ₁ t)) where
  continuous := continuous_blockSum.comp (h₀.continuous.prodMk h₁.continuous)
  mem t := blockSum_mem_symplecticGroup (h₀.mem t) (h₁.mem t)
  start := by
    show blockSum (ψ₀ 0) (ψ₁ 0) = 1
    rw [h₀.start, h₁.start, blockSum_one]
  endpoint := by
    refine ⟨blockSum_mem_symplecticGroup h₀.endpoint.1 h₁.endpoint.1, ?_⟩
    show (blockSum (ψ₀ 1) (ψ₁ 1) - 1).det ≠ 0
    rw [blockSum_sub_one, det_blockSum]
    exact mul_ne_zero h₀.endpoint.2 h₁.endpoint.2

/-- The complex block sum, in the coordinates of `blockSum`. -/
def blockSumC (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

/-- The block sum of two real forms is the real form of the complex block sum. -/
theorem blockSum_realForm (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    blockSum (realForm A) (realForm B) = realForm (blockSumC A B) := by
  ext k k'
  obtain ⟨i, rfl⟩ := (blockSumEquiv m n).surjective k
  obtain ⟨j, rfl⟩ := (blockSumEquiv m n).surjective k'
  rw [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
    simp [blockSumEquiv_inl_inl, blockSumEquiv_inl_inr, blockSumEquiv_inr_inl,
      blockSumEquiv_inr_inr, realForm, blockSumC]

theorem blockSumC_smul_one (z : ℂ) :
    blockSumC (z • (1 : Matrix (Fin m) (Fin m) ℂ)) (z • (1 : Matrix (Fin n) (Fin n) ℂ)) = z • 1 := by
  have h : Matrix.fromBlocks (z • (1 : Matrix (Fin m) (Fin m) ℂ)) 0 0
      (z • (1 : Matrix (Fin n) (Fin n) ℂ)) = z • Matrix.fromBlocks 1 0 0 1 := by
    rw [Matrix.fromBlocks_smul]; simp only [smul_zero]
  rw [blockSumC, h, Matrix.fromBlocks_one, ← Matrix.coe_reindexAlgEquiv ℂ ℂ, map_smul, map_one]

end BlockSum

/-! ## The blocks of Lemma 7.2.4 -/

section Blocks

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The eigenvalue count of a diagonal matrix. -/
theorem negEigenCount_diagonal {ι : Type*} [DecidableEq ι] [Fintype ι] (d : ι → ℝ) :
    negEigenCount (Matrix.diagonal d) = (Finset.univ.filter fun i => d i < 0).card := by
  have h : (fun i => Polynomial.X - Polynomial.C (d i))
      = (fun a : ℝ => Polynomial.X - Polynomial.C a) ∘ d := rfl
  rw [negEigenCount, Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod, h,
    ← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C, Multiset.countP_map]
  rfl

theorem negEigenCount_smul_one (c : ℝ) :
    negEigenCount (c • (1 : Matrix l l ℝ)) = if c < 0 then Fintype.card l else 0 := by
  rw [Matrix.smul_one_eq_diagonal, negEigenCount_diagonal]
  split_ifs with hc
  · rw [Finset.filter_true_of_mem fun _ _ => hc, Finset.card_univ]
  · rw [Finset.filter_false_of_mem fun _ _ => hc, Finset.card_empty]

theorem det_smul_one_ne_zero {c : ℝ} (hc : c ≠ 0) : (c • (1 : Matrix l l ℝ)).det ≠ 0 := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ hc

/-- The only eigenvalue of `c · Id` is `c`. -/
theorem eq_of_det_smul_one_sub_eq_zero {c c' : ℝ}
    (h : (c • (1 : Matrix l l ℝ) - c' • 1).det = 0) : c' = c := by
  rw [← sub_smul, Matrix.det_smul, Matrix.det_one, mul_one] at h
  have := (pow_eq_zero_iff'.mp h).1
  linarith [sub_eq_zero.mp this]

/-- The path `exp(tJ · (c Id)) = exp(tc J)` is the rotation of angle `tc`, the
real form of `e^{itc} · Id`. -/
theorem expPath_smul_one (c t : ℝ) :
    expPath (c • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ)) t
      = realForm (Complex.exp ((t * c : ℝ) * I) • (1 : Matrix l l ℂ)) := by
  rw [expPath_apply, Matrix.mul_smul, Matrix.mul_one, smul_smul, exp_smul_J]

/-- `e^{iℓπ} = −1` for odd `ℓ`. -/
theorem exp_odd_mul_pi_mul_I {k : ℤ} (hk : Odd k) :
    Complex.exp ((k : ℂ) * Real.pi * I) = -1 := by
  obtain ⟨q, rfl⟩ := hk
  have : ((2 * q + 1 : ℤ) : ℂ) * Real.pi * I = q * (2 * Real.pi * I) + Real.pi * I := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

/-- The path `exp(tℓπJ)` for odd `ℓ` is admissible: it ends at `−Id`. -/
theorem isAdmissiblePath_expPath_rot {k : ℤ} (hk : Odd k) :
    IsAdmissiblePath (expPath (((k : ℝ) * Real.pi) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ))) where
  continuous := continuous_expPath _
  mem := exp_smul_J_mul_mem_symplecticGroup (by rw [Matrix.transpose_smul, Matrix.transpose_one])
  start := exp_smul_J_mul_zero _
  endpoint := by
    rw [expPath_smul_one]
    have h : Complex.exp (((1 : ℝ) * ((k : ℝ) * Real.pi) : ℝ) * I) = -1 := by
      rw [← exp_odd_mul_pi_mul_I hk]; congr 1; push_cast; ring
    rw [h, neg_one_smul, realForm_neg, realForm_one]
    exact neg_one_mem_symplecticStar

/-- Hypothesis of the normalisation axiom for `c · Id` with `|c| < 2π`. -/
theorem abs_lt_of_det_smul_one_sub_eq_zero {c : ℝ} (hc : |c| < 2 * Real.pi) (c' : ℝ)
    (h : (c • (1 : Matrix l l ℝ) - c' • 1).det = 0) : |c'| < 2 * Real.pi := by
  rw [eq_of_det_smul_one_sub_eq_zero h]; exact hc

/-- The hyperbolic block `diag(1, −1)` of the proof of Lemma 7.2.4. -/
def hypBlock : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))

theorem hypBlock_transpose : hypBlockᵀ = hypBlock := Matrix.diagonal_transpose _

theorem det_hypBlock : hypBlock.det = -1 := by
  rw [hypBlock, Matrix.det_diagonal, Fintype.prod_sum_type]
  simp

theorem negEigenCount_hypBlock : negEigenCount hypBlock = 1 := by
  rw [hypBlock, negEigenCount_diagonal]
  have : (Finset.univ.filter fun i : Fin 1 ⊕ Fin 1 =>
      Sum.elim (fun _ => (1 : ℝ)) (fun _ => -1) i < 0) = {Sum.inr 0} := by
    ext (i | i) <;> simp [Fin.eq_zero i]
  rw [this, Finset.card_singleton]

theorem abs_lt_of_det_hypBlock_sub_eq_zero (c : ℝ) (h : (hypBlock - c • 1).det = 0) :
    |c| < 2 * Real.pi := by
  rw [hypBlock, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub, Matrix.det_diagonal,
    Finset.prod_eq_zero_iff] at h
  obtain ⟨i, -, hi⟩ := h
  have hpi : 3 < Real.pi := Real.pi_gt_three
  rcases i with i | i
  · simp only [Sum.elim_inl] at hi
    rw [show c = 1 by linarith, abs_one]; linarith
  · simp only [Sum.elim_inr] at hi
    rw [show c = -1 by linarith, abs_neg, abs_one]; linarith

theorem isAdmissiblePath_expPath_hypBlock : IsAdmissiblePath (expPath hypBlock) :=
  isAdmissiblePath_expPath hypBlock_transpose (by rw [det_hypBlock]; norm_num)
    abs_lt_of_det_hypBlock_sub_eq_zero

end Blocks

/-! ## The homotopy in `S` behind Lemma 7.2.4 -/

section Homotopy

/-- The matrix `[[u c, −s], [s, ū c]]`, unitary when `|u| = 1` and `c² + s² = 1`. -/
def gam (u : ℂ) (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u * c, -(s : ℂ); (s : ℂ), (starRingEnd ℂ) u * c]

theorem gam_mem_unitaryGroup {u : ℂ} (hu : u * (starRingEnd ℂ) u = 1) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) : gam u c s ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gam, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · linear_combination (c : ℂ) ^ 2 * hu + hcs'
  · ring
  · ring
  · linear_combination (c : ℂ) ^ 2 * hu + hcs'

theorem smul_one_mem_unitaryGroup {z : ℂ} (hz : z * (starRingEnd ℂ) z = 1) :
    z • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, one_mul,
    Complex.star_def, hz, one_smul]

theorem exp_mul_conj_exp (x : ℝ) :
    Complex.exp ((x : ℂ) * I) * (starRingEnd ℂ) (Complex.exp ((x : ℂ) * I)) = 1 := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- `γ(1, c, s) · γ(1, c, −s) = Id`: the rotation and its inverse. -/
theorem gam_one_mul_gam_one_neg {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    gam 1 c s * gam 1 c (-s) = 1 := by
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gam, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hcs'
  · ring
  · ring
  · linear_combination hcs'

/-- At `θ = π/2` the product is the identity, whatever `u` is. -/
theorem gam_zero_one_mul (u : ℂ) : gam u 0 1 * gam 1 0 (-1) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gam, Matrix.mul_apply, Fin.sum_univ_two]

/-- At `θ = 0` the product is `diag(u, ū)`. -/
theorem gam_one_zero_mul (u : ℂ) : gam u 1 0 * gam 1 1 0 = !![u, 0; 0, (starRingEnd ℂ) u] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gam, Matrix.mul_apply, Fin.sum_univ_two]

theorem smul_fin_two (e a b c d : ℂ) : e • !![a, b; c, d] = !![e * a, e * b; e * c, e * d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem continuous_gam {X : Type*} [TopologicalSpace X] {u : X → ℂ} {c s : X → ℝ}
    (hu : Continuous u) (hc : Continuous c) (hs : Continuous s) :
    Continuous fun x => gam (u x) (c x) (s x) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [gam, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  · exact hu.mul (Complex.continuous_ofReal.comp hc)
  · exact (Complex.continuous_ofReal.comp hs).neg
  · exact Complex.continuous_ofReal.comp hs
  · exact (Complex.continuous_conj.comp hu).mul (Complex.continuous_ofReal.comp hc)

/-- The family of paths in `U(2)`: `e^{iℓπt} · γ(e^{2πit}, cos θ_s, sin θ_s) · R_{−θ_s}`,
with `θ_s = sπ/2`. -/
noncomputable def uFam (k : ℤ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.exp (((k : ℝ) * Real.pi * t : ℝ) * I) •
    (gam (Complex.exp ((2 * Real.pi * t : ℝ) * I)) (Real.cos (s * Real.pi / 2))
        (Real.sin (s * Real.pi / 2)) *
      gam 1 (Real.cos (s * Real.pi / 2)) (-Real.sin (s * Real.pi / 2)))

/-- Its real form: the homotopy in `Sp(4)`. -/
noncomputable def hFam (k : ℤ) (s t : ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  realForm (uFam k s t)

theorem uFam_mem_unitaryGroup (k : ℤ) (s t : ℝ) : uFam k s t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hcs : Real.cos (s * Real.pi / 2) ^ 2 + Real.sin (s * Real.pi / 2) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  have hcs' : Real.cos (s * Real.pi / 2) ^ 2 + (-Real.sin (s * Real.pi / 2)) ^ 2 = 1 := by
    rw [neg_sq]; exact hcs
  have h1 := smul_one_mem_unitaryGroup (exp_mul_conj_exp ((k : ℝ) * Real.pi * t))
  have h2 := gam_mem_unitaryGroup (exp_mul_conj_exp (2 * Real.pi * t)) hcs
  have h3 := gam_mem_unitaryGroup (u := 1) (by simp) hcs'
  have h := mul_mem (mul_mem h1 h2) h3
  rw [mul_assoc, smul_one_mul] at h
  exact h

theorem continuous_hFam (k : ℤ) : Continuous (Function.uncurry (hFam k)) := by
  have h1 : Continuous fun p : ℝ × ℝ => Complex.exp (((k : ℝ) * Real.pi * p.2 : ℝ) * I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)
  have h2 : Continuous fun p : ℝ × ℝ => gam (Complex.exp ((2 * Real.pi * p.2 : ℝ) * I))
      (Real.cos (p.1 * Real.pi / 2)) (Real.sin (p.1 * Real.pi / 2)) :=
    continuous_gam (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const))
      (by fun_prop) (by fun_prop)
  have h3 : Continuous fun p : ℝ × ℝ => gam 1 (Real.cos (p.1 * Real.pi / 2))
      (-Real.sin (p.1 * Real.pi / 2)) :=
    continuous_gam continuous_const (by fun_prop) (by fun_prop)
  exact continuous_realForm.comp (h1.smul (h2.matrix_mul h3))

theorem hFam_zero (k : ℤ) (s : ℝ) : hFam k s 0 = 1 := by
  have hcs : Real.cos (s * Real.pi / 2) ^ 2 + Real.sin (s * Real.pi / 2) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  have h1 : gam (Complex.exp ((2 * Real.pi * 0 : ℝ) * I)) (Real.cos (s * Real.pi / 2))
      (Real.sin (s * Real.pi / 2)) = gam 1 (Real.cos (s * Real.pi / 2))
      (Real.sin (s * Real.pi / 2)) := by
    simp
  rw [hFam, uFam, h1, gam_one_mul_gam_one_neg hcs]
  simp [realForm_one]

theorem hFam_one {k : ℤ} (hk : Odd k) (s : ℝ) : hFam k s 1 = -1 := by
  have hcs : Real.cos (s * Real.pi / 2) ^ 2 + Real.sin (s * Real.pi / 2) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  have h1 : gam (Complex.exp ((2 * Real.pi * 1 : ℝ) * I)) (Real.cos (s * Real.pi / 2))
      (Real.sin (s * Real.pi / 2)) = gam 1 (Real.cos (s * Real.pi / 2))
      (Real.sin (s * Real.pi / 2)) := by
    rw [mul_one, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.exp_two_pi_mul_I]
  have h2 : Complex.exp (((k : ℝ) * Real.pi * 1 : ℝ) * I) = -1 := by
    rw [← exp_odd_mul_pi_mul_I hk]; congr 1; push_cast; ring
  rw [hFam, uFam, h1, h2, gam_one_mul_gam_one_neg hcs, neg_one_smul, realForm_neg, realForm_one]

theorem isAdmissiblePath_hFam {k : ℤ} (hk : Odd k) (s : ℝ) : IsAdmissiblePath (hFam k s) where
  continuous := Continuous.uncurry_left s (continuous_hFam k)
  mem t := realForm_mem_symplecticGroup (uFam_mem_unitaryGroup k s t)
  start := hFam_zero k s
  endpoint := by rw [hFam_one hk]; exact neg_one_mem_symplecticStar

theorem blockSumC_fin_one (a b : ℂ) :
    blockSumC (a • (1 : Matrix (Fin 1) (Fin 1) ℂ)) (b • (1 : Matrix (Fin 1) (Fin 1) ℂ))
      = !![a, 0; 0, b] := by
  have e0 : (finSumFinEquiv (Sum.inl (0 : Fin 1)) : Fin (1 + 1)) = 0 := rfl
  have e1 : (finSumFinEquiv (Sum.inr (0 : Fin 1)) : Fin (1 + 1)) = 1 := rfl
  ext k k'
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective k
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective k'
  rw [blockSumC, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> rw [Fin.eq_zero i, Fin.eq_zero j] <;>
    simp [e0, e1]

/-- At `s = 0` the family is the loop `diag(e^{i(ℓ+2)πt}, e^{i(ℓ−2)πt})`. -/
theorem uFam_s_zero (k : ℤ) (t : ℝ) :
    uFam k 0 t = blockSumC
      (Complex.exp ((t * (((k + 2 : ℤ) : ℝ) * Real.pi) : ℝ) * I) • (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (Complex.exp ((t * (((k - 2 : ℤ) : ℝ) * Real.pi) : ℝ) * I) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  have hconj : (starRingEnd ℂ) (Complex.exp ((2 * Real.pi * t : ℝ) * I))
      = Complex.exp (-((2 * Real.pi * t : ℝ) * I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have h1 : Complex.exp (((k : ℝ) * Real.pi * t : ℝ) * I) * Complex.exp ((2 * Real.pi * t : ℝ) * I)
      = Complex.exp ((t * (((k + 2 : ℤ) : ℝ) * Real.pi) : ℝ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : Complex.exp (((k : ℝ) * Real.pi * t : ℝ) * I) *
      (starRingEnd ℂ) (Complex.exp ((2 * Real.pi * t : ℝ) * I))
      = Complex.exp ((t * (((k - 2 : ℤ) : ℝ) * Real.pi) : ℝ) * I) := by
    rw [hconj, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [blockSumC_fin_one, uFam, zero_mul, zero_div, Real.cos_zero, Real.sin_zero, neg_zero,
    gam_one_zero_mul, smul_fin_two, mul_zero, h1, h2]

/-- At `s = 1` the family is the path `e^{iℓπt} · Id`. -/
theorem uFam_s_one (k : ℤ) (t : ℝ) :
    uFam k 1 t = blockSumC
      (Complex.exp ((t * ((k : ℝ) * Real.pi) : ℝ) * I) • (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (Complex.exp ((t * ((k : ℝ) * Real.pi) : ℝ) * I) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  rw [blockSumC_smul_one, uFam, one_mul, Real.cos_pi_div_two, Real.sin_pi_div_two,
    gam_zero_one_mul]
  congr 2
  push_cast; ring

/-- **The homotopy behind Lemma 7.2.4.**  For odd `ℓ`, the paths
`exp(t(ℓ+2)πJ) ⊕ exp(t(ℓ−2)πJ)` and `exp(tℓπJ) ⊕ exp(tℓπJ)` are homotopic in
`S`: the first is the second times the loop `diag(e^{2πit}, e^{−2πit})` of
`SU(2)`, which is contractible. -/
theorem homotopicInS_rot {k : ℤ} (hk : Odd k) :
    HomotopicInS
      (fun t => blockSum (expPath ((((k + 2 : ℤ) : ℝ) * Real.pi) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) t)
        (expPath ((((k - 2 : ℤ) : ℝ) * Real.pi) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) t))
      (fun t => blockSum (expPath (((k : ℝ) * Real.pi) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) t)
        (expPath (((k : ℝ) * Real.pi) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) t)) := by
  refine ⟨hFam k, continuous_hFam k, isAdmissiblePath_hFam hk, ?_, ?_⟩
  · funext t
    simp only [expPath_smul_one]
    rw [blockSum_realForm, hFam, uFam_s_zero]
  · funext t
    simp only [expPath_smul_one]
    rw [blockSum_realForm, hFam, uFam_s_one]

end Homotopy

end Chapter7
end MorseFloer
