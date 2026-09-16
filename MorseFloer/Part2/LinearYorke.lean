import MorseFloer.Part2.Wirtinger
import Mathlib

/-!
# Remark 7.1.2, second half: `exp(JS)` has no eigenvalue `1` when `‖S‖ < 2π`

This file proves the linear-algebraic input of Remark 7.1.2 of the book in the
form Chapter 7 needs: for a real square matrix `A` which is invertible and whose
Euclidean operator norm is `< 2π`, the matrix `exp A − Id` is invertible
(`LinearYorke.det_exp_sub_one_ne_zero`), together with the bound
`‖S‖ ≤ max |λ_i|` for a symmetric `S` (`LinearYorke.exists_norm_toEuclideanCLM_apply_le`)
and the isometry of an orthogonal matrix (`norm_toEuclideanCLM_apply_of_transpose_mul`).

## The route: Yorke's theorem for a linear field

The book argues with the spectrum: `exp A` has the eigenvalue `1` only if `A`
has an eigenvalue `2πik`, which `‖A‖ < 2π` forbids unless `k = 0`.  Rather than
the spectral mapping theorem for `exp`, which Mathlib lacks, the proof here uses
Yorke's theorem (`Wirtinger.yorke`, proved for Proposition 6.1.5): a vector `v`
with `exp A · v = v` gives a `1`-periodic orbit `t ↦ exp(tA) v` of the linear
field `x ↦ Ax`, which is `‖A‖`-Lipschitz with `‖A‖ < 2π`; so the orbit is
constant, `Av = 0`, and `v = 0` because `A` is invertible.

The symmetric bound comes from Mathlib's spectral theorem for Hermitian
matrices (`Matrix.IsHermitian.eigenvectorBasis`): expanding along the orthonormal
eigenbasis, `‖Sw‖² = ∑ λ_i² ⟪e_i, w⟫² ≤ (max |λ_i|)² ‖w‖²`.

The exponential and its derivative live in the normed algebra of matrices, for
which Mathlib has only scoped instances (`Matrix.Norms.Operator`); the statements
use the product topology, which agrees with the scoped one, and
`backward.isDefEq.respectTransparency false` lets Lean see it, as in Mathlib's
`Matrix.exp_add_of_commute`.
-/

open Matrix
open scoped RealInnerProductSpace NNReal

namespace MorseFloer
namespace LinearYorke

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An orthogonal matrix acts isometrically on Euclidean space. -/
theorem norm_toEuclideanCLM_apply_of_transpose_mul {Q : Matrix n n ℝ} (hQ : Qᵀ * Q = 1)
    (w : EuclideanSpace ℝ n) : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Q w‖ = ‖w‖ := by
  have hstar : star (Matrix.toEuclideanCLM (𝕜 := ℝ) Q) * Matrix.toEuclideanCLM (𝕜 := ℝ) Q
      = 1 := by
    rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, hQ, map_one]
  have h : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Q w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← mul_apply_eq_comp, hstar, one_apply_eq_self]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- For a real symmetric matrix `S` all of whose eigenvalues satisfy `|λ| < r`, the
Euclidean operator norm of `S` is bounded by some `M < r`: expanding along an
orthonormal eigenbasis, `‖Sw‖² = ∑ λ_i² ⟪e_i, w⟫² ≤ (max |λ_i|)² ‖w‖²`. -/
theorem exists_norm_toEuclideanCLM_apply_le {S : Matrix n n ℝ} (hS : Sᵀ = S) {r : ℝ}
    (hr0 : 0 < r) (hr : ∀ c : ℝ, (S - c • 1).det = 0 → |c| < r) :
    ∃ M : ℝ≥0, (M : ℝ) < r ∧ ∀ w : EuclideanSpace ℝ n,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S w‖ ≤ M * ‖w‖ := by
  have hH : S.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hS
  set b := hH.eigenvectorBasis with hb
  set lam := hH.eigenvalues with hlam
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) S with hT
  have hroot : ∀ i, (S - lam i • 1).det = 0 := by
    intro i
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨⇑(b i), ?_, ?_⟩
    · intro h0
      have h1 := b.orthonormal.1 i
      have h2 : b i = 0 := by rw [← WithLp.toLp_ofLp 2 (b i), h0]; rfl
      rw [h2] at h1
      simp at h1
    · rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        hH.mulVec_eigenvectorBasis, sub_self]
  set M : ℝ≥0 := Finset.univ.sup fun i => ‖lam i‖₊ with hM
  refine ⟨M, ?_, ?_⟩
  · have hlt : ∀ i, ‖lam i‖₊ < r.toNNReal := by
      intro i
      rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hr0.le]
      exact hr _ (hroot i)
    have hbot : (⊥ : ℝ≥0) < r.toNNReal := by
      rw [NNReal.bot_eq_zero]; exact Real.toNNReal_pos.mpr hr0
    have hMlt : M < r.toNNReal := (Finset.sup_lt_iff hbot).mpr fun i _ => hlt i
    have := NNReal.coe_lt_coe.mpr hMlt
    rwa [Real.coe_toNNReal _ hr0.le] at this
  · intro w
    have hstarT : star T = T := by
      rw [hT, ← map_star, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, hS]
    have hTb : ∀ i, T (b i) = lam i • b i := by
      intro i
      rw [← WithLp.toLp_ofLp 2 (T (b i)), hT, Matrix.ofLp_toEuclideanCLM,
        hH.mulVec_eigenvectorBasis, ← WithLp.ofLp_smul, WithLp.toLp_ofLp]
    have hcoef : ∀ i, ⟪b i, T w⟫ = lam i * ⟪b i, w⟫ := by
      intro i
      rw [← hstarT, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
        hTb, real_inner_smul_left]
    have hMi : ∀ i, |lam i| ≤ (M : ℝ) := fun i => by
      have := Finset.le_sup (f := fun i => ‖lam i‖₊) (Finset.mem_univ i)
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs] at this
      exact this
    have hsq : ‖T w‖ ^ 2 ≤ ((M : ℝ) * ‖w‖) ^ 2 := by
      rw [mul_pow, ← b.sum_sq_norm_inner_right (T w), ← b.sum_sq_norm_inner_right w,
        Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hcoef, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_pow]
      have := hMi i
      gcongr
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

set_option backward.isDefEq.respectTransparency false in
/-- The orbit `t ↦ exp(tA) w` of the linear field `x ↦ Ax` solves `x' = A x`. -/
theorem hasDerivAt_exp_smul_apply (A : Matrix n n ℝ) (w : EuclideanSpace ℝ n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Matrix.toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp (s • A)) w)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp (t • A)) w)) t := by
  open scoped Matrix.Norms.Operator in
  have hexp := hasDerivAt_exp_smul_const' A t
  let L : Matrix n n ℝ →ₗ[ℝ] EuclideanSpace ℝ n :=
    { toFun := fun M => Matrix.toEuclideanCLM (𝕜 := ℝ) M w
      map_add' := fun M N => by simp
      map_smul' := fun c M => by simp }
  have hL : HasFDerivAt L (LinearMap.toContinuousLinearMap L) (NormedSpace.exp (t • A)) :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt
  have h := hL.comp_hasDerivAt t hexp
  simpa [L, Function.comp_def] using h

/-- **Remark 7.1.2, second half, in operator form.**  If `A` is an invertible real
matrix whose Euclidean operator norm is `< 2π`, then `exp A` does not have the
eigenvalue `1`.

Proof by Yorke's theorem: a fixed vector `v ≠ 0` of `exp A` gives the
`1`-periodic orbit `t ↦ exp(tA) v` of the `‖A‖`-Lipschitz field `x ↦ Ax`, which
must be constant, so `Av = 0` and `v = 0`. -/
theorem det_exp_sub_one_ne_zero {A : Matrix n n ℝ} (hA : A.det ≠ 0)
    (hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ < 2 * Real.pi) :
    (NormedSpace.exp A - 1).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hfix : NormedSpace.exp A *ᵥ v = v := by
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) A with hT
  set w : EuclideanSpace ℝ n := WithLp.toLp 2 v with hw
  set x : ℝ → EuclideanSpace ℝ n :=
    fun s => Matrix.toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp (s • A)) w with hx
  have hxd : ∀ s, HasDerivAt x (T (x s)) s := fun s => hasDerivAt_exp_smul_apply A w s
  have hper : Function.Periodic x 1 := by
    intro s
    show Matrix.toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp ((s + 1) • A)) w
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp (s • A)) w
    rw [add_smul, one_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left s),
      map_mul, mul_apply_eq_comp]
    congr 1
    rw [← WithLp.toLp_ofLp 2 (Matrix.toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp A) w),
      Matrix.ofLp_toEuclideanCLM]
    show WithLp.toLp 2 (NormedSpace.exp A *ᵥ v) = WithLp.toLp 2 v
    rw [hfix]
  have hK : (‖T‖₊ : ℝ) < 2 * Real.pi := by rwa [coe_nnnorm]
  have hconst : ∀ s, x s = x 0 := fun s => Wirtinger.yorke T.lipschitz hK hxd hper s
  have hx0 : x 0 = w := by
    show Matrix.toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp ((0 : ℝ) • A)) w = w
    rw [zero_smul, NormedSpace.exp_zero, map_one, one_apply_eq_self]
  have hxfun : x = fun _ => w := funext fun s => (hconst s).trans hx0
  have hTw : T w = 0 := by
    have h := hxd 0
    rw [hxfun] at h
    exact h.unique (hasDerivAt_const 0 w)
  have hAv : A *ᵥ v = 0 := by
    have h := congrArg WithLp.ofLp hTw
    rwa [hT, Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] at h
  exact hv0 (Matrix.eq_zero_of_mulVec_eq_zero hA hAv)

end LinearYorke
end MorseFloer
