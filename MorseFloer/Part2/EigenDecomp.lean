import MorseFloer.Part2.SpectralProjector
import MorseFloer.Part2.SymplecticEigen

/-!
# The kernel of a factor of the characteristic polynomial is a sum of generalised eigenspaces

The fourth brick for the map `ρ : Sp(2n) → S¹` of Chapter 7.  For a complex matrix `M` and a
predicate `Pred` on `ℂ`, let `f_Pred` be the product of `X - μ` over the eigenvalues `μ`
satisfying `Pred`, with multiplicity (`fS`; the disc factors `fPoly`, `gPoly` of
`Part2/SpectralProjector.lean` are the cases `dist z c < r` and its negation).  Then

`ker f_Pred(M) = ⨆_{Pred μ} E_μ`,

the sum of the generalised eigenspaces for the eigenvalues satisfying `Pred`
(`kerAeval_fS_eq_iSup`).  This identifies the range of the spectral projector of the previous
brick with the object the book works with.

Both inclusions rest on one trick, and neither needs the dimension of a generalised
eigenspace.  Writing the characteristic polynomial as `(X - μ)^c · r` with `r(μ) ≠ 0`, a vector
`X` killed by some power of `M - μ` has `Y = (M - μ)^c X` killed both by a power of `M - μ`
and, by Cayley–Hamilton, by `r(M)`; these two polynomials are coprime, so `Y = 0`
(`eq_zero_of_aeval_coprime`).  Hence `E_μ ⊆ ker (M - μ)^c`, which is the inclusion `⊇`; the
inclusion `⊆` is the splitting of the kernel of a product of pairwise coprime polynomials.

For a symplectic matrix and a predicate stable under `μ ↦ 1/μ̄` on the eigenvalues, the two
kernels `ker f_Pred(M)` and `ker f_{¬Pred}(M)` are `H`-orthogonal (Lemma 7.3.3 spread over the
sums), and `H` is nondegenerate on `ker f_Pred(M)` (`eq_zero_of_mem_kerAeval_fS_of_forall`).
That is the form in which the signature of `Q` on the sum of the generalised eigenspaces in a
small disc is defined.
-/

open Polynomial Matrix Module

namespace MorseFloer
namespace EigenDecomp

section General

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The factor of the characteristic polynomial carrying the eigenvalues satisfying `Pred`. -/
noncomputable def fS (Pred : ℂ → Prop) [DecidablePred Pred] (M : Matrix m m ℂ) : ℂ[X] :=
  ((M.charpoly.roots.filter Pred).map fun z => X - C z).prod

theorem fPoly_eq_fS (c : ℂ) (r : ℝ) (M : Matrix m m ℂ) :
    SpectralProjector.fPoly c r M = fS (fun z => dist z c < r) M := rfl

theorem gPoly_eq_fS (c : ℂ) (r : ℝ) (M : Matrix m m ℂ) :
    SpectralProjector.gPoly c r M = fS (fun z => ¬dist z c < r) M := rfl

variable (Pred : ℂ → Prop) [DecidablePred Pred]

theorem fS_mul_fS_not (M : Matrix m m ℂ) : fS Pred M * fS (fun z => ¬Pred z) M = M.charpoly := by
  rw [fS, fS, ← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not]
  exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic M)
    IsAlgClosed.card_roots_eq_natDegree

theorem isCoprime_fS_fS_not (M : Matrix m m ℂ) : IsCoprime (fS Pred M) (fS (fun z => ¬Pred z) M) := by
  classical
  rw [fS, fS, Finset.prod_multiset_map_count, Finset.prod_multiset_map_count]
  refine IsCoprime.prod_left fun z hz => IsCoprime.prod_right fun w hw => IsCoprime.pow ?_
  refine isCoprime_X_sub_C_of_isUnit_sub ?_
  rw [isUnit_iff_ne_zero, sub_ne_zero]
  intro hzw
  rw [Multiset.mem_toFinset, Multiset.mem_filter] at hz hw
  exact hw.2 (hzw ▸ hz.2)

/-! ### Transport to the endomorphism `toLin' M` -/

theorem aeval_toLin' (M : Matrix m m ℂ) (p : ℂ[X]) :
    aeval (Matrix.toLin' M) p = Matrix.toLin' (aeval M p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, map_smul,
      Matrix.toLin'_pow]

theorem aeval_toLin'_charpoly (M : Matrix m m ℂ) : aeval (Matrix.toLin' M) M.charpoly = 0 := by
  rw [aeval_toLin', aeval_self_charpoly, map_zero]

/-- The generalised eigenspace of `M` for `μ`. -/
noncomputable abbrev E (M : Matrix m m ℂ) (μ : ℂ) : Submodule ℂ (m → ℂ) :=
  Module.End.maxGenEigenspace (Matrix.toLin' M) μ

/-- The kernel of `p(M)`. -/
noncomputable abbrev kerAeval (M : Matrix m m ℂ) (p : ℂ[X]) : Submodule ℂ (m → ℂ) :=
  LinearMap.ker (aeval (Matrix.toLin' M) p)

theorem mem_kerAeval {M : Matrix m m ℂ} {p : ℂ[X]} {v : m → ℂ} :
    v ∈ kerAeval M p ↔ aeval M p *ᵥ v = 0 := by
  rw [LinearMap.mem_ker, aeval_toLin', Matrix.toLin'_apply]

theorem aeval_X_sub_C (M : Matrix m m ℂ) (μ : ℂ) :
    aeval (Matrix.toLin' M) (X - C μ) = Matrix.toLin' M - μ • 1 := by
  rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

/-! ### The coprime trick -/

/-- A vector killed by `r(M)` and by a power of `M - μ`, with `r` coprime to that power,
vanishes. -/
theorem eq_zero_of_aeval_coprime {M : Matrix m m ℂ} {r : ℂ[X]} {μ : ℂ} {k : ℕ}
    (hcop : IsCoprime r ((X - C μ) ^ k)) {w : m → ℂ} (hr : aeval (Matrix.toLin' M) r w = 0)
    (hk : aeval (Matrix.toLin' M) ((X - C μ) ^ k) w = 0) : w = 0 := by
  obtain ⟨a, b, hab⟩ := hcop
  have h := congrArg (fun p => aeval (Matrix.toLin' M) p w) hab
  simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, map_one,
    Module.End.one_apply, hr, hk, map_zero, add_zero] at h
  exact h.symm

/-- `∏ (X - z)` over a multiset, with the power of `X - μ` split off. -/
theorem prod_X_sub_C_eq_pow_mul (s : Multiset ℂ) (μ : ℂ) :
    (s.map fun z => X - C z).prod
      = (X - C μ) ^ s.count μ * ((s.filter fun z => ¬z = μ).map fun z => X - C z).prod := by
  conv_lhs => rw [← Multiset.filter_add_not (fun z => z = μ) s]
  rw [Multiset.map_add, Multiset.prod_add, Multiset.filter_eq', Multiset.map_replicate,
    Multiset.prod_replicate]

theorem isCoprime_prod_X_sub_C_filter_ne (s : Multiset ℂ) (μ : ℂ) (k : ℕ) :
    IsCoprime (((s.filter fun z => ¬z = μ).map fun z => X - C z).prod) ((X - C μ) ^ k) := by
  classical
  rw [Finset.prod_multiset_map_count]
  refine IsCoprime.pow_right (IsCoprime.prod_left fun z hz => IsCoprime.pow_left ?_)
  refine isCoprime_X_sub_C_of_isUnit_sub ?_
  rw [isUnit_iff_ne_zero, sub_ne_zero]
  intro h
  rw [Multiset.mem_toFinset, Multiset.mem_filter] at hz
  exact hz.2 h

/-- **A generalised eigenvector is killed by `(M - μ)^c`, `c` the multiplicity of `μ`.**  In
particular `E_μ = 0` when `μ` is not an eigenvalue. -/
theorem pow_count_mulVec_eq_zero {M : Matrix m m ℂ} {μ : ℂ} {v : m → ℂ} (hv : v ∈ E M μ) :
    aeval (Matrix.toLin' M) ((X - C μ) ^ M.charpoly.roots.count μ) v = 0 := by
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  set c := M.charpoly.roots.count μ with hc
  set r := ((M.charpoly.roots.filter fun z => ¬z = μ).map fun z => X - C z).prod with hr
  have hcp : M.charpoly = (X - C μ) ^ c * r := by
    rw [hr, hc, ← prod_X_sub_C_eq_pow_mul]
    exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic M)
      IsAlgClosed.card_roots_eq_natDegree).symm
  have hcop : IsCoprime r ((X - C μ) ^ k) := isCoprime_prod_X_sub_C_filter_ne _ μ k
  -- `Y = D^c X` is killed by `r(M)` and by `D^k`
  have hY1 : aeval (Matrix.toLin' M) r (aeval (Matrix.toLin' M) ((X - C μ) ^ c) v) = 0 := by
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, ← hcp, aeval_toLin'_charpoly,
      LinearMap.zero_apply]
  have hY2 : aeval (Matrix.toLin' M) ((X - C μ) ^ k)
      (aeval (Matrix.toLin' M) ((X - C μ) ^ c) v) = 0 := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_add, add_comm, pow_add, map_mul,
      Module.End.mul_apply]
    have hk' : aeval (Matrix.toLin' M) ((X - C μ) ^ k) v = 0 := by
      rw [map_pow, aeval_X_sub_C]
      exact hk
    rw [hk', map_zero]
  exact eq_zero_of_aeval_coprime hcop hY1 hY2

theorem E_le_kerAeval_fS {M : Matrix m m ℂ} {μ : ℂ} (hμ : Pred μ) :
    E M μ ≤ kerAeval M (fS Pred M) := by
  intro v hv
  have h := pow_count_mulVec_eq_zero hv
  have hcount : (M.charpoly.roots.filter Pred).count μ = M.charpoly.roots.count μ :=
    Multiset.count_filter_of_pos hμ
  rw [LinearMap.mem_ker, fS, prod_X_sub_C_eq_pow_mul _ μ, hcount, mul_comm, map_mul,
    Module.End.mul_apply, h, map_zero]

theorem E_eq_bot_of_not_mem_roots {M : Matrix m m ℂ} {μ : ℂ} (hμ : μ ∉ M.charpoly.roots) :
    E M μ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have h := pow_count_mulVec_eq_zero hv
  rw [Multiset.count_eq_zero.2 hμ, pow_zero, map_one, Module.End.one_apply] at h
  exact h

/-! ### The kernel of a product of coprime factors -/

theorem kerAeval_prod_le_iSup (M : Matrix m m ℂ) (t : Finset ℂ) (n : ℂ → ℕ) :
    kerAeval M (∏ z ∈ t, (X - C z) ^ n z) ≤ ⨆ z ∈ t, E M z := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    intro v hv
    rw [LinearMap.mem_ker, map_one, Module.End.one_apply] at hv
    rw [hv]
    exact Submodule.zero_mem _
  | insert z t hz ih =>
    rw [Finset.prod_insert hz]
    have hcop : IsCoprime ((X - C z) ^ n z) (∏ w ∈ t, (X - C w) ^ n w) := by
      refine IsCoprime.pow_left (IsCoprime.prod_right fun w hw => IsCoprime.pow_right ?_)
      refine isCoprime_X_sub_C_of_isUnit_sub ?_
      rw [isUnit_iff_ne_zero, sub_ne_zero]
      rintro rfl
      exact hz hw
    rw [kerAeval, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime _ hcop]
    refine sup_le ?_ ?_
    · intro v hv
      have hv' : v ∈ E M z := by
        rw [LinearMap.mem_ker, map_pow, aeval_X_sub_C] at hv
        exact (Module.End.genEigenspace (Matrix.toLin' M) z).monotone le_top
          (Module.End.mem_genEigenspace_nat.2 hv)
      exact Submodule.mem_iSup_of_mem z (Submodule.mem_iSup_of_mem (Finset.mem_insert_self z t) hv')
    · refine ih.trans (iSup₂_mono' fun w hw => ⟨w, Finset.mem_insert_of_mem hw, le_rfl⟩)

/-- **The kernel of `f_Pred(M)` is the sum of the generalised eigenspaces for the eigenvalues
satisfying `Pred`.** -/
theorem kerAeval_fS_eq_iSup (M : Matrix m m ℂ) :
    kerAeval M (fS Pred M) = ⨆ (μ : ℂ) (_ : Pred μ), E M μ := by
  classical
  refine le_antisymm ?_ (iSup₂_le fun μ hμ => E_le_kerAeval_fS Pred hμ)
  have e : fS Pred M = ∏ z ∈ (M.charpoly.roots.filter Pred).toFinset,
      (X - C z) ^ (M.charpoly.roots.filter Pred).count z := by
    rw [fS, Finset.prod_multiset_map_count]
  rw [e]
  refine (kerAeval_prod_le_iSup M _ _).trans (iSup₂_mono' fun z hz => ⟨z, ?_, le_rfl⟩)
  rw [Multiset.mem_toFinset, Multiset.mem_filter] at hz
  exact hz.2

/-- The two complementary kernels span everything. -/
theorem kerAeval_fS_sup_not (M : Matrix m m ℂ) :
    kerAeval M (fS Pred M) ⊔ kerAeval M (fS (fun z => ¬Pred z) M) = ⊤ := by
  rw [kerAeval, kerAeval, sup_ker_aeval_eq_ker_aeval_mul_of_coprime _ (isCoprime_fS_fS_not Pred M),
    fS_mul_fS_not, aeval_toLin'_charpoly, LinearMap.ker_zero]

end General

/-! ### The symplectic case: orthogonality and nondegeneracy of `H` -/

section Symplectic

variable {l : Type*} [DecidableEq l] [Fintype l]
open SymplecticEigen Chapter7

/-- Membership in `E_μ` in the elementary terms of `Part2/SymplecticEigen.lean`. -/
theorem mem_E_iff (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) (v : (l ⊕ l) → ℂ) :
    v ∈ E M μ ↔ ∃ k, InGen M μ k v :=
  mem_maxGenEigenspace_iff M μ v

variable (Pred : ℂ → Prop) [DecidablePred Pred]

/-- **The two kernels are `H`-orthogonal** when `Pred` is stable under `μ ↦ 1/μ̄` on the
eigenvalues: Lemma 7.3.3 spread over the two sums. -/
theorem HForm_eq_zero_of_mem_kerAeval {M : Matrix (l ⊕ l) (l ⊕ l) ℂ}
    (hM : ∀ X Y, HForm (M *ᵥ X) (M *ᵥ Y) = HForm X Y)
    (hclosed : ∀ μ ∈ M.charpoly.roots, Pred μ → Pred (starRingEnd ℂ μ)⁻¹)
    {v w : (l ⊕ l) → ℂ} (hv : v ∈ kerAeval M (fS Pred M))
    (hw : w ∈ kerAeval M (fS (fun z => ¬Pred z) M)) : HForm v w = 0 := by
  rw [kerAeval_fS_eq_iSup] at hv hw
  refine Submodule.iSup_induction (motive := fun v => HForm v w = 0) _ hv ?_
    (HForm_zero_left w) fun a b ha hb => by rw [HForm_add_left, ha, hb, add_zero]
  intro μ v' hv'
  refine Submodule.iSup_induction (motive := fun v' => HForm v' w = 0) _ hv' ?_
    (HForm_zero_left w) fun a b ha hb => by rw [HForm_add_left, ha, hb, add_zero]
  intro hμ x hx
  refine Submodule.iSup_induction (motive := fun w => HForm x w = 0) _ hw ?_
    (HForm_zero_right x) fun a b ha hb => by rw [HForm_add_right, ha, hb, add_zero]
  intro ν w' hw'
  refine Submodule.iSup_induction (motive := fun w' => HForm x w' = 0) _ hw' ?_
    (HForm_zero_right x) fun a b ha hb => by rw [HForm_add_right, ha, hb, add_zero]
  intro hν y hy
  -- `x ∈ E_μ`, `y ∈ E_ν`, `Pred μ`, `¬ Pred ν`
  by_cases hμroot : μ ∈ M.charpoly.roots
  · obtain ⟨k, hk⟩ := (mem_E_iff M μ x).1 hx
    obtain ⟨n, hn⟩ := (mem_E_iff M ν y).1 hy
    refine HForm_eq_zero_of_inGen hM ?_ k n x y hk hn
    intro hcon
    apply hν
    -- `μ ν̄ = 1` gives `ν = 1/μ̄`
    have h1 : starRingEnd ℂ ν = μ⁻¹ := eq_inv_of_mul_eq_one_right hcon
    have h2 : ν = starRingEnd ℂ (μ⁻¹) := by
      rw [← h1, Complex.conj_conj]
    rw [h2, map_inv₀]
    exact hclosed μ hμroot hμ
  · rw [E_eq_bot_of_not_mem_roots hμroot, Submodule.mem_bot] at hx
    rw [hx, HForm_zero_left]

/-- **`H` is nondegenerate on `ker f_Pred(M)`** when `Pred` is stable under `μ ↦ 1/μ̄` on the
eigenvalues.  A vector of the kernel orthogonal to the kernel is orthogonal to the
complementary kernel as well, hence to everything. -/
theorem eq_zero_of_mem_kerAeval_fS_of_forall {M : Matrix (l ⊕ l) (l ⊕ l) ℂ}
    (hM : ∀ X Y, HForm (M *ᵥ X) (M *ᵥ Y) = HForm X Y)
    (hclosed : ∀ μ ∈ M.charpoly.roots, Pred μ → Pred (starRingEnd ℂ μ)⁻¹)
    {v : (l ⊕ l) → ℂ} (hv : v ∈ kerAeval M (fS Pred M))
    (h : ∀ w ∈ kerAeval M (fS Pred M), HForm v w = 0) : v = 0 := by
  refine eq_zero_of_forall_HForm_eq_zero fun Z => ?_
  have hZ : Z ∈ kerAeval M (fS Pred M) ⊔ kerAeval M (fS (fun z => ¬Pred z) M) := by
    rw [kerAeval_fS_sup_not]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hZ
  rw [HForm_add_right, h y hy, HForm_eq_zero_of_mem_kerAeval Pred hM hclosed hv hz, add_zero]

/-- The same for the real form `B`. -/
theorem eq_zero_of_mem_kerAeval_fS_of_forall_BForm {M : Matrix (l ⊕ l) (l ⊕ l) ℂ}
    (hM : ∀ X Y, HForm (M *ᵥ X) (M *ᵥ Y) = HForm X Y)
    (hclosed : ∀ μ ∈ M.charpoly.roots, Pred μ → Pred (starRingEnd ℂ μ)⁻¹)
    {v : (l ⊕ l) → ℂ} (hv : v ∈ kerAeval M (fS Pred M))
    (h : ∀ w ∈ kerAeval M (fS Pred M), BForm v w = 0) : v = 0 := by
  refine eq_zero_of_mem_kerAeval_fS_of_forall Pred hM hclosed hv fun w hw => ?_
  have hI : Complex.I • w ∈ kerAeval M (fS Pred M) := Submodule.smul_mem _ _ hw
  have h1 := h w hw
  have h2 := h (Complex.I • w) hI
  rw [BForm_eq_im] at h1 h2
  rw [HForm_smul_right, Complex.conj_I, neg_mul, Complex.neg_im, neg_eq_zero,
    Complex.I_mul_im] at h2
  exact Complex.ext h2 h1

end Symplectic

end EigenDecomp
end MorseFloer
