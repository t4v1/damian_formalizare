import MorseFloer.Part2.EigenDecomp
import MorseFloer.Part2.SymplecticSpectrum

/-!
# Multiplicities, kernels of factors, and pairings of eigenvalues

Bookkeeping for the map `ρ` of Chapter 7.  The dimension of a generalised eigenspace is the
algebraic multiplicity (`finrank_E`, Mathlib's `finrank_maxGenEigenspace_eq` read on a matrix),
so the kernel of the factor `f_Pred(M)` of the characteristic polynomial has dimension the
number of eigenvalues satisfying `Pred`, with multiplicity (`finrank_kerAeval_fS`); the kernels
of two factors with disjoint sets of eigenvalues form a direct sum (`kerAeval_fS_or`,
`kerAeval_fS_inf`), and are `H`-orthogonal as soon as no eigenvalue of the one and no eigenvalue
of the other have `μ ν̄ = 1` (`HForm_eq_zero_of_mem_kerAeval_of_ne`, Lemma 7.3.3 spread over
the sums).

For a real symplectic matrix, the spectrum is stable under `μ ↦ μ̄` and `μ ↦ 1/μ̄` with
multiplicities (`count_conj`, `count_inv`), which pairs off the eigenvalues in a stable region:
the non-real ones by conjugation (`card_filter_im_ne_zero`), those off the unit circle by
`μ ↦ 1/μ̄` (`card_filter_norm_ne_one`), and the negative real ones other than `-1` by inversion
(`card_filter_neg_real`).  Finally the multiplicity of `-1` is even (`even_count_neg_one`):
the characteristic polynomial is self-reciprocal, so is its quotient `q` by `(X + 1)^m`, and a
self-reciprocal polynomial of odd degree vanishes at `-1`.
-/

open Polynomial Matrix Module

namespace MorseFloer
namespace EigenMult

open EigenDecomp

section General

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The dimension of the generalised eigenspace is the algebraic multiplicity. -/
theorem finrank_E (M : Matrix m m ℂ) (μ : ℂ) :
    finrank ℂ (E M μ) = M.charpoly.roots.count μ := by
  rw [E, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin', count_roots]

theorem finrank_kerAeval_mul_of_coprime (M : Matrix m m ℂ) {p q : ℂ[X]} (h : IsCoprime p q) :
    finrank ℂ (kerAeval M (p * q)) = finrank ℂ (kerAeval M p) + finrank ℂ (kerAeval M q) := by
  rw [kerAeval, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime _ h]
  have := Submodule.finrank_sup_add_finrank_inf_eq (kerAeval M p) (kerAeval M q)
  rw [(disjoint_ker_aeval_of_isCoprime _ h).eq_bot, finrank_bot, add_zero] at this
  exact this

theorem fS_eq_pow_count (M : Matrix m m ℂ) (μ : ℂ) :
    fS (· = μ) M = (X - C μ) ^ M.charpoly.roots.count μ := by
  classical
  rw [fS, Multiset.filter_eq', Multiset.map_replicate, Multiset.prod_replicate]

theorem kerAeval_pow_count (M : Matrix m m ℂ) (μ : ℂ) :
    kerAeval M ((X - C μ) ^ M.charpoly.roots.count μ) = E M μ := by
  classical
  rw [← fS_eq_pow_count, kerAeval_fS_eq_iSup]
  exact iSup_iSup_eq_left

theorem finrank_kerAeval_prod (M : Matrix m m ℂ) (t : Finset ℂ) (n : ℂ → ℕ) :
    finrank ℂ (kerAeval M (∏ z ∈ t, (X - C z) ^ n z))
      = ∑ z ∈ t, finrank ℂ (kerAeval M ((X - C z) ^ n z)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, kerAeval, map_one, Module.End.one_eq_id,
      LinearMap.ker_id, finrank_bot]
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, finrank_kerAeval_mul_of_coprime, ih]
    refine IsCoprime.pow_left (IsCoprime.prod_right fun z hz => IsCoprime.pow_right ?_)
    refine isCoprime_X_sub_C_of_isUnit_sub ?_
    rw [isUnit_iff_ne_zero, sub_ne_zero]
    exact fun h => ha (h ▸ hz)

/-- **The dimension of `ker f_Pred(M)`** is the number of eigenvalues satisfying `Pred`, with
multiplicity. -/
theorem finrank_kerAeval_fS (Pred : ℂ → Prop) [DecidablePred Pred] (M : Matrix m m ℂ) :
    finrank ℂ (kerAeval M (fS Pred M)) = M.charpoly.roots.countP Pred := by
  classical
  set s := M.charpoly.roots.filter Pred with hs
  have e : fS Pred M = ∏ z ∈ s.toFinset, (X - C z) ^ s.count z := by
    rw [fS, ← hs, Finset.prod_multiset_map_count]
  rw [e, finrank_kerAeval_prod, Multiset.countP_eq_card_filter, ← hs,
    ← Multiset.toFinset_sum_count_eq]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hPz : Pred z := (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hz)).2
  rw [hs, Multiset.count_filter_of_pos hPz, kerAeval_pow_count, finrank_E]

theorem fS_congr {P Q : ℂ → Prop} [DecidablePred P] [DecidablePred Q] (M : Matrix m m ℂ)
    (h : ∀ z ∈ M.charpoly.roots, P z ↔ Q z) : fS P M = fS Q M := by
  rw [fS, fS, Multiset.filter_congr h]

theorem fS_or {P Q : ℂ → Prop} [DecidablePred P] [DecidablePred Q] (M : Matrix m m ℂ)
    (hdisj : ∀ z ∈ M.charpoly.roots, ¬(P z ∧ Q z)) :
    fS (fun z => P z ∨ Q z) M = fS P M * fS Q M := by
  rw [fS, fS, fS, ← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_filter,
    Multiset.filter_eq_nil.2 hdisj, add_zero]

theorem isCoprime_fS_fS {P Q : ℂ → Prop} [DecidablePred P] [DecidablePred Q]
    (M : Matrix m m ℂ) (hdisj : ∀ z ∈ M.charpoly.roots, ¬(P z ∧ Q z)) :
    IsCoprime (fS P M) (fS Q M) := by
  classical
  rw [fS, fS, Finset.prod_multiset_map_count, Finset.prod_multiset_map_count]
  refine IsCoprime.prod_left fun z hz => IsCoprime.prod_right fun w hw => IsCoprime.pow ?_
  refine isCoprime_X_sub_C_of_isUnit_sub ?_
  rw [isUnit_iff_ne_zero, sub_ne_zero]
  rw [Multiset.mem_toFinset, Multiset.mem_filter] at hz hw
  intro hzw
  exact hdisj z hz.1 ⟨hz.2, hzw ▸ hw.2⟩

theorem kerAeval_fS_or {P Q : ℂ → Prop} [DecidablePred P] [DecidablePred Q]
    (M : Matrix m m ℂ) (hdisj : ∀ z ∈ M.charpoly.roots, ¬(P z ∧ Q z)) :
    kerAeval M (fS (fun z => P z ∨ Q z) M) = kerAeval M (fS P M) ⊔ kerAeval M (fS Q M) := by
  rw [fS_or M hdisj, kerAeval, kerAeval, kerAeval,
    sup_ker_aeval_eq_ker_aeval_mul_of_coprime _ (isCoprime_fS_fS M hdisj)]

theorem kerAeval_fS_inf {P Q : ℂ → Prop} [DecidablePred P] [DecidablePred Q]
    (M : Matrix m m ℂ) (hdisj : ∀ z ∈ M.charpoly.roots, ¬(P z ∧ Q z)) :
    kerAeval M (fS P M) ⊓ kerAeval M (fS Q M) = ⊥ :=
  (disjoint_ker_aeval_of_isCoprime _ (isCoprime_fS_fS M hdisj)).eq_bot

end General

/-! ### Pairings of the eigenvalues of a symplectic matrix -/

section Symplectic

variable {l : Type*} [DecidableEq l] [Fintype l]
open SymplecticEigen SymplecticSpectrum Chapter7

/-- **Lemma 7.3.3 spread over two sums.**  If no eigenvalue satisfying `P` and no eigenvalue
satisfying `Q` have `μ ν̄ = 1`, the kernels `ker f_P(M)` and `ker f_Q(M)` are `H`-orthogonal. -/
theorem HForm_eq_zero_of_mem_kerAeval_of_ne {M : Matrix (l ⊕ l) (l ⊕ l) ℂ}
    (hM : ∀ X Y, HForm (M *ᵥ X) (M *ᵥ Y) = HForm X Y) (P Q : ℂ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ μ ∈ M.charpoly.roots, ∀ ν ∈ M.charpoly.roots, P μ → Q ν →
      μ * starRingEnd ℂ ν ≠ 1)
    {v w : (l ⊕ l) → ℂ} (hv : v ∈ kerAeval M (fS P M)) (hw : w ∈ kerAeval M (fS Q M)) :
    HForm v w = 0 := by
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
  by_cases hμroot : μ ∈ M.charpoly.roots
  · by_cases hνroot : ν ∈ M.charpoly.roots
    · obtain ⟨k, hk⟩ := (mem_E_iff M μ x).1 hx
      obtain ⟨n, hn⟩ := (mem_E_iff M ν y).1 hy
      exact HForm_eq_zero_of_inGen hM (hPQ μ hμroot ν hνroot hμ hν) k n x y hk hn
    · rw [E_eq_bot_of_not_mem_roots hνroot, Submodule.mem_bot] at hy
      rw [hy, HForm_zero_right]
  · rw [E_eq_bot_of_not_mem_roots hμroot, Submodule.mem_bot] at hx
    rw [hx, HForm_zero_left]

theorem count_conj (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) (μ : ℂ) :
    (cpx A).charpoly.roots.count (starRingEnd ℂ μ) = (cpx A).charpoly.roots.count μ := by
  classical
  conv_lhs => rw [← roots_map_conj A]
  exact Multiset.count_map_eq_count' _ _ (RingHom.injective _) μ

theorem count_inv {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    (μ : ℂ) : (cpx A).charpoly.roots.count μ⁻¹ = (cpx A).charpoly.roots.count μ := by
  classical
  conv_lhs => rw [← roots_map_inv hA]
  exact Multiset.count_map_eq_count' _ _ inv_injective μ

theorem roots_map_inv_conj {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    (cpx A).charpoly.roots.map (fun z => (starRingEnd ℂ z)⁻¹) = (cpx A).charpoly.roots := by
  have e : (fun z : ℂ => (starRingEnd ℂ z)⁻¹) = (fun z => z⁻¹) ∘ (starRingEnd ℂ) := rfl
  rw [e, ← Multiset.map_map, roots_map_conj A, roots_map_inv hA]

theorem inv_conj_inv_conj (z : ℂ) : (starRingEnd ℂ (starRingEnd ℂ z)⁻¹)⁻¹ = z := by
  rw [map_inv₀, Complex.conj_conj, inv_inv]

/-- **A fixed-point-free pairing of a multiset has even cardinality**, in the form needed: if
`σ` preserves `s` and exchanges the parts `P` and `Q`, then `#(P ∨ Q) = 2 #P`. -/
theorem card_filter_eq_two_mul {s : Multiset ℂ} {σ : ℂ → ℂ} (hσ : s.map σ = s)
    (P Q : ℂ → Prop) [DecidablePred P] [DecidablePred Q] (hPQ : ∀ z ∈ s, ¬(P z ∧ Q z))
    (hσP : ∀ z ∈ s, Q (σ z) ↔ P z) :
    Multiset.card (s.filter fun z => P z ∨ Q z) = 2 * Multiset.card (s.filter P) := by
  have h1 : s.filter (fun z => P z ∨ Q z) = s.filter P + s.filter Q := by
    rw [Multiset.filter_add_filter, Multiset.filter_eq_nil.2 hPQ, add_zero]
  have h2 : s.filter Q = (s.filter P).map σ := by
    conv_lhs => rw [← hσ]
    rw [Multiset.filter_map]
    congr 1
    exact Multiset.filter_congr fun z hz => hσP z hz
  rw [h1, Multiset.card_add, h2, Multiset.card_map, two_mul]

/-- The non-real eigenvalues in a conjugation-symmetric region come in conjugate pairs. -/
theorem card_filter_im_ne_zero (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) (R : ℂ → Prop) [DecidablePred R]
    (hR : ∀ z, R (starRingEnd ℂ z) ↔ R z) :
    Multiset.card ((cpx A).charpoly.roots.filter fun z => R z ∧ z.im ≠ 0)
      = 2 * Multiset.card ((cpx A).charpoly.roots.filter fun z => R z ∧ 0 < z.im) := by
  have h := card_filter_eq_two_mul (roots_map_conj A) (fun z => R z ∧ 0 < z.im)
    (fun z => R z ∧ z.im < 0) (fun z _ h => by linarith [h.1.2, h.2.2]) (fun z _ => by
      rw [hR, Complex.conj_im]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩)
  rw [← h]
  congr 1
  refine Multiset.filter_congr fun z _ => ?_
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne h2 with h3 | h3
    · exact Or.inr ⟨h1, h3⟩
    · exact Or.inl ⟨h1, h3⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, h2.ne'⟩
    · exact ⟨h1, h2.ne⟩

/-- In a region stable under `μ ↦ 1/μ̄`, the eigenvalues off the unit circle come in pairs
`μ, 1/μ̄`, one inside and one outside. -/
theorem card_filter_norm_ne_one {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) (R : ℂ → Prop) [DecidablePred R]
    (hR : ∀ z ∈ (cpx A).charpoly.roots, R z → R (starRingEnd ℂ z)⁻¹) :
    Multiset.card ((cpx A).charpoly.roots.filter fun z => R z ∧ ‖z‖ ≠ 1)
      = 2 * Multiset.card ((cpx A).charpoly.roots.filter fun z => R z ∧ ‖z‖ < 1) := by
  have hR' : ∀ z ∈ (cpx A).charpoly.roots, R (starRingEnd ℂ z)⁻¹ ↔ R z := fun z hz =>
    ⟨fun h => by
      have := hR _ (inv_conj_mem_roots hA hz) h
      rwa [inv_conj_inv_conj] at this, hR z hz⟩
  have h := card_filter_eq_two_mul (roots_map_inv_conj hA) (fun z => R z ∧ ‖z‖ < 1)
    (fun z => R z ∧ 1 < ‖z‖) (fun z _ h => by linarith [h.1.2, h.2.2]) (fun z hz => by
      have hz0 : z ≠ 0 := fun h0 => zero_notMem_roots hA (h0 ▸ hz)
      rw [hR' z hz, norm_inv, Complex.norm_conj, one_lt_inv₀ (norm_pos_iff.2 hz0)])
  rw [← h]
  congr 1
  refine Multiset.filter_congr fun z _ => ?_
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne h2 with h3 | h3
    · exact Or.inl ⟨h1, h3⟩
    · exact Or.inr ⟨h1, h3⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, h2.ne⟩
    · exact ⟨h1, h2.ne'⟩

/-- A real number, as a complex number, and its image under `μ ↦ 1/μ̄`. -/
theorem inv_conj_of_im_eq_zero {z : ℂ} (hz : z.im = 0) :
    (starRingEnd ℂ z)⁻¹ = ((z.re⁻¹ : ℝ) : ℂ) := by
  have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
  conv_lhs => rw [e]
  rw [Complex.conj_ofReal, Complex.ofReal_inv]

/-- In a region stable under `μ ↦ 1/μ̄`, the negative real eigenvalues other than `-1` come in
pairs `μ, 1/μ`, one in `(-1, 0)` and one below `-1`. -/
theorem card_filter_neg_real {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) (R : ℂ → Prop) [DecidablePred R]
    (hR : ∀ z ∈ (cpx A).charpoly.roots, R z → R (starRingEnd ℂ z)⁻¹) :
    Multiset.card ((cpx A).charpoly.roots.filter fun z => R z ∧ z.im = 0 ∧ z.re < 0 ∧ z ≠ -1)
      = 2 * Multiset.card ((cpx A).charpoly.roots.filter fun z =>
          R z ∧ z.im = 0 ∧ -1 < z.re ∧ z.re < 0) := by
  have hR' : ∀ z ∈ (cpx A).charpoly.roots, R (starRingEnd ℂ z)⁻¹ ↔ R z := fun z hz =>
    ⟨fun h => by
      have := hR _ (inv_conj_mem_roots hA hz) h
      rwa [inv_conj_inv_conj] at this, hR z hz⟩
  have key : ∀ x : ℝ, x < 0 → (x⁻¹ < -1 ↔ -1 < x) := fun x hx => by
    rw [inv_eq_one_div, div_lt_iff_of_neg hx]
    constructor <;> intro h <;> linarith
  have h := card_filter_eq_two_mul (roots_map_inv_conj hA)
    (fun z => R z ∧ z.im = 0 ∧ -1 < z.re ∧ z.re < 0)
    (fun z => R z ∧ z.im = 0 ∧ z.re < -1) (fun z _ h => by linarith [h.1.2.2.1, h.2.2.2])
    (fun z hz => by
      rw [hR' z hz]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have hzi : z.im = 0 := by
          by_contra hzi
          -- `im (1/z̄) = im z / |z|²`, nonzero
          rw [Complex.inv_im, Complex.conj_im, Complex.normSq_conj, neg_neg] at h2
          have hn : Complex.normSq z ≠ 0 := by
            rw [Ne, Complex.normSq_eq_zero]
            intro h0
            exact hzi (by rw [h0, Complex.zero_im])
          exact hzi ((div_eq_zero_iff.1 h2).resolve_right hn)
        rw [inv_conj_of_im_eq_zero hzi, Complex.ofReal_re] at h3
        refine ⟨h1, hzi, ?_, ?_⟩
        · have hx : z.re < 0 := by
            by_contra hx
            push Not at hx
            have : 0 ≤ z.re⁻¹ := inv_nonneg.2 hx
            linarith
          exact (key _ hx).1 h3
        · by_contra hx
          push Not at hx
          have : 0 ≤ z.re⁻¹ := inv_nonneg.2 hx
          linarith
      · rintro ⟨h1, h2, h3, h4⟩
        rw [inv_conj_of_im_eq_zero h2, Complex.ofReal_re, Complex.ofReal_im]
        exact ⟨h1, rfl, (key _ h4).2 h3⟩)
  rw [← h]
  congr 1
  refine Multiset.filter_congr fun z _ => ?_
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have h5 : z.re ≠ -1 := fun h5 => h4 (Complex.ext (by simp [h5]) (by simp [h2]))
    rcases lt_or_gt_of_ne h5 with h6 | h6
    · exact Or.inr ⟨h1, h2, h6⟩
    · exact Or.inl ⟨h1, h2, h6, h3⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨h1, h2, h4, fun h5 => by rw [h5] at h3; simp at h3⟩
    · exact ⟨h1, h2, by linarith, fun h5 => by rw [h5] at h3; simp at h3⟩

/-- **The multiplicity of `-1` is even.**  The characteristic polynomial `p` is self-reciprocal;
writing `p = (X + 1)^m q` with `q(-1) ≠ 0`, `q` is self-reciprocal of degree `2n - m`, and
evaluating `q(X) = X^{2n-m} q(1/X)` at `-1` gives `(-1)^{2n-m} = 1`. -/
theorem even_count_neg_one {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) : Even ((cpx A).charpoly.roots.count (-1)) := by
  classical
  set p := (cpx A).charpoly with hp
  have hp0 : p ≠ 0 := (charpoly_monic _).ne_zero
  rw [count_roots]
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 (-1)
  set mm := p.rootMultiplicity (-1) with hmm
  have hq0 : q.eval (-1) ≠ 0 := by
    rwa [dvd_iff_isRoot, IsRoot.def] at hq
  have hqne : q ≠ 0 := fun h => hq0 (by rw [h, eval_zero])
  set N := q.natDegree with hN
  have hcardN : Fintype.card (l ⊕ l) = mm + N := by
    rw [← charpoly_natDegree_eq_dim (cpx A), ← hp, hpq,
      natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _)) hqne, natDegree_pow, natDegree_X_sub_C,
      mul_one]
  -- `q(c) = c^N q(1/c)` away from `0` and `-1`
  have hqrefl : ∀ c : ℂ, c ≠ 0 → c ≠ -1 → q.eval c = c ^ N * q.eval c⁻¹ := by
    intro c hc0 hc1
    have h := charpoly_eval_inv hA hc0
    rw [← hp, hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_mul, eval_pow, eval_sub,
      eval_X, eval_C, hcardN, pow_add] at h
    have e : c ^ mm * (c⁻¹ - -1) ^ mm = (c - -1) ^ mm := by
      rw [← mul_pow]
      congr 1
      field_simp
      ring
    have hc1' : c - -1 ≠ 0 := fun h' => hc1 (by linear_combination h')
    have : (c - -1) ^ mm * (q.eval c - c ^ N * q.eval c⁻¹) = 0 := by
      linear_combination h + c ^ N * q.eval c⁻¹ * e
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hc1'))
  -- hence `q` is self-reciprocal
  have hrefl : reflect N q = q := by
    refine eq_of_infinite_eval_eq _ _
      (((Set.finite_singleton (0 : ℂ)).insert (-1)).infinite_compl.mono ?_)
    intro c hc
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
    have := invertibleOfNonzero (inv_ne_zero hc.2)
    have h : eval (⅟c⁻¹) (reflect N q) * (c⁻¹) ^ N = eval c⁻¹ q :=
      eval₂_reflect_mul_pow (RingHom.id ℂ) c⁻¹ N q le_rfl
    rw [invOf_eq_inv, inv_inv] at h
    show eval c (reflect N q) = eval c q
    rw [hqrefl c hc.2 hc.1, ← h, mul_left_comm, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hc.2),
      mul_one]
  -- evaluate at `-1`
  have h1 : eval (-1) q * (-1) ^ N = eval (-1) q := by
    have : Invertible (-1 : ℂ) := invertibleOfNonzero (by norm_num)
    have h : eval (⅟(-1 : ℂ)) (reflect N q) * (-1) ^ N = eval (-1) q :=
      eval₂_reflect_mul_pow (RingHom.id ℂ) (-1 : ℂ) N q le_rfl
    rw [invOf_eq_inv, inv_neg_one, hrefl] at h
    exact h
  have hNeven : Even N := by
    have : ((-1 : ℂ)) ^ N = 1 := mul_left_cancel₀ hq0 (h1.trans (mul_one _).symm)
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 this
  have hcard := even_card (l := l)
  rw [hcardN] at hcard
  exact (Nat.even_add.1 hcard).2 hNeven

end Symplectic

end EigenMult
end MorseFloer
