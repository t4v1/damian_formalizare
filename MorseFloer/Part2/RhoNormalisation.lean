import MorseFloer.Part2.RhoNaturality

/-!
# Properties of `ρ`: the normalisation

The normalisation clause of Theorem 7.1.3 for the map `ρ` of `Part2/Rho.lean`: if the spectrum
of the symplectic matrix `A` is real, `ρ(A) = (-1)^{m₀/2}`, with `m₀` the total multiplicity of
the negative eigenvalues (`rho_normalisation`).  When the characteristic polynomial splits over
`ℝ` its complex roots are the images of the real ones, so no eigenvalue lies on the upper half
of the unit circle and `ρ(A) = (-1)^{m(-1)/2} (-1)^{p}` with `p` the number of eigenvalues in
`(-1, 0)` (`rhoC_of_real`); and `m₀ = m(-1) + 2p`, the negative eigenvalues other than `-1`
coming in pairs `μ, 1/μ` (`Part2/EigenMult.lean`), with `m(-1)` even.
-/

open Polynomial Matrix Module

namespace MorseFloer
namespace Rho

open Chapter7 SymplecticEigen SymplecticSpectrum EigenDecomp EigenMult HermitianIndex
  SignatureContinuity

variable {l : Type*} [DecidableEq l] [Fintype l]

open Classical in
/-- **`ρ` of a matrix with real spectrum**, as a product of signs. -/
theorem rhoC_of_real (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (hreal : ∀ z ∈ M.charpoly.roots, z.im = 0) :
    rhoC M = (-1) ^ (M.charpoly.roots.count (-1) / 2)
      * (-1) ^ Multiset.card (M.charpoly.roots.filter fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0) := by
  set s := M.charpoly.roots with hs
  have hne1 : ∀ z ∈ s, ¬(‖z‖ = 1 ∧ 0 < z.im) := fun z hz h => by
    rw [hreal z hz] at h
    exact lt_irrefl _ h.2
  rw [rhoC, ← Finset.prod_filter_mul_prod_filter_not s.toFinset (fun z => z = -1) (factor M)]
  -- the factor at `-1`
  have e1 : ∏ μ ∈ s.toFinset.filter (fun z => z = -1), factor M μ
      = (-1) ^ (s.count (-1) / 2) := by
    by_cases hm : (-1 : ℂ) ∈ s
    · have : s.toFinset.filter (fun z => z = -1) = {-1} := by
        ext z
        rw [Finset.mem_filter, Multiset.mem_toFinset, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h⟩; exact h
        · rintro rfl; exact ⟨hm, rfl⟩
      rw [this, Finset.prod_singleton, factor_neg_one]
    · have : s.toFinset.filter (fun z => z = -1) = ∅ := by
        ext z
        rw [Finset.mem_filter, Multiset.mem_toFinset]
        simp only [Finset.notMem_empty, iff_false, not_and]
        rintro hz rfl
        exact hm hz
      rw [this, Finset.prod_empty, Multiset.count_eq_zero.2 hm]
      simp
  -- the factors on `(-1, 0)`
  have e2 : ∏ μ ∈ s.toFinset.filter (fun z => ¬z = -1), factor M μ
      = (-1) ^ Multiset.card (s.filter fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0) := by
    rw [← Finset.prod_filter_of_ne (s := s.toFinset.filter (fun z => ¬z = -1)) (f := factor M)
      (p := fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0) (fun z hz hne => by
        by_contra h
        rw [Finset.mem_filter, Multiset.mem_toFinset] at hz
        exact hne (factor_eq_one (hne1 z hz.1) hz.2 h)), ← prod_neg_one_pow_count]
    refine Finset.prod_congr ?_ fun μ hμ => ?_
    · ext z
      simp only [Finset.mem_filter, Multiset.mem_toFinset]
      constructor
      · rintro ⟨⟨h0, -⟩, h2⟩
        exact ⟨h0, h2⟩
      · rintro ⟨h0, h2⟩
        refine ⟨⟨h0, fun h => ?_⟩, h2⟩
        rw [h] at h2
        simp at h2
    · obtain ⟨hμs, him, hre1, hre2⟩ := Finset.mem_filter.1 hμ
      refine factor_of_real (hne1 μ (Multiset.mem_toFinset.1 hμs)) (fun h => ?_)
        ⟨him, hre1, hre2⟩
      rw [h] at hre1
      simp at hre1
  rw [e1, e2]

/-- The complex eigenvalues of a real matrix with real spectrum are its real eigenvalues. -/
theorem roots_cpx_of_hasRealSpectrum {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (h : HasRealSpectrum A) :
    (cpx A).charpoly.roots = A.charpoly.roots.map Complex.ofRealHom := by
  rw [charpoly_cpx, ← roots_map_of_injective_of_card_eq_natDegree Complex.ofRealHom.injective]
  rw [charpoly_natDegree_eq_dim]
  exact h

open Classical in
/-- **Normalisation: `ρ(A) = (-1)^{m₀/2}` when the spectrum is real** (Theorem 7.1.3). -/
theorem rho_normalisation (n : ℕ) {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ) (hreal : HasRealSpectrum A) :
    rho n A = (-1 : ℂ) ^ (negEigenCount A / 2) := by
  set s := (cpx A).charpoly.roots with hs
  have hroots := roots_cpx_of_hasRealSpectrum hreal
  have him : ∀ z ∈ s, z.im = 0 := by
    intro z hz
    rw [hs, hroots] at hz
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hz
    simp
  rw [rho, rhoC_of_real _ him, ← pow_add]
  congr 1
  -- the counts
  set c₁ := s.count (-1) with hc₁
  set p := Multiset.card (s.filter fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0) with hp
  set n₀ := Multiset.card (s.filter fun z => z.im = 0 ∧ z.re < 0) with hn₀
  set n₁ := Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ z.re < 0 ∧ z ≠ -1) with hn₁
  have h0 : negEigenCount A = n₀ := by
    rw [negEigenCount, hn₀, hs, hroots, Multiset.countP_eq_card_filter, Multiset.filter_map,
      Multiset.card_map]
    congr 1
    refine Multiset.filter_congr fun x _ => ?_
    simp
  have hc₁' : c₁ = Multiset.card (s.filter fun z => z = -1) := by
    rw [hc₁, Multiset.count_eq_card_filter_eq]
    congr 1
    exact Multiset.filter_congr fun z _ => eq_comm
  have h1 : n₀ = Multiset.card (s.filter fun z => z = -1) + n₁ := by
    refine card_filter_eq_add s _ _ _ (fun z _ => ?_) (fun z _ h => h.2.2.2.2 h.1)
    constructor
    · rintro ⟨hz1, hz2⟩
      by_cases hz : z = -1
      · exact Or.inl hz
      · exact Or.inr ⟨trivial, hz1, hz2, hz⟩
    · rintro (rfl | ⟨-, hz1, hz2, -⟩)
      · exact ⟨by simp, by simp⟩
      · exact ⟨hz1, hz2⟩
  have h2 : n₁ = 2 * Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ -1 < z.re ∧ z.re < 0) :=
    card_filter_neg_real hA (fun _ => True) fun _ _ _ => trivial
  have h3 : Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ -1 < z.re ∧ z.re < 0) = p := by
    rw [hp]
    congr 1
    exact Multiset.filter_congr fun z _ => by simp
  obtain ⟨k, hk⟩ := even_count_neg_one hA
  rw [← hc₁] at hk
  omega

end Rho
end MorseFloer
