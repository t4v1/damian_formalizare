import MorseFloer.Part2.RhoUnitary

/-!
# Lemma 7.1.6: the lift of `ρ` to `ℝ` on `Sp(2n)⋆`

The map `ρ` of `Part2/Rho.lean` admits a continuous real lift through `θ ↦ e^{iθ}` on each of
the two components `Sp(2n)±` of `Sp(2n)⋆ = {A : det(A - 1) ≠ 0}` (§7.3.d).  The lift is written,
as in the book, as a sum over the distinct eigenvalues `μ` of a local term (`liftTerm`):
`2π m₋(μ) + σ(μ) arg μ` on the upper half of the unit circle, `π m(μ)` on the rest of the upper
half-plane, `(π/2) m(μ)` on the real axis, `0` below it (`rhoLiftC`, `rhoLift`), plus the
constant `π` on `Sp(2n)⁻`.

This file proves that it is a lift: `exp(i ρ̃(A)) = ρ(A) (-1)^q`, where `q` is the number of
real eigenvalues larger than `1` (`exp_rhoLiftC`) — the upper-circle terms give the factors
`μ^{σ(μ)}`, the other upper eigenvalues pair as `μ, 1/μ̄` so their contribution is `1`, and the
real eigenvalues give `(-1)^{m₀/2}` up to `(-1)^q`, the positive ones pairing as `μ, 1/μ` — and
that `(-1)^q` is the sign of `det(A - 1)` (`det_sub_one_pos_iff`), which is a product of
`(1 - μ)` over the eigenvalues, the non-real ones pairing into `|1 - μ|²`.  Hence
`exp(i ρ̃) = ρ` on `Sp(2n)⁺` and `exp(i(ρ̃ + π)) = ρ` on `Sp(2n)⁻`.  The continuity of `ρ̃` on
`Sp(2n)⋆` is proved in `Part2/RhoLiftContinuity.lean`.
-/

open Polynomial Matrix Module Filter Topology

namespace MorseFloer
namespace Rho

open Chapter7 SymplecticEigen SymplecticSpectrum EigenDecomp EigenMult HermitianIndex
  SignatureContinuity

/-! ### Multisets under an involution -/

theorem filter_eq_map_of_involution {s : Multiset ℂ} {σ : ℂ → ℂ} (hσ : s.map σ = s)
    (P Q : ℂ → Prop) [DecidablePred P] [DecidablePred Q] (hσP : ∀ z ∈ s, Q (σ z) ↔ P z) :
    s.filter Q = (s.filter P).map σ := by
  conv_lhs => rw [← hσ]
  rw [Multiset.filter_map]
  congr 1
  exact Multiset.filter_congr fun z hz => hσP z hz

theorem prod_pos_of_forall (s : Multiset ℝ) (h : ∀ x ∈ s, 0 < x) : 0 < s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact mul_pos (h a (Multiset.mem_cons_self a s))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

theorem filter_eq_add_of_dichotomy (s : Multiset ℂ) (P Q R : ℂ → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred R] (h1 : ∀ z ∈ s, P z ↔ Q z ∨ R z)
    (h2 : ∀ z ∈ s, ¬(Q z ∧ R z)) : s.filter P = s.filter Q + s.filter R := by
  rw [Multiset.filter_add_filter, Multiset.filter_eq_nil.2 h2, add_zero]
  exact Multiset.filter_congr h1

variable {l : Type*} [DecidableEq l] [Fintype l]

theorem im_inv_conj_eq_zero_iff {z : ℂ} (hz : z ≠ 0) :
    ((starRingEnd ℂ z)⁻¹).im = 0 ↔ z.im = 0 := by
  rw [Complex.inv_im, Complex.conj_im, Complex.normSq_conj, neg_neg, div_eq_zero_iff]
  have : Complex.normSq z ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  simp [this]

/-- In a region stable under `μ ↦ 1/μ̄`, the real eigenvalues larger than `1` are as many as
those in `(0, 1)`. -/
theorem card_filter_pos_real {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) (R : ℂ → Prop) [DecidablePred R]
    (hR : ∀ z ∈ (cpx A).charpoly.roots, R z → R (starRingEnd ℂ z)⁻¹) :
    Multiset.card ((cpx A).charpoly.roots.filter fun z => R z ∧ z.im = 0 ∧ 1 < z.re)
      = Multiset.card ((cpx A).charpoly.roots.filter fun z =>
          R z ∧ z.im = 0 ∧ 0 < z.re ∧ z.re < 1) := by
  have hR' : ∀ z ∈ (cpx A).charpoly.roots, R (starRingEnd ℂ z)⁻¹ ↔ R z := fun z hz =>
    ⟨fun h => by
      have := hR _ (inv_conj_mem_roots hA hz) h
      rwa [inv_conj_inv_conj] at this, hR z hz⟩
  rw [filter_eq_map_of_involution (roots_map_inv_conj hA)
    (fun z => R z ∧ z.im = 0 ∧ 0 < z.re ∧ z.re < 1) (fun z => R z ∧ z.im = 0 ∧ 1 < z.re)
    (fun z hz => ?_), Multiset.card_map]
  have hz0 : z ≠ 0 := fun h0 => zero_notMem_roots hA (h0 ▸ hz)
  rw [hR' z hz, im_inv_conj_eq_zero_iff hz0]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [inv_conj_of_im_eq_zero h2, Complex.ofReal_re, one_lt_inv_iff₀] at h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [inv_conj_of_im_eq_zero h2, Complex.ofReal_re, one_lt_inv_iff₀]
    exact h3

/-! ### The lift -/

open Classical in
theorem mPos_le_count (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) :
    mPos M μ ≤ M.charpoly.roots.count μ := by
  rw [mPos, ← finrank_E]
  exact posIndex_le_finrank _ _

open Classical in
/-- The local term of the lift at the eigenvalue `μ`. -/
noncomputable def liftTerm (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) : ℝ :=
  if ‖μ‖ = 1 ∧ 0 < μ.im then
    2 * Real.pi * ((M.charpoly.roots.count μ : ℝ) - (mPos M μ : ℝ))
      + (sigma M μ : ℝ) * Complex.arg μ
  else if 0 < μ.im then Real.pi * (M.charpoly.roots.count μ : ℝ)
  else if μ.im = 0 then Real.pi / 2 * (M.charpoly.roots.count μ : ℝ)
  else 0

open Classical in
/-- The lift on complex matrices. -/
noncomputable def rhoLiftC (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) : ℝ :=
  ∑ μ ∈ M.charpoly.roots.toFinset, liftTerm M μ

/-- **The lift `ρ̃` of §7.3.d**, on `Sp(2n)⁺`; on `Sp(2n)⁻` the lift is `ρ̃ + π`. -/
noncomputable def rhoLift (n : ℕ) (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) : ℝ :=
  rhoLiftC (cpx A)

open Classical in
theorem liftTerm_of_circle {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} (h : ‖μ‖ = 1 ∧ 0 < μ.im) :
    liftTerm M μ = 2 * Real.pi * ((M.charpoly.roots.count μ : ℝ) - (mPos M μ : ℝ))
      + (sigma M μ : ℝ) * Complex.arg μ := by
  rw [liftTerm, ite_eq_left h]

open Classical in
theorem liftTerm_of_upper {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} (h1 : ¬(‖μ‖ = 1 ∧ 0 < μ.im))
    (h2 : 0 < μ.im) : liftTerm M μ = Real.pi * (M.charpoly.roots.count μ : ℝ) := by
  rw [liftTerm, ite_eq_right h1, ite_eq_left h2]

open Classical in
theorem liftTerm_of_real {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} (h : μ.im = 0) :
    liftTerm M μ = Real.pi / 2 * (M.charpoly.roots.count μ : ℝ) := by
  rw [liftTerm, ite_eq_right (fun h' => by rw [h] at h'; exact lt_irrefl _ h'.2),
    ite_eq_right (by rw [h]; exact lt_irrefl _), ite_eq_left h]

open Classical in
theorem liftTerm_of_lower {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} (h : μ.im < 0) :
    liftTerm M μ = 0 := by
  rw [liftTerm, ite_eq_right (fun h' => by linarith [h'.2]), ite_eq_right (by linarith), ite_eq_right h.ne]

/-! ### `exp(i ρ̃) = ρ (-1)^q` -/

open Classical in
theorem exp_liftTerm_circle {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} (h : ‖μ‖ = 1 ∧ 0 < μ.im) :
    Complex.exp (liftTerm M μ * Complex.I) = factor M μ := by
  rw [liftTerm_of_circle h, factor_of_circle h]
  set c := M.charpoly.roots.count μ with hc
  set p := mPos M μ with hp
  set σ := sigma M μ with hσ
  have e : ((2 * Real.pi * ((c : ℝ) - (p : ℝ)) + (σ : ℝ) * Complex.arg μ : ℝ) : ℂ) * Complex.I
      = ((c - p : ℤ) : ℂ) * (2 * Real.pi * Complex.I) + (σ : ℂ) * (Complex.arg μ * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_int_mul]
  have := Complex.norm_mul_exp_arg_mul_I μ
  rw [h.1, Complex.ofReal_one, one_mul] at this
  rw [this]

open Classical in
theorem exp_liftTerm_upper {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} (h1 : ¬(‖μ‖ = 1 ∧ 0 < μ.im))
    (h2 : 0 < μ.im) : Complex.exp (liftTerm M μ * Complex.I) = (-1) ^ M.charpoly.roots.count μ := by
  rw [liftTerm_of_upper h1 h2]
  have e : ((Real.pi * (M.charpoly.roots.count μ : ℝ) : ℝ) : ℂ) * Complex.I
      = (M.charpoly.roots.count μ : ℕ) * (Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

open Classical in
theorem exp_liftTerm_real {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} (h : μ.im = 0) :
    Complex.exp (liftTerm M μ * Complex.I)
      = Complex.exp ((M.charpoly.roots.count μ : ℕ) * (Real.pi / 2 * Complex.I)) := by
  rw [liftTerm_of_real h]
  congr 1
  push_cast
  ring

/-- A four-way split of a product over the distinct eigenvalues. -/
theorem prod_split4 (T : Finset ℂ) (f : ℂ → ℂ) :
    ∏ μ ∈ T, f μ
      = (∏ μ ∈ T.filter (fun z => ‖z‖ = 1 ∧ 0 < z.im), f μ)
        * ((∏ μ ∈ T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ 0 < z.im), f μ)
        * ((∏ μ ∈ T.filter (fun z => z.im = 0), f μ)
        * ∏ μ ∈ T.filter (fun z => z.im < 0), f μ)) := by
  have e3 : ((T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im))).filter (fun z => ¬0 < z.im)).filter
      (fun z => z.im = 0) = T.filter (fun z => z.im = 0) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨h0, -⟩, -⟩, h⟩
      exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩
      exact ⟨⟨⟨h0, fun h' => by rw [h] at h'; exact lt_irrefl _ h'.2⟩, by rw [h]; exact lt_irrefl _⟩, h⟩
  have e4 : ((T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im))).filter (fun z => ¬0 < z.im)).filter
      (fun z => ¬z.im = 0) = T.filter (fun z => z.im < 0) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨h0, -⟩, h1⟩, h2⟩
      exact ⟨h0, lt_of_le_of_ne (not_lt.1 h1) h2⟩
    · rintro ⟨h0, h⟩
      exact ⟨⟨⟨h0, fun h' => by linarith [h'.2]⟩, by linarith⟩, h.ne⟩
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun z => ‖z‖ = 1 ∧ 0 < z.im),
    ← Finset.prod_filter_mul_prod_filter_not (T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im)))
      (fun z => 0 < z.im),
    ← Finset.prod_filter_mul_prod_filter_not ((T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im))).filter
      (fun z => ¬0 < z.im)) (fun z => z.im = 0), e3, e4, Finset.filter_filter]

open Classical in
/-- The product of the real factors: `(-1)^{m(-1)/2} (-1)^{#(-1, 0)}`. -/
theorem prod_factor_real (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) :
    ∏ μ ∈ M.charpoly.roots.toFinset.filter (fun z => z.im = 0), factor M μ
      = (-1) ^ (M.charpoly.roots.count (-1) / 2)
        * (-1) ^ Multiset.card (M.charpoly.roots.filter fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0) := by
  set s := M.charpoly.roots with hs
  set T := s.toFinset.filter (fun z => z.im = 0) with hT
  have hne1 : ∀ z ∈ T, ¬(‖z‖ = 1 ∧ 0 < z.im) := fun z hz h => by
    rw [hT, Finset.mem_filter] at hz
    rw [hz.2] at h
    exact lt_irrefl _ h.2
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun z => z = -1) (factor M)]
  have e1 : ∏ μ ∈ T.filter (fun z => z = -1), factor M μ = (-1) ^ (s.count (-1) / 2) := by
    by_cases hm : (-1 : ℂ) ∈ s
    · have : T.filter (fun z => z = -1) = {-1} := by
        ext z
        rw [Finset.mem_filter, hT, Finset.mem_filter, Multiset.mem_toFinset, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h⟩; exact h
        · rintro rfl; exact ⟨⟨hm, by simp⟩, rfl⟩
      rw [this, Finset.prod_singleton, factor_neg_one]
    · have : T.filter (fun z => z = -1) = ∅ := by
        ext z
        rw [Finset.mem_filter, hT, Finset.mem_filter, Multiset.mem_toFinset]
        simp only [Finset.notMem_empty, iff_false, not_and]
        rintro ⟨hz, -⟩ rfl
        exact hm hz
      rw [this, Finset.prod_empty, Multiset.count_eq_zero.2 hm]
      simp
  have e2 : ∏ μ ∈ T.filter (fun z => ¬z = -1), factor M μ
      = (-1) ^ Multiset.card (s.filter fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0) := by
    rw [← Finset.prod_filter_of_ne (s := T.filter (fun z => ¬z = -1)) (f := factor M)
      (p := fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0) (fun z hz hne => by
        by_contra h
        rw [Finset.mem_filter] at hz
        exact hne (factor_eq_one (hne1 z hz.1) hz.2 h)), ← prod_neg_one_pow_count]
    refine Finset.prod_congr ?_ fun μ hμ => ?_
    · ext z
      rw [hT]
      simp only [Finset.mem_filter, Multiset.mem_toFinset]
      constructor
      · rintro ⟨⟨⟨h0, -⟩, -⟩, h2⟩
        exact ⟨h0, h2⟩
      · rintro ⟨h0, h2⟩
        refine ⟨⟨⟨h0, h2.1⟩, fun h => ?_⟩, h2⟩
        rw [h] at h2
        simp at h2
    · obtain ⟨hμs, him, hre1, hre2⟩ := Finset.mem_filter.1 hμ
      refine factor_of_real (fun h => ?_) (fun h => ?_) ⟨him, hre1, hre2⟩
      · rw [him] at h
        exact lt_irrefl _ h.2
      · rw [h] at hre1
        simp at hre1
  rw [e1, e2]

open Classical in
/-- The sum of the multiplicities of the real eigenvalues, for a symplectic matrix without the
eigenvalue `1`: `m(-1) + 2p + 2q`. -/
theorem card_filter_real_eq {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) (h1 : (1 : ℂ) ∉ (cpx A).charpoly.roots) :
    Multiset.card ((cpx A).charpoly.roots.filter fun z => z.im = 0)
      = (cpx A).charpoly.roots.count (-1)
        + 2 * Multiset.card ((cpx A).charpoly.roots.filter fun z =>
            z.im = 0 ∧ -1 < z.re ∧ z.re < 0)
        + 2 * Multiset.card ((cpx A).charpoly.roots.filter fun z => z.im = 0 ∧ 1 < z.re) := by
  set s := (cpx A).charpoly.roots with hs
  have h0 : ∀ z ∈ s, z ≠ 0 := fun z hz h => zero_notMem_roots hA (h ▸ hz)
  have hc : s.count (-1) = Multiset.card (s.filter fun z => z = -1) := by
    rw [Multiset.count_eq_card_filter_eq]
    congr 1
    exact Multiset.filter_congr fun z _ => eq_comm
  -- real = (negative) + (positive)
  have e1 : Multiset.card (s.filter fun z => z.im = 0)
      = Multiset.card (s.filter fun z => z.im = 0 ∧ z.re < 0)
        + Multiset.card (s.filter fun z => z.im = 0 ∧ 0 < z.re) := by
    refine card_filter_eq_add s _ _ _ (fun z hz => ?_) (fun z _ h => by linarith [h.1.2, h.2.2])
    constructor
    · intro h
      rcases lt_trichotomy z.re 0 with h' | h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact absurd (Complex.ext h' h) (h0 z hz)
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h) <;> exact h.1
  -- negative = {-1} + (the others), which pair off
  have e2 : Multiset.card (s.filter fun z => z.im = 0 ∧ z.re < 0)
      = Multiset.card (s.filter fun z => z = -1)
        + Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ z.re < 0 ∧ z ≠ -1) := by
    refine card_filter_eq_add s _ _ _ (fun z _ => ?_) (fun z _ h => h.2.2.2.2 h.1)
    constructor
    · rintro ⟨hz1, hz2⟩
      by_cases hz : z = -1
      · exact Or.inl hz
      · exact Or.inr ⟨trivial, hz1, hz2, hz⟩
    · rintro (rfl | ⟨-, hz1, hz2, -⟩)
      · exact ⟨by simp, by simp⟩
      · exact ⟨hz1, hz2⟩
  have e3 : Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ z.re < 0 ∧ z ≠ -1)
      = 2 * Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ -1 < z.re ∧ z.re < 0) :=
    card_filter_neg_real hA (fun _ => True) fun _ _ _ => trivial
  have e3' : Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ -1 < z.re ∧ z.re < 0)
      = Multiset.card (s.filter fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0) := by
    congr 1
    exact Multiset.filter_congr fun z _ => by simp
  -- positive = (0, 1) + (1, ∞), which pair off
  have e4 : Multiset.card (s.filter fun z => z.im = 0 ∧ 0 < z.re)
      = Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ 0 < z.re ∧ z.re < 1)
        + Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ 1 < z.re) := by
    refine card_filter_eq_add s _ _ _ (fun z hz => ?_) (fun z _ h => by linarith [h.1.2.2.2, h.2.2.2])
    constructor
    · rintro ⟨hz1, hz2⟩
      rcases lt_trichotomy z.re 1 with h' | h' | h'
      · exact Or.inl ⟨trivial, hz1, hz2, h'⟩
      · exact absurd (by rw [Complex.ext_iff]; simp [h', hz1] : z = 1) (fun h => h1 (h ▸ hz))
      · exact Or.inr ⟨trivial, hz1, h'⟩
    · rintro (⟨-, hz1, hz2, -⟩ | ⟨-, hz1, hz2⟩)
      · exact ⟨hz1, hz2⟩
      · exact ⟨hz1, by linarith⟩
  have e5 : Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ 1 < z.re)
      = Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ 0 < z.re ∧ z.re < 1) :=
    card_filter_pos_real hA (fun _ => True) fun _ _ _ => trivial
  have e5' : Multiset.card (s.filter fun z => True ∧ z.im = 0 ∧ 1 < z.re)
      = Multiset.card (s.filter fun z => z.im = 0 ∧ 1 < z.re) := by
    congr 1
    exact Multiset.filter_congr fun z _ => by simp
  omega

open Classical in
/-- **The lift is a lift, up to the sign `(-1)^q`**: for a symplectic `A` without the
eigenvalue `1`, `exp(i ρ̃(A)) = ρ(A) (-1)^q`, `q` being the number of real eigenvalues
larger than `1`. -/
theorem exp_rhoLiftC {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    (h1 : (1 : ℂ) ∉ (cpx A).charpoly.roots) :
    Complex.exp (rhoLiftC (cpx A) * Complex.I)
      = rhoC (cpx A)
        * (-1) ^ Multiset.card ((cpx A).charpoly.roots.filter fun z => z.im = 0 ∧ 1 < z.re) := by
  set M := cpx A with hM
  set s := M.charpoly.roots with hs
  set T := s.toFinset with hT
  rw [rhoLiftC, rhoC, ← hs, ← hT, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum,
    prod_split4, prod_split4 T (factor M)]
  -- the upper circle
  have hP1 : ∏ μ ∈ T.filter (fun z => ‖z‖ = 1 ∧ 0 < z.im), Complex.exp (liftTerm M μ * Complex.I)
      = ∏ μ ∈ T.filter (fun z => ‖z‖ = 1 ∧ 0 < z.im), factor M μ :=
    Finset.prod_congr rfl fun μ hμ => exp_liftTerm_circle (Finset.mem_filter.1 hμ).2
  -- the rest of the upper half-plane: an even number of eigenvalues
  have hP2 : ∏ μ ∈ T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ 0 < z.im),
      Complex.exp (liftTerm M μ * Complex.I) = 1 := by
    rw [Finset.prod_congr rfl fun μ hμ =>
      exp_liftTerm_upper (Finset.mem_filter.1 hμ).2.1 (Finset.mem_filter.1 hμ).2.2,
      prod_neg_one_pow_count]
    have h := card_filter_norm_ne_one hA (fun z => 0 < z.im) fun z hz h => by
      have hz0 : z ≠ 0 := fun h0 => zero_notMem_roots hA (h0 ▸ hz)
      rw [Complex.inv_im, Complex.conj_im, Complex.normSq_conj, neg_neg]
      exact div_pos h (Complex.normSq_pos.2 hz0)
    have e : (s.filter fun z => ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ 0 < z.im)
        = s.filter fun z => 0 < z.im ∧ ‖z‖ ≠ 1 := by
      refine Multiset.filter_congr fun z _ => ?_
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, fun h => h1 ⟨h, h2⟩⟩
      · rintro ⟨h1, h2⟩; exact ⟨fun h => h2 h.1, h1⟩
    rw [e, h, pow_mul]
    simp
  have hP2' : ∏ μ ∈ T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ 0 < z.im), factor M μ = 1 := by
    refine Finset.prod_eq_one fun μ hμ => ?_
    obtain ⟨-, h1', h2'⟩ := Finset.mem_filter.1 hμ
    exact factor_eq_one h1' (fun h => by rw [h] at h2'; simp at h2') (fun h => by linarith [h.1])
  -- the lower half-plane
  have hP4 : ∏ μ ∈ T.filter (fun z => z.im < 0), Complex.exp (liftTerm M μ * Complex.I) = 1 := by
    refine Finset.prod_eq_one fun μ hμ => ?_
    rw [liftTerm_of_lower (Finset.mem_filter.1 hμ).2]
    simp
  have hP4' : ∏ μ ∈ T.filter (fun z => z.im < 0), factor M μ = 1 := by
    refine Finset.prod_eq_one fun μ hμ => ?_
    have h := (Finset.mem_filter.1 hμ).2
    exact factor_eq_one (fun h' => by linarith [h'.2]) (fun h' => by rw [h'] at h; simp at h)
      (fun h' => by linarith [h'.1])
  -- the real axis
  have hP3 : ∏ μ ∈ T.filter (fun z => z.im = 0), Complex.exp (liftTerm M μ * Complex.I)
      = (∏ μ ∈ T.filter (fun z => z.im = 0), factor M μ)
        * (-1) ^ Multiset.card (s.filter fun z => z.im = 0 ∧ 1 < z.re) := by
    rw [Finset.prod_congr rfl fun μ hμ => exp_liftTerm_real (Finset.mem_filter.1 hμ).2,
      ← Complex.exp_sum, ← Finset.sum_mul, ← Nat.cast_sum, sum_count_filter, prod_factor_real,
      card_filter_real_eq hA h1]
    obtain ⟨k, hk⟩ := even_count_neg_one hA
    rw [← hs] at hk
    rw [hk]
    set p := Multiset.card (s.filter fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0) with hp
    set q := Multiset.card (s.filter fun z => z.im = 0 ∧ 1 < z.re) with hq
    have e : ((k + k + 2 * p + 2 * q : ℕ) : ℂ) * (Real.pi / 2 * Complex.I)
        = ((k + p + q : ℕ) : ℂ) * (Real.pi * Complex.I) := by
      push_cast
      ring
    rw [e, Complex.exp_nat_mul, Complex.exp_pi_mul_I, pow_add, pow_add,
      show (k + k) / 2 = k by omega]
  rw [hP1, hP2, hP2', hP3, hP4, hP4']
  ring

/-! ### The sign of `det(A - 1)` -/

theorem cpx_sub_one (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) : cpx (A - 1) = cpx A - 1 := by
  rw [cpx, cpx, ← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply]

theorem det_cpx (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) : (cpx A).det = ((A.det : ℝ) : ℂ) :=
  (RingHom.map_det Complex.ofRealHom A).symm

/-- `det(A - 1)` as the product of `1 - μ` over the eigenvalues. -/
theorem det_sub_one_eq_prod (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    (((A - 1).det : ℝ) : ℂ) = ((cpx A).charpoly.roots.map fun z => 1 - z).prod := by
  rw [← det_cpx, cpx_sub_one]
  have h := charpoly_eval (cpx A) 1
  rw [one_smul] at h
  rw [← h]
  conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic (cpx A))
    IsAlgClosed.card_roots_eq_natDegree]
  rw [eval_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun z _ => ?_
  simp

theorem one_notMem_roots_iff (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    (1 : ℂ) ∉ (cpx A).charpoly.roots ↔ (A - 1).det ≠ 0 := by
  rw [mem_roots (charpoly_monic _).ne_zero, IsRoot.def, charpoly_eval, one_smul, ← cpx_sub_one,
    det_cpx]
  constructor
  · intro h h'
    exact h (by rw [h']; simp)
  · intro h h'
    exact h (Complex.ofReal_eq_zero.1 h')

open Classical in
/-- **The sign of `det(A - 1)`** for a symplectic `A` without the eigenvalue `1`: it is
`(-1)^q`, `q` the number of real eigenvalues larger than `1`. -/
theorem det_sub_one_pos_iff {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (h1 : (1 : ℂ) ∉ (cpx A).charpoly.roots) :
    0 < (A - 1).det
      ↔ Even (Multiset.card ((cpx A).charpoly.roots.filter fun z => z.im = 0 ∧ 1 < z.re)) := by
  set s := (cpx A).charpoly.roots with hs
  -- the eigenvalues: real, upper, lower (the lower ones conjugate to the upper ones)
  have hsplit : s = s.filter (fun z => z.im = 0) + s.filter (fun z => 0 < z.im)
      + (s.filter (fun z => 0 < z.im)).map (starRingEnd ℂ) := by
    have e1 : s = s.filter (fun z => z.im = 0) + s.filter (fun z => ¬z.im = 0) :=
      (Multiset.filter_add_not _ _).symm
    have e2 : s.filter (fun z => ¬z.im = 0) = s.filter (fun z => 0 < z.im)
        + s.filter (fun z => z.im < 0) := by
      refine filter_eq_add_of_dichotomy s _ _ _ (fun z _ => ?_) (fun z _ h => by linarith [h.1, h.2])
      constructor
      · intro h
        rcases lt_or_gt_of_ne h with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'
      · rintro (h | h)
        · exact h.ne'
        · exact h.ne
    have e3 : s.filter (fun z => z.im < 0) = (s.filter (fun z => 0 < z.im)).map (starRingEnd ℂ) :=
      filter_eq_map_of_involution (roots_map_conj A) _ _ fun z _ => by
        rw [Complex.conj_im]
        constructor <;> intro h <;> linarith
    rw [← e3, add_assoc, ← e2, ← e1]
  have hprod := det_sub_one_eq_prod A
  rw [← hs] at hprod
  conv_rhs at hprod => rw [hsplit]
  rw [Multiset.map_add, Multiset.map_add, Multiset.prod_add, Multiset.prod_add,
    Multiset.map_map] at hprod
  -- the non-real part is `|w|²`
  set w := ((s.filter fun z => 0 < z.im).map fun z => 1 - z).prod with hw
  have hconj : ((s.filter fun z => 0 < z.im).map ((fun z => 1 - z) ∘ starRingEnd ℂ)).prod
      = starRingEnd ℂ w := by
    rw [hw, map_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun z _ => ?_
    simp
  rw [hconj] at hprod
  have hw0 : w ≠ 0 := by
    rw [hw]
    refine Multiset.prod_ne_zero ?_
    intro h
    obtain ⟨z, hz, hz1⟩ := Multiset.mem_map.1 h
    have := (Multiset.mem_filter.1 hz).2
    rw [sub_eq_zero] at hz1
    rw [← hz1] at this
    simp at this
  -- the real part
  set R := (s.filter fun z => z.im = 0).map fun z => 1 - z.re with hR
  have hreal : ((s.filter fun z => z.im = 0).map fun z => 1 - z).prod = ((R.prod : ℝ) : ℂ) := by
    have e : ((R.prod : ℝ) : ℂ) = Complex.ofRealHom R.prod := rfl
    rw [e, hR, map_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun z hz => ?_
    have him := (Multiset.mem_filter.1 hz).2
    apply Complex.ext <;> simp [him]
  rw [hreal, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul] at hprod
  have hdet : (A - 1).det = R.prod * Complex.normSq w := Complex.ofReal_injective hprod
  -- the sign of the real part
  have hRsplit : (s.filter fun z => z.im = 0)
      = (s.filter fun z => z.im = 0 ∧ z.re < 1) + s.filter fun z => z.im = 0 ∧ 1 < z.re := by
    refine filter_eq_add_of_dichotomy s _ _ _ (fun z hz => ?_) (fun z _ h => by linarith [h.1.2, h.2.2])
    constructor
    · intro h
      rcases lt_trichotomy z.re 1 with h' | h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact absurd (by rw [Complex.ext_iff]; simp [h', h] : z = 1) (fun e => h1 (e ▸ hz))
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h) <;> exact h.1
  have hR1 : 0 < ((s.filter fun z => z.im = 0 ∧ z.re < 1).map fun z => 1 - z.re).prod := by
    refine prod_pos_of_forall _ fun x hx => ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
    linarith [(Multiset.mem_filter.1 hz).2.2]
  have hR2 : ((s.filter fun z => z.im = 0 ∧ 1 < z.re).map fun z => 1 - z.re).prod
      = (-1) ^ Multiset.card (s.filter fun z => z.im = 0 ∧ 1 < z.re)
        * ((s.filter fun z => z.im = 0 ∧ 1 < z.re).map fun z => z.re - 1).prod := by
    have hc : ((s.filter fun z => z.im = 0 ∧ 1 < z.re).map fun _ => (-1 : ℝ)).prod
        = (-1) ^ Multiset.card (s.filter fun z => z.im = 0 ∧ 1 < z.re) := by
      rw [Multiset.map_const', Multiset.prod_replicate]
    rw [← hc, ← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun z _ => ?_
    ring
  have hR3 : 0 < ((s.filter fun z => z.im = 0 ∧ 1 < z.re).map fun z => z.re - 1).prod := by
    refine prod_pos_of_forall _ fun x hx => ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
    linarith [(Multiset.mem_filter.1 hz).2.2]
  have hRprod : R.prod = ((s.filter fun z => z.im = 0 ∧ z.re < 1).map fun z => 1 - z.re).prod
      * ((-1) ^ Multiset.card (s.filter fun z => z.im = 0 ∧ 1 < z.re)
        * ((s.filter fun z => z.im = 0 ∧ 1 < z.re).map fun z => z.re - 1).prod) := by
    rw [hR, hRsplit, Multiset.map_add, Multiset.prod_add, hR2]
  have hnorm : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
  rw [hdet, hRprod]
  set q := Multiset.card (s.filter fun z => z.im = 0 ∧ 1 < z.re) with hq
  set P₁ := ((s.filter fun z => z.im = 0 ∧ z.re < 1).map fun z => 1 - z.re).prod with hP₁
  set P₂ := ((s.filter fun z => z.im = 0 ∧ 1 < z.re).map fun z => z.re - 1).prod with hP₂
  have hpos : 0 < P₁ * P₂ * Complex.normSq w := mul_pos (mul_pos hR1 hR3) hnorm
  rcases Nat.even_or_odd q with hq' | hq'
  · rw [hq'.neg_one_pow, one_mul]
    exact ⟨fun _ => hq', fun _ => hpos⟩
  · rw [hq'.neg_one_pow]
    constructor
    · intro h
      have e : P₁ * (-1 * P₂) * Complex.normSq w = -(P₁ * P₂ * Complex.normSq w) := by ring
      rw [e] at h
      linarith
    · intro h
      exact absurd h (Nat.not_even_iff_odd.2 hq')

/-! ### The lift on `Sp(2n)±` -/

/-- **Lemma 7.1.6 on `Sp(2n)⁺`**: `exp(i ρ̃(A)) = ρ(A)` when `det(A - 1) > 0`. -/
theorem exp_rhoLift_plus (n : ℕ) {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ) (hdet : 0 < (A - 1).det) :
    Complex.exp (rhoLift n A * Complex.I) = rho n A := by
  classical
  have h1 : (1 : ℂ) ∉ (cpx A).charpoly.roots := (one_notMem_roots_iff A).2 hdet.ne'
  rw [rhoLift, rho, exp_rhoLiftC hA h1, ((det_sub_one_pos_iff h1).1 hdet).neg_one_pow, mul_one]

/-- **Lemma 7.1.6 on `Sp(2n)⁻`**: `exp(i(ρ̃(A) + π)) = ρ(A)` when `det(A - 1) < 0`. -/
theorem exp_rhoLift_minus (n : ℕ) {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ) (hdet : (A - 1).det < 0) :
    Complex.exp ((rhoLift n A + Real.pi) * Complex.I) = rho n A := by
  classical
  have h1 : (1 : ℂ) ∉ (cpx A).charpoly.roots := (one_notMem_roots_iff A).2 hdet.ne
  have hodd : Odd (Multiset.card ((cpx A).charpoly.roots.filter fun z => z.im = 0 ∧ 1 < z.re)) := by
    rw [← Nat.not_even_iff_odd]
    intro h
    exact absurd ((det_sub_one_pos_iff h1).2 h) (not_lt.2 hdet.le)
  rw [add_mul, Complex.exp_add, rhoLift, rho, exp_rhoLiftC hA h1,
    hodd.neg_one_pow, Complex.exp_pi_mul_I]
  ring

end Rho
end MorseFloer
