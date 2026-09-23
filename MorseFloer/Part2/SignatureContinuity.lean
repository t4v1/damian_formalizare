import MorseFloer.Part2.HermitianIndex
import MorseFloer.Part2.EigenDecomp

/-!
# Local constancy of the signature on the eigenvalues in a disc

A brick for the map `ρ` of Chapter 7 (§7.3.c, Propositions 7.3.6–7.3.8).  For a complex
matrix `A` and a disc `D(c, r)`, let `V_A = ker f_A(A)` be the sum of the generalised eigenspaces
of `A` for the eigenvalues in the disc (`discSpace`, from `Part2/EigenDecomp.lean`), and let
`G(X, Y) = -i ω(X, Ȳ)` be the Hermitian form whose diagonal is the quadratic form `Q` of §7.3.a
(`GForm`).  The theorem `eventually_posIndex_eq` says that the positive index of `G` on `V_A`
(`HermitianIndex.posIndex`) is locally constant in `A`, near any `A₀` without eigenvalues on the
circle and on whose `V_{A₀}` the form is nondegenerate — which, for a symplectic `A₀` and a disc
whose eigenvalues are stable under `μ ↦ 1/μ̄`, is Corollary 7.3.4 as proved in
`Part2/EigenDecomp.lean`.

The proof transports a basis of `V_{A₀}` by the continuous spectral projector `P_A` of
`Part2/SpectralProjector.lean`: near `A₀` the transported family is still linearly independent
(an open condition), together with the family transported by `1 - P_A` it spans everything, so it
spans exactly `V_A`; the index is then the number of positive eigenvalues of the Gram matrix of
that family (Sylvester, `HermitianIndex.posIndex_eq_countP`), which depends continuously on `A`,
and the number of roots of the characteristic polynomial in the open half-plane `Re > 0` cannot
jump as long as none of them sits on the imaginary axis — which is the nondegeneracy at `A₀`.
-/

open Polynomial Matrix Module Filter Topology

namespace MorseFloer
namespace SignatureContinuity

open Chapter7 SymplecticEigen SpectralProjector EigenDecomp HermitianIndex

/-! ### Roots in a stable region: the count is locally constant -/

/-- **The number of eigenvalues in a region cannot jump.**  If the matrix `Γ x` depends
continuously on `x`, and the predicate `Pred` is constant on an `ε₀`-neighbourhood of each
eigenvalue of `Γ x₀`, then the number of eigenvalues of `Γ x` satisfying `Pred`, counted with
multiplicity, equals that of `Γ x₀` for `x` near `x₀`. -/
theorem eventually_countP_roots_charpoly {X : Type*} [TopologicalSpace X] {n : Type*}
    [Fintype n] [DecidableEq n] (Pred : ℂ → Prop) [DecidablePred Pred]
    {Γ : X → Matrix n n ℂ} {x₀ : X} (hΓ : ContinuousAt Γ x₀) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hstab : ∀ z ∈ (Γ x₀).charpoly.roots, ∀ w : ℂ, dist w z < ε₀ → (Pred w ↔ Pred z)) :
    ∀ᶠ x in 𝓝 x₀, (Γ x).charpoly.roots.countP Pred = (Γ x₀).charpoly.roots.countP Pred := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Fintype.card n = N := ⟨_, rfl⟩
  obtain ⟨δ, hδ, hδ'⟩ :=
    RootsContinuity.exists_delta_roots_close (n := N) (p := (Γ x₀).charpoly) hε₀
  have hcoef : ∀ᶠ x in 𝓝 x₀, ∀ i ∈ Finset.range (N + 1),
      ‖(Γ x).charpoly.coeff i - (Γ x₀).charpoly.coeff i‖ < δ := by
    rw [eventually_all_finset]
    intro i _
    have h : ContinuousAt (fun x => (Γ x).charpoly.coeff i) x₀ :=
      (continuous_charpoly_coeff (m := n) i).continuousAt.comp hΓ
    exact (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 h)).2 _ hδ
  filter_upwards [hcoef] with x hx
  have hclose : ∀ i, ‖(Γ x).charpoly.coeff i - (Γ x₀).charpoly.coeff i‖ < δ := by
    intro i
    by_cases hi : i ∈ Finset.range (N + 1)
    · exact hx i hi
    · rw [Finset.mem_range, not_lt] at hi
      rw [coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, hN]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, hN]; omega), sub_zero,
        norm_zero]
      exact hδ
  obtain ⟨a, b, ha, hb, hab⟩ := hδ' (Γ x).charpoly (charpoly_monic _)
    (by rw [charpoly_natDegree_eq_dim, hN]) hclose
  have hbmem : ∀ i, b i ∈ (Γ x₀).charpoly.roots := fun i => by
    rw [hb]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  rw [ha, hb, Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter, card_filter_map,
    card_filter_map]
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  exact hstab (b i) (hbmem i) (a i) (by rw [dist_eq_norm]; exact hab i)

/-- For an invertible Hermitian matrix, the half-plane `Re > 0` is stable around every
eigenvalue: they are real and nonzero. -/
theorem exists_stab_re {n : Type*} [Fintype n] [DecidableEq n] {Γ : Matrix n n ℂ}
    (hΓ : Γ.IsHermitian) (hdet : Γ.det ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ z ∈ Γ.charpoly.roots, ∀ w : ℂ, dist w z < ε₀ → (0 < w.re ↔ 0 < z.re) := by
  classical
  have hne : ∀ i, hΓ.eigenvalues i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hΓ.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  obtain ⟨ε₀, hε₀, hsep⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ i, ε₀ ≤ |hΓ.eigenvalues i| := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · set s : Finset ℝ := Finset.univ.image fun i => |hΓ.eigenvalues i| with hs
      have hsne : s.Nonempty := Finset.univ_nonempty.image _
      refine ⟨s.min' hsne, ?_, fun i => Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (Finset.min'_mem s hsne)
      rw [← hi]
      exact abs_pos.2 (hne i)
  refine ⟨ε₀, hε₀, fun z hz w hw => ?_⟩
  rw [hΓ.roots_charpoly_eq_eigenvalues] at hz
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
  have hz' : ((RCLike.ofReal ∘ hΓ.eigenvalues) i : ℂ).re = hΓ.eigenvalues i := by
    simp
  have h1 : |w.re - ((RCLike.ofReal ∘ hΓ.eigenvalues) i : ℂ).re| < ε₀ := by
    calc |w.re - ((RCLike.ofReal ∘ hΓ.eigenvalues) i : ℂ).re|
        = |(w - (RCLike.ofReal ∘ hΓ.eigenvalues) i).re| := by rw [Complex.sub_re]
      _ ≤ ‖w - (RCLike.ofReal ∘ hΓ.eigenvalues) i‖ := Complex.abs_re_le_norm _
      _ < ε₀ := by rwa [dist_eq_norm] at hw
  rw [hz'] at h1 ⊢
  have h2 := hsep i
  rw [abs_lt] at h1
  constructor
  · intro hw0
    by_contra hz0
    push Not at hz0
    rw [abs_of_nonpos hz0] at h2
    linarith
  · intro hz0
    rw [abs_of_pos hz0] at h2
    linarith

/-! ### The Hermitian form `G = -i H` -/

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The Hermitian form `G(X, Y) = -i ω(X, Ȳ)`; its diagonal is the quadratic form `Q` of
§7.3.a. -/
noncomputable def GForm (X Y : (l ⊕ l) → ℂ) : ℂ := -Complex.I * HForm X Y

theorem HForm_conj (X Y : (l ⊕ l) → ℂ) : starRingEnd ℂ (HForm X Y) = -HForm Y X := by
  rw [HForm, HForm, ← stdFormC_conjVec, conjVec_conjVec, stdFormC_skew]

theorem isHermForm_GForm : IsHermForm (GForm (l := l)) where
  add_left X Y Z := by rw [GForm, GForm, GForm, HForm_add_left]; ring
  smul_left a X Y := by rw [GForm, GForm, HForm_smul_left]; ring
  conj_symm X Y := by
    rw [GForm, GForm, map_mul, map_neg, Complex.conj_I, HForm_conj]
    ring

/-- The diagonal of `G` is `Q(X) = Im ω(X, X̄)`. -/
theorem GForm_self_re (X : (l ⊕ l) → ℂ) : (GForm X X).re = BForm X X := by
  have h := congrArg Complex.re (HForm_conj X X)
  rw [Complex.conj_re, Complex.neg_re] at h
  rw [GForm, BForm_eq_im, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im]
  linarith

omit [DecidableEq l] [Fintype l] in
theorem conjVec_eq_star (Y : (l ⊕ l) → ℂ) : conjVec Y = star Y := rfl

theorem GForm_eq (X Y : (l ⊕ l) → ℂ) :
    GForm X Y = -Complex.I * (X ⬝ᵥ (-(Matrix.J l ℂ)) *ᵥ star Y) := by
  rw [GForm, HForm, stdFormC_apply, conjVec_eq_star]

theorem continuous_GForm :
    Continuous fun p : ((l ⊕ l) → ℂ) × ((l ⊕ l) → ℂ) => GForm p.1 p.2 := by
  have e : (fun p : ((l ⊕ l) → ℂ) × ((l ⊕ l) → ℂ) => GForm p.1 p.2)
      = fun p => -Complex.I * (p.1 ⬝ᵥ (-(Matrix.J l ℂ)) *ᵥ star p.2) :=
    funext fun p => GForm_eq _ _
  rw [e]
  have h1 : Continuous fun p : ((l ⊕ l) → ℂ) × ((l ⊕ l) → ℂ) => star p.2 := continuous_snd.star
  have h2 : Continuous fun p : ((l ⊕ l) → ℂ) × ((l ⊕ l) → ℂ) => (-(Matrix.J l ℂ)) *ᵥ star p.2 :=
    continuous_const.matrix_mulVec h1
  have h3 : Continuous fun p : ((l ⊕ l) → ℂ) × ((l ⊕ l) → ℂ) =>
      p.1 ⬝ᵥ (-(Matrix.J l ℂ)) *ᵥ star p.2 := continuous_fst.dotProduct h2
  exact continuous_const.mul h3

theorem continuousAt_gForm {X : Type*} [TopologicalSpace X] {f g : X → ((l ⊕ l) → ℂ)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => GForm (f x) (g x)) x := by
  have e : (fun x => GForm (f x) (g x))
      = fun x => -Complex.I * (f x ⬝ᵥ (-(Matrix.J l ℂ)) *ᵥ star (g x)) :=
    funext fun x => GForm_eq _ _
  rw [e]
  have h1 : ContinuousAt (fun x => star (g x)) x := hg.star
  have h2 : ContinuousAt (fun x => (-(Matrix.J l ℂ)) *ᵥ star (g x)) x :=
    ((continuous_const.matrix_mulVec continuous_id).continuousAt).comp h1
  have h3 : ContinuousAt (fun x => f x ⬝ᵥ (-(Matrix.J l ℂ)) *ᵥ star (g x)) x :=
    (continuous_fst.dotProduct continuous_snd).continuousAt.comp (hf.prodMk h2)
  exact continuousAt_const.mul h3

theorem GForm_eq_zero_iff (X Y : (l ⊕ l) → ℂ) : GForm X Y = 0 ↔ HForm X Y = 0 := by
  rw [GForm, mul_eq_zero, neg_eq_zero]
  simp [Complex.I_ne_zero]

/-! ### The main theorem -/

variable (c : ℂ) (r : ℝ)

/-- The sum of the generalised eigenspaces of `A` for the eigenvalues in the disc `D(c, r)`. -/
noncomputable abbrev discSpace (A : Matrix (l ⊕ l) (l ⊕ l) ℂ) : Submodule ℂ ((l ⊕ l) → ℂ) :=
  kerAeval A (fPoly c r A)

/-- The complementary sum, for the eigenvalues outside the disc. -/
noncomputable abbrev outSpace (A : Matrix (l ⊕ l) (l ⊕ l) ℂ) : Submodule ℂ ((l ⊕ l) → ℂ) :=
  kerAeval A (gPoly c r A)

theorem discSpace_sup_outSpace (A : Matrix (l ⊕ l) (l ⊕ l) ℂ) :
    discSpace c r A ⊔ outSpace c r A = ⊤ :=
  kerAeval_fS_sup_not (fun z => dist z c < r) A

/-- **Local constancy of the signature.**  If `A₀` has no eigenvalue on the circle `|z - c| = r`
and `G` is nondegenerate on `V_{A₀}`, the positive index of `G` on `V_A` is constant for `A`
near `A₀`. -/
theorem eventually_posIndex_eq (A₀ : Matrix (l ⊕ l) (l ⊕ l) ℂ)
    (hcirc : ∀ z ∈ A₀.charpoly.roots, dist z c ≠ r)
    (hnd : ∀ v ∈ discSpace c r A₀, (∀ w ∈ discSpace c r A₀, GForm v w = 0) → v = 0) :
    ∀ᶠ A in 𝓝 A₀, posIndex GForm (discSpace c r A) = posIndex GForm (discSpace c r A₀) := by
  classical
  obtain ⟨U, P, hU, hPc, hP⟩ := exists_continuous_projector c r A₀ hcirc
  have hPA₀ : ContinuousAt P A₀ := hPc.continuousAt hU
  -- the algebra of the projector, on `U`
  have hrange : ∀ A ∈ U, ∀ x, P A *ᵥ x ∈ discSpace c r A := fun A hA x => by
    rw [mem_kerAeval, mulVec_mulVec, (hP A hA).2.2.1, zero_mulVec]
  have hrange' : ∀ A ∈ U, ∀ x, (1 - P A) *ᵥ x ∈ outSpace c r A := fun A hA x => by
    rw [mem_kerAeval, mulVec_mulVec, (hP A hA).2.2.2.1, zero_mulVec]
  have hfix : ∀ A ∈ U, ∀ x ∈ discSpace c r A, P A *ᵥ x = x := fun A hA x hx =>
    (hP A hA).2.2.2.2.1 x (mem_kerAeval.1 hx)
  have hkill : ∀ A ∈ U, ∀ x ∈ outSpace c r A, P A *ᵥ x = 0 := fun A hA x hx =>
    (hP A hA).2.2.2.2.2.1 x (mem_kerAeval.1 hx)
  have hinf : ∀ A ∈ U, discSpace c r A ⊓ outSpace c r A = ⊥ := fun A hA => by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    rw [Submodule.mem_bot, ← hfix A hA x hx.1, hkill A hA x hx.2]
  have hdim : ∀ A ∈ U, finrank ℂ (discSpace c r A) + finrank ℂ (outSpace c r A)
      = Fintype.card (l ⊕ l) := fun A hA => by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (discSpace c r A) (outSpace c r A)
    rw [hinf A hA, discSpace_sup_outSpace, finrank_bot, add_zero, finrank_top,
      Module.finrank_fintype_fun_eq_card] at h
    exact h.symm
  have hA₀U : A₀ ∈ U := mem_of_mem_nhds hU
  -- bases of the two spaces at `A₀`
  obtain ⟨e, he, heV⟩ := exists_basis_family (discSpace c r A₀)
  obtain ⟨e', he', he'V⟩ := exists_basis_family (outSpace c r A₀)
  have heV' : ∀ i, e i ∈ discSpace c r A₀ := fun i => heV ▸ Submodule.subset_span ⟨i, rfl⟩
  have he'V' : ∀ i, e' i ∈ outSpace c r A₀ := fun i => he'V ▸ Submodule.subset_span ⟨i, rfl⟩
  -- the transported families
  set b : Matrix (l ⊕ l) (l ⊕ l) ℂ → Fin (finrank ℂ (discSpace c r A₀)) → ((l ⊕ l) → ℂ) :=
    fun A i => P A *ᵥ e i with hb
  set b' : Matrix (l ⊕ l) (l ⊕ l) ℂ → Fin (finrank ℂ (outSpace c r A₀)) → ((l ⊕ l) → ℂ) :=
    fun A i => (1 - P A) *ᵥ e' i with hb'
  have hb₀ : b A₀ = e := funext fun i => hfix A₀ hA₀U _ (heV' i)
  have hb'₀ : b' A₀ = e' := funext fun i => by
    rw [hb']
    show (1 - P A₀) *ᵥ e' i = e' i
    rw [sub_mulVec, one_mulVec, hkill A₀ hA₀U _ (he'V' i), sub_zero]
  set bb : Matrix (l ⊕ l) (l ⊕ l) ℂ → (Fin (finrank ℂ (discSpace c r A₀))
      ⊕ Fin (finrank ℂ (outSpace c r A₀))) → ((l ⊕ l) → ℂ) := fun A => Sum.elim (b A) (b' A)
    with hbb
  have hbb₀ : LinearIndependent ℂ (bb A₀) := by
    rw [hbb]
    show LinearIndependent ℂ (Sum.elim (b A₀) (b' A₀))
    rw [hb₀, hb'₀]
    refine he.sum_type he' ?_
    rw [heV, he'V, disjoint_iff]
    exact hinf A₀ hA₀U
  have hbbc : ContinuousAt bb A₀ := by
    refine continuousAt_pi.2 fun i => ?_
    rcases i with i | i
    · exact ((continuous_id.matrix_mulVec continuous_const).continuousAt).comp hPA₀
    · exact ((continuous_id.matrix_mulVec continuous_const).continuousAt).comp
        (continuousAt_const.sub hPA₀)
  have hli : ∀ᶠ A in 𝓝 A₀, LinearIndependent ℂ (bb A) :=
    hbbc.preimage_mem_nhds (isOpen_setOfPred_linearIndependent.mem_nhds hbb₀)
  -- near `A₀` the transported family spans `V_A`
  have hspan : ∀ A ∈ U, LinearIndependent ℂ (bb A) →
      Submodule.span ℂ (Set.range (b A)) = discSpace c r A := fun A hA hAli => by
    have h1 : LinearIndependent ℂ (b A) := hAli.comp Sum.inl Sum.inl_injective
    have h2 : LinearIndependent ℂ (b' A) := hAli.comp Sum.inr Sum.inr_injective
    have hle1 : Submodule.span ℂ (Set.range (b A)) ≤ discSpace c r A :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hrange A hA _)
    have hle2 : Submodule.span ℂ (Set.range (b' A)) ≤ outSpace c r A :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hrange' A hA _)
    have hr1 := Submodule.finrank_mono hle1
    have hr2 := Submodule.finrank_mono hle2
    rw [finrank_span_eq_card h1, Fintype.card_fin] at hr1
    rw [finrank_span_eq_card h2, Fintype.card_fin] at hr2
    have hd := hdim A hA
    have hd₀ := hdim A₀ hA₀U
    refine Submodule.eq_of_le_of_finrank_eq hle1 ?_
    rw [finrank_span_eq_card h1, Fintype.card_fin]
    omega
  -- the Gram matrix and its eigenvalues
  have hgram : ContinuousAt (fun A => gram GForm (b A)) A₀ := by
    refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
    show ContinuousAt (fun A => GForm (P A *ᵥ e j) (P A *ᵥ e i)) A₀
    have h1 : ContinuousAt (fun A => P A *ᵥ e j) A₀ :=
      ((continuous_id.matrix_mulVec continuous_const).continuousAt).comp hPA₀
    have h2 : ContinuousAt (fun A => P A *ᵥ e i) A₀ :=
      ((continuous_id.matrix_mulVec continuous_const).continuousAt).comp hPA₀
    exact continuousAt_gForm h1 h2
  have hdet : (gram GForm (b A₀)).det ≠ 0 := by
    rw [hb₀]
    exact det_gram_ne_zero isHermForm_GForm he heV hnd
  obtain ⟨ε₀, hε₀, hstab⟩ := exists_stab_re (isHermitian_gram isHermForm_GForm (b A₀)) hdet
  have hcount := eventually_countP_roots_charpoly (fun z : ℂ => 0 < z.re) hgram hε₀ hstab
  filter_upwards [hU, hli, hcount] with A hAU hAli hAcount
  have h1 : LinearIndependent ℂ (b A) := hAli.comp Sum.inl Sum.inl_injective
  rw [posIndex_eq_countP isHermForm_GForm h1 (hspan A hAU hAli),
    posIndex_eq_countP isHermForm_GForm he heV, hAcount, hb₀]

end SignatureContinuity
end MorseFloer
