import MorseFloer.Part2.SignatureContinuity
import MorseFloer.Part2.EigenMult

/-!
# The map `ρ : Sp(2n) → S¹` of Theorem 7.1.3: definition and continuity

This file constructs the map `ρ` of §7.3.b and proves that it is continuous on the symplectic
group (§7.3.c, Corollary 7.3.9 and Proposition 7.3.10).

`ρ(A)` is a product over the distinct eigenvalues `μ` of `A` of a factor depending on `μ` and
on the spectral data of `A` at `μ` (`factor`): `μ^{σ(μ)}` when `μ` is on the unit circle with
positive imaginary part, where `σ(μ) = 2 m₊(μ) - m(μ)` is the signature of the form `Q` on the
generalised eigenspace `E_μ` (`sigma`, with `m₊` the positive index of
`Part2/HermitianIndex.lean`); `(-1)^{m(-1)/2}` at `μ = -1`; `(-1)^{m(μ)}` for a real `μ` in
`(-1, 0)`; and `1` otherwise.  For a symplectic `A` the negative real eigenvalues other than `-1`
come in pairs `μ, 1/μ`, so this is the book's `(-1)^{m₀/2} ∏ λ^{σ(λ)}` of Proposition 7.3.5.

Continuity is proved at each `A₀` by localising at the eigenvalues of `A₀`: for small `r` the
discs `D(λ, r)` about the distinct eigenvalues `λ` of `A₀` are disjoint and, for `A` near `A₀`,
contain all the eigenvalues of `A` (`Part2/RootsContinuity.lean`), so `ρ(A)` is the product of
the local products over the discs (`rhoC_eq_prod_localProd`), and it suffices to show that each
local product tends to the factor of `λ` (`tendsto_localProd`).  There are four cases.  If `λ`
is neither on the circle nor real in `[-1, 0]`, and is not `1`, the local product is `1`.  If
`λ ∈ (-1, 0)`, it is `(-1)` to the number of real eigenvalues in the disc, which has the parity
of the number of all eigenvalues in the disc, the non-real ones coming in conjugate pairs; that
number is the multiplicity of `λ`.  If `λ` is on the circle, the local product is
`∏ μ^{σ(μ)}` over the circle eigenvalues in the disc, and since those `μ` tend to `λ` it
suffices to know `∑ σ(μ) = σ(λ)` (`eventually_sum_sigma`): the sum of the generalised
eigenspaces over the disc carries the signature `∑ σ(μ)`, the eigenvalues off the circle
contributing nothing (they pair into hyperbolic planes, Corollary 7.3.4), and that signature is
locally constant (`Part2/SignatureContinuity.lean`).  Finally at `λ = -1` the local product is
`(-1)^{m(-1)/2 + p} ∏ μ^{σ(μ)}` with `p` the number of eigenvalues in `(-1, 0)` in the disc,
and the exponent has the right parity by counting the eigenvalues in the disc along their
orbits under conjugation and inversion (Proposition 7.3.10).
-/

open Polynomial Matrix Module Filter Topology

namespace MorseFloer
namespace Rho

open Chapter7 SymplecticEigen SymplecticSpectrum SpectralProjector EigenDecomp EigenMult
  HermitianIndex SignatureContinuity

/-! ### Elementary estimates -/

theorem norm_prod_sub_one_le {ι : Type*} (s : Finset ι) (x : ι → ℂ) {δ : ℝ}
    (hx : ∀ i ∈ s, ‖x i‖ ≤ 1) (h1 : ∀ i ∈ s, ‖x i - 1‖ ≤ δ) :
    ‖∏ i ∈ s, x i - 1‖ ≤ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hxa := hx a (Finset.mem_insert_self a s)
    have h1a := h1 a (Finset.mem_insert_self a s)
    calc ‖x a * ∏ i ∈ s, x i - 1‖ = ‖x a * (∏ i ∈ s, x i - 1) + (x a - 1)‖ := by congr 1; ring
      _ ≤ ‖x a * (∏ i ∈ s, x i - 1)‖ + ‖x a - 1‖ := norm_add_le _ _
      _ ≤ 1 * (s.card * δ) + δ := by
          rw [norm_mul]
          gcongr
      _ = ((s.card + 1 : ℕ) : ℝ) * δ := by push_cast; ring

theorem norm_zpow_sub_one_le {z : ℂ} (hz : ‖z‖ = 1) (n : ℤ) :
    ‖z ^ n - 1‖ ≤ (n.natAbs : ℝ) * ‖z - 1‖ := by
  have hnat : ∀ k : ℕ, ‖z ^ k - 1‖ ≤ (k : ℝ) * ‖z - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc ‖z ^ (k + 1) - 1‖ = ‖z ^ k * (z - 1) + (z ^ k - 1)‖ := by congr 1; ring
        _ ≤ ‖z ^ k * (z - 1)‖ + ‖z ^ k - 1‖ := norm_add_le _ _
        _ ≤ 1 * ‖z - 1‖ + k * ‖z - 1‖ := by
            rw [norm_mul, norm_pow, hz, one_pow]
            gcongr
        _ = ((k + 1 : ℕ) : ℝ) * ‖z - 1‖ := by push_cast; ring
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k ∨ n = -k := ⟨n.natAbs, Int.natAbs_eq n⟩
  rcases hk with rfl | rfl
  · rw [Int.natAbs_natCast, zpow_natCast]
    exact hnat k
  · rw [Int.natAbs_neg, Int.natAbs_natCast, _root_.zpow_neg, zpow_natCast]
    have hzk : ‖z ^ k‖ = 1 := by rw [norm_pow, hz, one_pow]
    have hne : z ^ k ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hzk
      exact zero_ne_one hzk
    calc ‖(z ^ k)⁻¹ - 1‖ = ‖(z ^ k)⁻¹ * (1 - z ^ k)‖ := by
          rw [mul_sub, inv_mul_cancel₀ hne, mul_one]
      _ = ‖z ^ k - 1‖ := by rw [norm_mul, norm_inv, hzk, inv_one, one_mul, norm_sub_rev]
      _ ≤ k * ‖z - 1‖ := hnat k

theorem prod_zpow_eq {ι : Type*} (s : Finset ι) (e : ι → ℤ) {c₀ : ℂ} (hc₀ : c₀ ≠ 0)
    (μ : ι → ℂ) :
    ∏ i ∈ s, μ i ^ e i = c₀ ^ (∑ i ∈ s, e i) * ∏ i ∈ s, (μ i / c₀) ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hc₀,
      div_zpow]
    have := zpow_ne_zero (e a) hc₀
    field_simp

/-- **Products of unit complex numbers close to `c₀`.**  If the finsets `s x` of unit complex
numbers have at most `N` elements, all within `ε` of `c₀` for `x` far enough along the filter
(for every `ε`), with integer exponents bounded by `N`, and the prefactor `g x` has norm at most
`1`, then `g x ∏ μ^{e μ}` tends to the limit of `g x c₀^{∑ e μ}`, as soon as the latter is
eventually constant. -/
theorem tendsto_prod_zpow {X : Type*} {F : Filter X} (N : ℕ) {c₀ : ℂ} (hc₀ : ‖c₀‖ = 1)
    (g : X → ℂ) (s : X → Finset ℂ) (e : X → ℂ → ℤ) (hg : ∀ x, ‖g x‖ ≤ 1)
    (hcard : ∀ x, (s x).card ≤ N) (he : ∀ x, ∀ μ ∈ s x, (e x μ).natAbs ≤ N)
    (hunit : ∀ x, ∀ μ ∈ s x, ‖μ‖ = 1)
    (hclose : ∀ ε > 0, ∀ᶠ x in F, ∀ μ ∈ s x, ‖μ - c₀‖ < ε) {c : ℂ}
    (hsum : ∀ᶠ x in F, g x * c₀ ^ (∑ μ ∈ s x, e x μ) = c) :
    Tendsto (fun x => g x * ∏ μ ∈ s x, μ ^ e x μ) F (𝓝 c) := by
  have hc₀' : c₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc₀
    exact zero_ne_one hc₀
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hε : 0 < δ / (N * N + 1) := by positivity
  filter_upwards [hclose _ hε, hsum] with x h1 h2
  rw [dist_eq_norm, prod_zpow_eq (s x) (e x) hc₀', ← mul_assoc, h2]
  have hc : ‖c‖ ≤ 1 := by
    rw [← h2, norm_mul, norm_zpow, hc₀, _root_.one_zpow, mul_one]
    exact hg x
  have hbound : ‖∏ μ ∈ s x, (μ / c₀) ^ e x μ - 1‖ ≤ (s x).card * (N * (δ / (N * N + 1))) := by
    refine norm_prod_sub_one_le _ _ (fun μ hμ => ?_) (fun μ hμ => ?_)
    · rw [norm_zpow, norm_div, hunit x μ hμ, hc₀, div_one, _root_.one_zpow]
    · have hq : ‖μ / c₀‖ = 1 := by rw [norm_div, hunit x μ hμ, hc₀, div_one]
      refine (norm_zpow_sub_one_le hq _).trans ?_
      have h3 : ‖μ / c₀ - 1‖ = ‖μ - c₀‖ := by
        have : μ / c₀ - 1 = (μ - c₀) / c₀ := by field_simp
        rw [this, norm_div, hc₀, div_one]
      rw [h3]
      exact mul_le_mul (by exact_mod_cast he x μ hμ) (h1 μ hμ).le (norm_nonneg _)
        (by positivity)
  calc ‖c * ∏ μ ∈ s x, (μ / c₀) ^ e x μ - c‖
      = ‖c‖ * ‖∏ μ ∈ s x, (μ / c₀) ^ e x μ - 1‖ := by rw [← norm_mul, mul_sub, mul_one]
    _ ≤ 1 * (N * (N * (δ / (N * N + 1)))) := by
        gcongr
        exact hbound.trans (by gcongr; exact_mod_cast hcard x)
    _ < δ := by
        rw [one_mul]
        have h4 : (N : ℝ) * (N * (δ / (N * N + 1))) = δ * (N * N / (N * N + 1)) := by ring
        rw [h4]
        exact mul_lt_of_lt_one_right hδ ((div_lt_one (by positivity)).2 (by linarith))

/-- A strict sign is preserved by a perturbation smaller than the absolute value. -/
theorem sign_stable {a b ε : ℝ} (h : |a - b| < ε) (hε : ε ≤ |b|) : (0 < a ↔ 0 < b) ∧ a ≠ 0 := by
  rw [abs_lt] at h
  rcases lt_or_gt_of_ne (show b ≠ 0 by intro hb; rw [hb, abs_zero] at hε; linarith) with hb | hb
  · rw [abs_of_neg hb] at hε
    exact ⟨⟨fun h1 => by linarith, fun h1 => by linarith⟩, by intro h1; linarith⟩
  · rw [abs_of_pos hb] at hε
    exact ⟨⟨fun _ => hb, fun _ => by linarith⟩, by intro h1; linarith⟩

/-! ### The eigenvalues near an eigenvalue of `A₀` -/

section Cluster

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Near `A₀`, the eigenvalues of `A` can be enumerated within `ε` of those of `A₀`. -/
theorem eventually_enum (A₀ : Matrix n n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ A in 𝓝 A₀, ∃ a b : Fin (Fintype.card n) → ℂ,
      A.charpoly.roots = Finset.univ.val.map a ∧ A₀.charpoly.roots = Finset.univ.val.map b ∧
      ∀ i, dist (a i) (b i) < ε := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Fintype.card n = N := ⟨_, rfl⟩
  obtain ⟨δ, hδ, hδ'⟩ :=
    RootsContinuity.exists_delta_roots_close (n := N) (p := A₀.charpoly) hε
  have hcoef : ∀ᶠ A in 𝓝 A₀, ∀ i ∈ Finset.range (N + 1),
      ‖A.charpoly.coeff i - A₀.charpoly.coeff i‖ < δ := by
    rw [eventually_all_finset]
    intro i _
    have h := (continuous_charpoly_coeff (m := n) i).continuousAt (x := A₀)
    exact (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 h)).2 _ hδ
  filter_upwards [hcoef] with A hA
  have hclose : ∀ i, ‖A.charpoly.coeff i - A₀.charpoly.coeff i‖ < δ := by
    intro i
    by_cases hi : i ∈ Finset.range (N + 1)
    · exact hA i hi
    · rw [Finset.mem_range, not_lt] at hi
      rw [coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, hN]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, hN]; omega), sub_zero,
        norm_zero]
      exact hδ
  obtain ⟨a, b, ha, hb, hab⟩ := hδ' A.charpoly (charpoly_monic A)
    (by rw [charpoly_natDegree_eq_dim, hN]) hclose
  subst hN
  exact ⟨a, b, ha, hb, fun i => by rw [dist_eq_norm]; exact hab i⟩

/-- Every eigenvalue of `A` near `A₀` is within `ε` of an eigenvalue of `A₀`. -/
theorem eventually_roots_near (A₀ : Matrix n n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ A in 𝓝 A₀, ∀ z ∈ A.charpoly.roots, ∃ w ∈ A₀.charpoly.roots, dist z w < ε := by
  filter_upwards [eventually_enum A₀ hε] with A hA
  obtain ⟨a, b, ha, hb, hab⟩ := hA
  intro z hz
  rw [ha] at hz
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
  exact ⟨b i, by rw [hb]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i), hab i⟩

/-- **The cluster of eigenvalues at `c₀`.**  If the other eigenvalues of `A₀` are at distance
at least `3r` from `c₀`, then for `A` near `A₀` the eigenvalues of `A` in `D(c₀, r)` are within
`ε` of `c₀`, there are as many of them as the multiplicity of `c₀`, and none is on the
circle. -/
theorem eventually_cluster (A₀ : Matrix n n ℂ) (c₀ : ℂ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ z ∈ A₀.charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀) {ε : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ r) :
    ∀ᶠ A in 𝓝 A₀, (∀ z ∈ A.charpoly.roots, dist z c₀ < r → dist z c₀ < ε) ∧
      (A.charpoly.roots.countP fun z => dist z c₀ < r) = A₀.charpoly.roots.count c₀ ∧
      ∀ z ∈ A.charpoly.roots, dist z c₀ ≠ r := by
  classical
  filter_upwards [eventually_enum A₀ hε] with A hA
  obtain ⟨a, b, ha, hb, hab⟩ := hA
  have hbmem : ∀ i, b i ∈ A₀.charpoly.roots := fun i => by
    rw [hb]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  have key : ∀ i, dist (a i) c₀ < r ↔ b i = c₀ := by
    intro i
    constructor
    · intro h
      by_contra hne
      have h1 := hsep (b i) (hbmem i) hne
      have h2 := dist_triangle (b i) (a i) c₀
      rw [dist_comm (b i) (a i)] at h2
      linarith [hab i]
    · intro h
      have h3 : dist (b i) c₀ = 0 := by rw [h, dist_self]
      linarith [dist_triangle (a i) (b i) c₀, hab i]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz hzr
    rw [ha] at hz
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    have h3 : dist (b i) c₀ = 0 := by rw [(key i).1 hzr, dist_self]
    linarith [dist_triangle (a i) (b i) c₀, hab i]
  · rw [ha, hb, Multiset.countP_eq_card_filter, Multiset.count_eq_card_filter_eq,
      card_filter_map, card_filter_map]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    rw [key i, eq_comm]
  · intro z hz h
    rw [ha] at hz
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    by_cases hbi : b i = c₀
    · have h3 : dist (b i) c₀ = 0 := by rw [hbi, dist_self]
      linarith [dist_triangle (a i) (b i) c₀, hab i]
    · have h1 := hsep (b i) (hbmem i) hbi
      have h2 := dist_triangle (b i) (a i) c₀
      rw [dist_comm (b i) (a i)] at h2
      linarith [hab i]

end Cluster

/-! ### The definition of `ρ` -/

variable {l : Type*} [DecidableEq l] [Fintype l]

omit [DecidableEq l] [Fintype l] in
theorem continuous_cpx :
    Continuous (cpx : Matrix (l ⊕ l) (l ⊕ l) ℝ → Matrix (l ⊕ l) (l ⊕ l) ℂ) :=
  continuous_id.matrix_map Complex.continuous_ofReal

/-- `m₊(μ)`: the positive index of `Q` on the generalised eigenspace `E_μ`. -/
noncomputable def mPos (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) : ℕ := posIndex GForm (E M μ)

open Classical in
/-- The signature `σ(μ) = m₊(μ) - m₋(μ) = 2 m₊(μ) - m(μ)` of the eigenvalue `μ`. -/
noncomputable def sigma (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) : ℤ :=
  2 * (mPos M μ : ℤ) - (M.charpoly.roots.count μ : ℤ)

open Classical in
/-- The factor of the eigenvalue `μ` in `ρ`: `μ^{σ(μ)}` on the upper half of the unit circle,
`(-1)^{m(-1)/2}` at `-1`, `(-1)^{m(μ)}` on `(-1, 0)`, and `1` elsewhere. -/
noncomputable def factor (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) : ℂ :=
  if ‖μ‖ = 1 ∧ 0 < μ.im then μ ^ sigma M μ
  else if μ = -1 then (-1) ^ (M.charpoly.roots.count μ / 2)
  else if μ.im = 0 ∧ -1 < μ.re ∧ μ.re < 0 then (-1) ^ M.charpoly.roots.count μ
  else 1

open Classical in
/-- `ρ` of a complex matrix: the product of the factors of its distinct eigenvalues. -/
noncomputable def rhoC (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) : ℂ :=
  ∏ μ ∈ M.charpoly.roots.toFinset, factor M μ

/-- **The map `ρ` of Theorem 7.1.3**, on real `2n × 2n` matrices. -/
noncomputable def rho (n : ℕ) (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) : ℂ :=
  rhoC (cpx A)

open Classical in
theorem factor_of_circle {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} (h : ‖μ‖ = 1 ∧ 0 < μ.im) :
    factor M μ = μ ^ sigma M μ := by
  rw [factor, ite_eq_left h]

open Classical in
theorem factor_neg_one (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) :
    factor M (-1) = (-1) ^ (M.charpoly.roots.count (-1) / 2) := by
  rw [factor, ite_eq_right (by simp), ite_eq_left rfl]

open Classical in
theorem factor_of_real {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} (h1 : ¬(‖μ‖ = 1 ∧ 0 < μ.im))
    (h2 : μ ≠ -1) (h3 : μ.im = 0 ∧ -1 < μ.re ∧ μ.re < 0) :
    factor M μ = (-1) ^ M.charpoly.roots.count μ := by
  rw [factor, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]

open Classical in
theorem factor_eq_one {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} (h1 : ¬(‖μ‖ = 1 ∧ 0 < μ.im))
    (h2 : μ ≠ -1) (h3 : ¬(μ.im = 0 ∧ -1 < μ.re ∧ μ.re < 0)) : factor M μ = 1 := by
  rw [factor, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

open Classical in
theorem natAbs_sigma_le (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) :
    (sigma M μ).natAbs ≤ M.charpoly.roots.count μ := by
  have hp : mPos M μ ≤ M.charpoly.roots.count μ := by
    rw [mPos, ← finrank_E]
    exact posIndex_le_finrank _ _
  unfold sigma
  omega

theorem card_roots_eq (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) :
    Multiset.card M.charpoly.roots = Fintype.card (l ⊕ l) := by
  rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim]

open Classical in
theorem count_le_card (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (μ : ℂ) :
    M.charpoly.roots.count μ ≤ Fintype.card (l ⊕ l) :=
  (Multiset.count_le_card _ _).trans (card_roots_eq M).le

open Classical in
theorem card_toFinset_le (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) :
    M.charpoly.roots.toFinset.card ≤ Fintype.card (l ⊕ l) :=
  (Multiset.toFinset_card_le _).trans (card_roots_eq M).le

/-! ### Localisation at the eigenvalues of `A₀` -/

open Classical in
/-- The distinct eigenvalues of `M` in the disc `D(c₀, r)`. -/
noncomputable def discRoots (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (c₀ : ℂ) (r : ℝ) : Finset ℂ :=
  M.charpoly.roots.toFinset.filter fun z => dist z c₀ < r

open Classical in
/-- The local product: the factors of the eigenvalues in the disc. -/
noncomputable def localProd (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (c₀ : ℂ) (r : ℝ) : ℂ :=
  ∏ μ ∈ discRoots M c₀ r, factor M μ

open Classical in
theorem mem_discRoots {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {c₀ : ℂ} {r : ℝ} {z : ℂ} :
    z ∈ discRoots M c₀ r ↔ z ∈ M.charpoly.roots ∧ dist z c₀ < r := by
  rw [discRoots, Finset.mem_filter, Multiset.mem_toFinset]

open Classical in
/-- **`ρ` is the product of the local products** over a family of disjoint discs covering the
spectrum. -/
theorem rhoC_eq_prod_localProd (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (R : Finset ℂ) (r : ℝ)
    (hcover : ∀ z ∈ M.charpoly.roots, ∃ c ∈ R, dist z c < r)
    (hdisj : ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' → 2 * r ≤ dist c c') :
    rhoC M = ∏ c ∈ R, localProd M c r := by
  have e : M.charpoly.roots.toFinset = R.biUnion fun c => discRoots M c r := by
    ext z
    simp only [Finset.mem_biUnion, mem_discRoots, Multiset.mem_toFinset]
    constructor
    · intro hz
      obtain ⟨c, hc, h⟩ := hcover z hz
      exact ⟨c, hc, hz, h⟩
    · rintro ⟨c, -, hz, -⟩
      exact hz
  rw [rhoC, e, Finset.prod_biUnion]
  · rfl
  intro c hc c' hc' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro z hz hz'
  rw [mem_discRoots] at hz hz'
  have := dist_triangle c z c'
  rw [dist_comm c z] at this
  linarith [hdisj c hc c' hc' hne, hz.2, hz'.2]

open Classical in
/-- At `A₀` itself, the disc about `c₀` contains only `c₀`. -/
theorem localProd_self {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {c₀ : ℂ} (hc₀ : c₀ ∈ M.charpoly.roots)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ z ∈ M.charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀) :
    localProd M c₀ r = factor M c₀ := by
  have e : discRoots M c₀ r = {c₀} := by
    ext z
    rw [mem_discRoots, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hzr⟩
      by_contra hne
      have := hsep z hz hne
      linarith
    · intro hz
      rw [hz]
      exact ⟨hc₀, by rw [dist_self]; exact hr⟩
  rw [localProd, e, Finset.prod_singleton]

/-- The radius below which the disc about `λ` stays on one side of the real axis, of the unit
circle, of the imaginary axis and of the line `Re = -1`, whenever `λ` is not on them. -/
noncomputable def radiusBound (μ : ℂ) : ℝ :=
  min (1 / 4) (min (if μ.im = 0 then 1 else |μ.im|)
    (min (if ‖μ‖ = 1 then 1 else |‖μ‖ - 1|)
      (min (if μ.re = 0 then 1 else |μ.re|) (if μ.re = -1 then 1 else |μ.re + 1|))))

theorem radiusBound_pos (μ : ℂ) : 0 < radiusBound μ := by
  unfold radiusBound
  refine lt_min (by norm_num) (lt_min ?_ (lt_min ?_ (lt_min ?_ ?_)))
  · split_ifs with h
    · exact one_pos
    · exact abs_pos.2 h
  · split_ifs with h
    · exact one_pos
    · exact abs_pos.2 (sub_ne_zero.2 h)
  · split_ifs with h
    · exact one_pos
    · exact abs_pos.2 h
  · split_ifs with h
    · exact one_pos
    · exact abs_pos.2 (by intro h'; exact h (by linear_combination h'))

section Geometry

variable {c₀ : ℂ} {r : ℝ} (hrb : r ≤ radiusBound c₀)
include hrb

theorem radius_le_quarter : r ≤ 1 / 4 :=
  hrb.trans (min_le_left _ _)

theorem disc_im (hc : c₀.im ≠ 0) {z : ℂ} (hz : dist z c₀ < r) :
    (0 < z.im ↔ 0 < c₀.im) ∧ z.im ≠ 0 := by
  have h1 : r ≤ |c₀.im| := by
    have := hrb.trans ((min_le_right _ _).trans (min_le_left _ _))
    rwa [ite_eq_right hc] at this
  refine sign_stable ?_ h1
  calc |z.im - c₀.im| = |(z - c₀).im| := by rw [Complex.sub_im]
    _ ≤ ‖z - c₀‖ := Complex.abs_im_le_norm _
    _ < r := by rwa [dist_eq_norm] at hz

theorem disc_norm (hc : ‖c₀‖ ≠ 1) {z : ℂ} (hz : dist z c₀ < r) :
    (0 < ‖z‖ - 1 ↔ 0 < ‖c₀‖ - 1) ∧ ‖z‖ ≠ 1 := by
  have h1 : r ≤ |‖c₀‖ - 1| := by
    have := hrb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rwa [ite_eq_right hc] at this
  have h := sign_stable (a := ‖z‖ - 1) (b := ‖c₀‖ - 1) ?_ h1
  · exact ⟨h.1, fun h2 => h.2 (by rw [h2, sub_self])⟩
  · calc |‖z‖ - 1 - (‖c₀‖ - 1)| = |‖z‖ - ‖c₀‖| := by ring_nf
      _ ≤ ‖z - c₀‖ := abs_norm_sub_norm_le _ _
      _ < r := by rwa [dist_eq_norm] at hz

theorem disc_re (hc : c₀.re ≠ 0) {z : ℂ} (hz : dist z c₀ < r) :
    (0 < z.re ↔ 0 < c₀.re) ∧ z.re ≠ 0 := by
  have h1 : r ≤ |c₀.re| := by
    have := hrb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
    rwa [ite_eq_right hc] at this
  refine sign_stable ?_ h1
  calc |z.re - c₀.re| = |(z - c₀).re| := by rw [Complex.sub_re]
    _ ≤ ‖z - c₀‖ := Complex.abs_re_le_norm _
    _ < r := by rwa [dist_eq_norm] at hz

theorem disc_re_add_one (hc : c₀.re ≠ -1) {z : ℂ} (hz : dist z c₀ < r) :
    (-1 < z.re ↔ -1 < c₀.re) ∧ z.re ≠ -1 := by
  have h1 : r ≤ |c₀.re + 1| := by
    have := hrb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
    rwa [ite_eq_right hc] at this
  have h := sign_stable (a := z.re + 1) (b := c₀.re + 1) ?_ h1
  · refine ⟨?_, fun h2 => h.2 (by rw [h2]; ring)⟩
    have h3 := h.1
    constructor
    · intro hh
      have := h3.1 (by linarith)
      linarith
    · intro hh
      have := h3.2 (by linarith)
      linarith
  · calc |z.re + 1 - (c₀.re + 1)| = |(z - c₀).re| := by rw [Complex.sub_re]; ring_nf
      _ ≤ ‖z - c₀‖ := Complex.abs_re_le_norm _
      _ < r := by rwa [dist_eq_norm] at hz

theorem disc_re_neg_of_neg_one (hc : c₀ = -1) {z : ℂ} (hz : dist z c₀ < r) : z.re < 0 := by
  have h4 := radius_le_quarter hrb
  have : |(z - c₀).re| < 1 / 4 := lt_of_le_of_lt (Complex.abs_re_le_norm _)
    (by rw [← dist_eq_norm]; linarith)
  rw [Complex.sub_re, hc, abs_lt] at this
  simp only [Complex.neg_re, Complex.one_re] at this
  linarith [this.2]

end Geometry

/-! ### The trivial case and the real case -/

open Classical in
theorem localProd_eq_one {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {c₀ : ℂ} {r : ℝ}
    (hD : ∀ z, dist z c₀ < r → ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ z ≠ -1 ∧
      ¬(z.im = 0 ∧ -1 < z.re ∧ z.re < 0)) :
    localProd M c₀ r = 1 := by
  refine Finset.prod_eq_one fun μ hμ => ?_
  obtain ⟨h1, h2, h3⟩ := hD μ (mem_discRoots.1 hμ).2
  exact factor_eq_one h1 h2 h3

open Classical in
/-- A product of `(-1)^{m(μ)}` over the distinct eigenvalues satisfying `P` is `(-1)` to the
number of eigenvalues satisfying `P`, with multiplicity. -/
theorem prod_neg_one_pow_count (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (P : ℂ → Prop)
    [DecidablePred P] :
    ∏ μ ∈ M.charpoly.roots.toFinset.filter P, (-1 : ℂ) ^ M.charpoly.roots.count μ
      = (-1) ^ Multiset.card (M.charpoly.roots.filter P) := by
  rw [Finset.prod_pow_eq_pow_sum, ← Multiset.toFinset_filter, ← Multiset.toFinset_sum_count_eq]
  congr 1
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Multiset.mem_toFinset, Multiset.mem_filter] at hμ
  rw [Multiset.count_filter_of_pos hμ.2]

/-- Splitting a count along a dichotomy. -/
theorem card_filter_eq_add (s : Multiset ℂ) (P Q R : ℂ → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred R] (h1 : ∀ z ∈ s, P z ↔ Q z ∨ R z)
    (h2 : ∀ z ∈ s, ¬(Q z ∧ R z)) :
    Multiset.card (s.filter P) = Multiset.card (s.filter Q) + Multiset.card (s.filter R) := by
  rw [← Multiset.card_add, Multiset.filter_add_filter, Multiset.filter_eq_nil.2 h2, add_zero]
  congr 1
  exact Multiset.filter_congr h1

open Classical in
/-- The number of eigenvalues satisfying `P`, with multiplicity, as a sum over the distinct
ones. -/
theorem sum_count_filter (s : Multiset ℂ) (P : ℂ → Prop) [DecidablePred P] :
    ∑ μ ∈ s.toFinset.filter P, s.count μ = Multiset.card (s.filter P) := by
  rw [← Multiset.toFinset_filter, ← Multiset.toFinset_sum_count_eq]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Multiset.mem_toFinset, Multiset.mem_filter] at hμ
  rw [Multiset.count_filter_of_pos hμ.2]

theorem neg_one_zpow_eq_of_even {x y : ℤ} (h : Even (x - y)) : (-1 : ℂ) ^ x = (-1) ^ y := by
  have e : x = y + (x - y) := by ring
  rw [e, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), h.neg_one_zpow, mul_one]

/-- The eventual facts about the eigenvalues of a nearby symplectic matrix in the disc. -/
theorem eventually_facts {A₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ} (c₀ : ℂ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ z ∈ (cpx A₀).charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀) {ε : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ r) :
    ∀ᶠ A in 𝓝[Matrix.symplecticGroup l ℝ] A₀, A ∈ Matrix.symplecticGroup l ℝ ∧
      (∀ z ∈ (cpx A).charpoly.roots, dist z c₀ < r → dist z c₀ < ε) ∧
      ((cpx A).charpoly.roots.countP fun z => dist z c₀ < r) = (cpx A₀).charpoly.roots.count c₀ ∧
      ∀ z ∈ (cpx A).charpoly.roots, dist z c₀ ≠ r := by
  have h := (continuous_cpx.tendsto A₀).eventually (eventually_cluster (cpx A₀) c₀ hr hsep hε hεr)
  filter_upwards [self_mem_nhdsWithin, h.filter_mono nhdsWithin_le_nhds] with A hA h'
  exact ⟨hA, h'⟩

/-- **Stability of the disc under `μ ↦ 1/μ̄`** for the eigenvalues near a point of the unit
circle. -/
theorem stab_of_close {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    {c₀ : ℂ} (hc₀ : ‖c₀‖ = 1) {r : ℝ} (hr4 : r ≤ 1 / 4)
    (hclose : ∀ z ∈ (cpx A).charpoly.roots, dist z c₀ < r → dist z c₀ < r / 2) :
    ∀ z ∈ (cpx A).charpoly.roots, dist z c₀ < r → dist (starRingEnd ℂ z)⁻¹ c₀ < r := by
  intro z hz hzr
  have hz0 : z ≠ 0 := fun h0 => zero_notMem_roots hA (h0 ▸ hz)
  have h1 := hclose z hz hzr
  rw [dist_eq_norm] at h1 ⊢
  rw [norm_inv_conj_sub hc₀ hz0, div_lt_iff₀ (norm_pos_iff.2 hz0)]
  have h2 : 1 - r / 2 ≤ ‖z‖ := by
    have := norm_sub_norm_le z c₀
    rw [hc₀] at this
    have h3 := abs_le.1 (abs_norm_sub_norm_le z c₀)
    linarith [this, h3.1, norm_sub_rev z c₀]
  have hr0 : 0 < r := by linarith [norm_nonneg (z - c₀)]
  nlinarith

/-- **The real case, Proposition 7.3.10 for `λ ∈ (-1, 0)`.**  In a disc about a negative real
`c₀ ∈ (-1, 0)` meeting neither the circle nor `-1`, the local product is `(-1)` to the number
of eigenvalues in the disc, which is the multiplicity of `c₀`. -/
theorem eventually_localProd_eq_of_real {A₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ} {c₀ : ℂ}
    (hc₀' : c₀.im = 0 ∧ -1 < c₀.re ∧ c₀.re < 0) {r : ℝ}
    (hr : 0 < r) (hsep : ∀ z ∈ (cpx A₀).charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀)
    (hD : ∀ z, dist z c₀ < r → ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ z ≠ -1 ∧
      (z.im = 0 → -1 < z.re ∧ z.re < 0)) :
    ∀ᶠ A in 𝓝[Matrix.symplecticGroup l ℝ] A₀, localProd (cpx A) c₀ r = factor (cpx A₀) c₀ := by
  classical
  filter_upwards [eventually_facts c₀ hr hsep hr le_rfl] with A hA
  obtain ⟨-, -, hcount, -⟩ := hA
  set M := cpx A with hM
  have hconj : ∀ z : ℂ, dist (starRingEnd ℂ z) c₀ < r ↔ dist z c₀ < r := by
    intro z
    have e : c₀ = starRingEnd ℂ c₀ := (Complex.conj_eq_iff_im.2 hc₀'.1).symm
    conv_lhs => rw [e]
    rw [Complex.dist_conj_conj]
  -- the local product is `(-1)` to the number of real eigenvalues in the disc
  have h1 : localProd M c₀ r
      = (-1) ^ Multiset.card (M.charpoly.roots.filter fun z => dist z c₀ < r ∧ z.im = 0) := by
    rw [localProd, ← Finset.prod_filter_mul_prod_filter_not (discRoots M c₀ r) (fun z => z.im = 0)]
    have e1 : ∏ μ ∈ (discRoots M c₀ r).filter (fun z => ¬z.im = 0), factor M μ = 1 := by
      refine Finset.prod_eq_one fun μ hμ => ?_
      rw [Finset.mem_filter, mem_discRoots] at hμ
      obtain ⟨h1, h2, -⟩ := hD μ hμ.1.2
      exact factor_eq_one h1 h2 (fun h => hμ.2 h.1)
    have e2 : ∏ μ ∈ (discRoots M c₀ r).filter (fun z => z.im = 0), factor M μ
        = ∏ μ ∈ M.charpoly.roots.toFinset.filter (fun z => dist z c₀ < r ∧ z.im = 0),
            (-1 : ℂ) ^ M.charpoly.roots.count μ := by
      rw [discRoots, Finset.filter_filter]
      refine Finset.prod_congr rfl fun μ hμ => ?_
      rw [Finset.mem_filter] at hμ
      obtain ⟨h1, h2, h3⟩ := hD μ hμ.2.1
      exact factor_of_real h1 h2 ⟨hμ.2.2, h3 hμ.2.2⟩
    rw [e1, e2, mul_one, prod_neg_one_pow_count]
  -- the non-real eigenvalues in the disc come in conjugate pairs
  have h2 : Multiset.card (M.charpoly.roots.filter fun z => dist z c₀ < r ∧ z.im ≠ 0)
      = 2 * Multiset.card (M.charpoly.roots.filter fun z => dist z c₀ < r ∧ 0 < z.im) :=
    card_filter_im_ne_zero A (fun z => dist z c₀ < r) hconj
  have h3 : Multiset.card (M.charpoly.roots.filter fun z => dist z c₀ < r)
      = Multiset.card (M.charpoly.roots.filter fun z => dist z c₀ < r ∧ z.im = 0)
        + Multiset.card (M.charpoly.roots.filter fun z => dist z c₀ < r ∧ z.im ≠ 0) :=
    card_filter_eq_add _ _ _ _ (fun z _ => by tauto) (fun z _ => by tauto)
  rw [Multiset.countP_eq_card_filter] at hcount
  have h4 : factor (cpx A₀) c₀ = (-1) ^ (cpx A₀).charpoly.roots.count c₀ := by
    obtain ⟨h1', h2', -⟩ := hD c₀ (by rw [dist_self]; exact hr)
    exact factor_of_real h1' h2' hc₀'
  rw [h1, h4, ← hcount, h3, h2, pow_add, pow_mul]
  simp

/-! ### The signature on the disc, and the circle case -/

open Classical in
/-- The circle eigenvalues of `M` in the disc. -/
noncomputable def circleRoots (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (c₀ : ℂ) (r : ℝ) : Finset ℂ :=
  M.charpoly.roots.toFinset.filter fun z => dist z c₀ < r ∧ ‖z‖ = 1

open Classical in
/-- **The signature of `Q` on a sum of circle eigenspaces is the sum of the signatures.** -/
theorem sum_sigma_of_finset {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    (T : Finset ℂ) (hT : ∀ μ ∈ T, ‖μ‖ = 1) :
    ∑ μ ∈ T, sigma (cpx A) μ
      = 2 * (posIndex GForm (kerAeval (cpx A) (fS (· ∈ T) (cpx A))) : ℤ)
        - (finrank ℂ (kerAeval (cpx A) (fS (· ∈ T) (cpx A))) : ℤ) := by
  induction T using Finset.induction_on with
  | empty =>
    have e : kerAeval (cpx A) (fS (· ∈ (∅ : Finset ℂ)) (cpx A)) = ⊥ := by
      rw [fS, Multiset.filter_eq_nil.2 (fun z _ h => Finset.notMem_empty z h), Multiset.map_zero,
        Multiset.prod_zero, kerAeval, map_one, Module.End.one_eq_id, LinearMap.ker_id]
    rw [e, Finset.sum_empty, finrank_bot]
    have := posIndex_le_finrank (GForm (l := l)) ⊥
    rw [finrank_bot] at this
    omega
  | insert a T ha ih =>
    set M := cpx A with hM
    have hdisj : ∀ z ∈ M.charpoly.roots, ¬(z = a ∧ z ∈ T) := fun z _ h => ha (h.1 ▸ h.2)
    have e : kerAeval M (fS (· ∈ insert a T) M) = kerAeval M (fS (· = a) M) ⊔ kerAeval M (fS (· ∈ T) M) := by
      rw [← kerAeval_fS_or M hdisj]
      congr 1
      exact fS_congr M fun z _ => Finset.mem_insert
    have hinf : kerAeval M (fS (· = a) M) ⊓ kerAeval M (fS (· ∈ T) M) = ⊥ := kerAeval_fS_inf M hdisj
    have horth : ∀ v ∈ kerAeval M (fS (· = a) M), ∀ w ∈ kerAeval M (fS (· ∈ T) M), GForm v w = 0 := by
      intro v hv w hw
      rw [GForm_eq_zero_iff]
      refine HForm_eq_zero_of_mem_kerAeval_of_ne (HForm_cpx hA) (· = a) (· ∈ T) ?_ hv hw
      rintro μ _ ν _ rfl hν h
      apply ha
      have hν1 : ν * starRingEnd ℂ ν = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hT ν (Finset.mem_insert_of_mem hν)]
        norm_num
      have hν0 : starRingEnd ℂ ν ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hν1
        exact zero_ne_one hν1
      have : μ = ν := mul_right_cancel₀ hν0 (h.trans hν1.symm)
      rw [this]
      exact hν
    have hEa : kerAeval M (fS (· = a) M) = E M a := by
      rw [fS_eq_pow_count, kerAeval_pow_count]
    rw [Finset.sum_insert ha, ih (fun μ hμ => hT μ (Finset.mem_insert_of_mem hμ)), e,
      posIndex_sup isHermForm_GForm hinf horth]
    have hrank := Submodule.finrank_sup_add_finrank_inf_eq (kerAeval M (fS (· = a) M))
      (kerAeval M (fS (· ∈ T) M))
    rw [hinf, finrank_bot, add_zero] at hrank
    rw [hrank, hEa, sigma, mPos, finrank_E]
    push_cast
    ring

open Classical in
/-- **The signature of `Q` on the sum of the eigenspaces of the disc is `∑ σ(μ)` over the
circle eigenvalues in the disc**: the eigenvalues off the circle pair into hyperbolic planes. -/
theorem sum_sigma_eq {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    {c₀ : ℂ} {r : ℝ}
    (hstab : ∀ z ∈ (cpx A).charpoly.roots, dist z c₀ < r →
      dist (starRingEnd ℂ z)⁻¹ c₀ < r) :
    ∑ μ ∈ circleRoots (cpx A) c₀ r, sigma (cpx A) μ
      = 2 * (posIndex GForm (discSpace c₀ r (cpx A)) : ℤ)
        - (finrank ℂ (discSpace c₀ r (cpx A)) : ℤ) := by
  set M := cpx A with hM
  have hM0 : ∀ z ∈ M.charpoly.roots, z ≠ 0 := fun z hz h0 => zero_notMem_roots hA (h0 ▸ hz)
  -- the sum of the circle part and of the off-circle part
  set P₁ : ℂ → Prop := fun z => dist z c₀ < r ∧ ‖z‖ = 1 with hP₁
  set P₂ : ℂ → Prop := fun z => dist z c₀ < r ∧ ‖z‖ ≠ 1 with hP₂
  have hdisj : ∀ z ∈ M.charpoly.roots, ¬(P₁ z ∧ P₂ z) := fun z _ h => h.2.2 h.1.2
  have eV : discSpace c₀ r M = kerAeval M (fS P₁ M) ⊔ kerAeval M (fS P₂ M) := by
    rw [← kerAeval_fS_or M hdisj, discSpace, fPoly_eq_fS]
    congr 1
    refine fS_congr M fun z _ => ?_
    constructor
    · intro h
      by_cases h1 : ‖z‖ = 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (h | h) <;> exact h.1
  have hinf : kerAeval M (fS P₁ M) ⊓ kerAeval M (fS P₂ M) = ⊥ := kerAeval_fS_inf M hdisj
  have horth : ∀ v ∈ kerAeval M (fS P₁ M), ∀ w ∈ kerAeval M (fS P₂ M), GForm v w = 0 := by
    intro v hv w hw
    rw [GForm_eq_zero_iff]
    refine HForm_eq_zero_of_mem_kerAeval_of_ne (HForm_cpx hA) P₁ P₂ ?_ hv hw
    intro μ _ ν _ hμ hν h
    apply hν.2
    have := congrArg norm h
    rw [norm_mul, Complex.norm_conj, hμ.2, one_mul, norm_one] at this
    exact this
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq (kerAeval M (fS P₁ M))
    (kerAeval M (fS P₂ M))
  rw [hinf, finrank_bot, add_zero] at hrank
  rw [eV, posIndex_sup isHermForm_GForm hinf horth, hrank]
  -- the circle part
  have hT : ∀ μ ∈ circleRoots M c₀ r, ‖μ‖ = 1 := fun μ hμ => by
    rw [circleRoots, Finset.mem_filter] at hμ
    exact hμ.2.2
  have e1 : kerAeval M (fS P₁ M) = kerAeval M (fS (· ∈ circleRoots M c₀ r) M) := by
    congr 1
    refine fS_congr M fun z hz => ?_
    rw [circleRoots, Finset.mem_filter, Multiset.mem_toFinset]
    exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
  rw [sum_sigma_of_finset hA _ hT, ← e1]
  -- the off-circle part is hyperbolic
  set Q₁ : ℂ → Prop := fun z => dist z c₀ < r ∧ ‖z‖ < 1 with hQ₁
  set Q₂ : ℂ → Prop := fun z => dist z c₀ < r ∧ 1 < ‖z‖ with hQ₂
  have hdisj' : ∀ z ∈ M.charpoly.roots, ¬(Q₁ z ∧ Q₂ z) := fun z _ h => by
    linarith [h.1.2, h.2.2]
  have eW : kerAeval M (fS P₂ M) = kerAeval M (fS Q₁ M) ⊔ kerAeval M (fS Q₂ M) := by
    rw [← kerAeval_fS_or M hdisj']
    congr 1
    refine fS_congr M fun z _ => ?_
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne h2 with h3 | h3
      · exact Or.inl ⟨h1, h3⟩
      · exact Or.inr ⟨h1, h3⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2.ne⟩
      · exact ⟨h1, h2.ne'⟩
  have hI : kerAeval M (fS Q₁ M) ≤ kerAeval M (fS P₂ M) := by
    rw [eW]
    exact le_sup_left
  have hiso : ∀ x ∈ kerAeval M (fS Q₁ M), (GForm x x).re = 0 := by
    intro x hx
    have : GForm x x = 0 := by
      rw [GForm_eq_zero_iff]
      refine HForm_eq_zero_of_mem_kerAeval_of_ne (HForm_cpx hA) Q₁ Q₁ ?_ hx hx
      intro μ _ ν _ hμ hν h
      have := congrArg norm h
      rw [norm_mul, Complex.norm_conj, norm_one] at this
      nlinarith [hμ.2, hν.2, norm_nonneg μ, norm_nonneg ν]
    rw [this, Complex.zero_re]
  have hstab' : ∀ z ∈ M.charpoly.roots, P₂ z → P₂ (starRingEnd ℂ z)⁻¹ := by
    intro z hz h
    refine ⟨hstab z hz h.1, ?_⟩
    rw [norm_inv, Complex.norm_conj]
    intro h1
    exact h.2 (by rw [← inv_inv ‖z‖, h1, inv_one])
  have hnd : ∀ v ∈ kerAeval M (fS P₂ M), (∀ w ∈ kerAeval M (fS P₂ M), GForm v w = 0) → v = 0 := by
    intro v hv h
    refine eq_zero_of_mem_kerAeval_fS_of_forall P₂ (HForm_cpx hA) hstab' hv fun w hw => ?_
    rw [← GForm_eq_zero_iff]
    exact h w hw
  have hdim : 2 * finrank ℂ (kerAeval M (fS Q₁ M)) = finrank ℂ (kerAeval M (fS P₂ M)) := by
    rw [finrank_kerAeval_fS, finrank_kerAeval_fS, Multiset.countP_eq_card_filter,
      Multiset.countP_eq_card_filter]
    exact (card_filter_norm_ne_one hA (fun z => dist z c₀ < r) hstab).symm
  rw [posIndex_eq_of_isotropic isHermForm_GForm hI hnd hiso hdim]
  push_cast
  rw [← hdim]
  push_cast
  ring

open Classical in
/-- At `A₀`, the disc contributes exactly `E_{c₀}`. -/
theorem discSpace_self {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {c₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsep : ∀ z ∈ M.charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀) :
    discSpace c₀ r M = E M c₀ := by
  rw [discSpace, fPoly_eq_fS, ← kerAeval_pow_count, ← fS_eq_pow_count]
  congr 1
  refine fS_congr M fun z hz => ?_
  constructor
  · intro h
    by_contra hne
    have := hsep z hz hne
    linarith
  · rintro rfl
    rw [dist_self]
    exact hr

/-- **Corollary 7.3.9.**  Near a symplectic `A₀` with an eigenvalue `c₀` on the unit circle,
the sum of the signatures of the circle eigenvalues of `A` in a small disc about `c₀` is the
signature of `c₀`. -/
theorem eventually_sum_sigma {A₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA₀ : A₀ ∈ Matrix.symplecticGroup l ℝ) {c₀ : ℂ} (hc₀n : ‖c₀‖ = 1) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ z ∈ (cpx A₀).charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀) (hr4 : r ≤ 1 / 4) :
    ∀ᶠ A in 𝓝[Matrix.symplecticGroup l ℝ] A₀,
      ∑ μ ∈ circleRoots (cpx A) c₀ r, sigma (cpx A) μ = sigma (cpx A₀) c₀ := by
  classical
  set M₀ := cpx A₀ with hM₀
  -- the circle carries no eigenvalue of `A₀`, and `Q` is nondegenerate on `E_{c₀}`
  have hcirc : ∀ z ∈ M₀.charpoly.roots, dist z c₀ ≠ r := by
    intro z hz h
    by_cases hne : z = c₀
    · rw [hne, dist_self] at h
      linarith
    · have := hsep z hz hne
      linarith
  have hc₀inv : (starRingEnd ℂ c₀)⁻¹ = c₀ := by
    have h1 : c₀ * starRingEnd ℂ c₀ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc₀n]
      norm_num
    exact (eq_inv_of_mul_eq_one_left h1).symm
  have hnd : ∀ v ∈ discSpace c₀ r M₀, (∀ w ∈ discSpace c₀ r M₀, GForm v w = 0) → v = 0 := by
    intro v hv h
    rw [discSpace, fPoly_eq_fS] at hv h
    refine eq_zero_of_mem_kerAeval_fS_of_forall (fun z => dist z c₀ < r) (HForm_cpx hA₀)
      ?_ hv fun w hw => ?_
    · intro z hz hzr
      have hz' : z = c₀ := by
        by_contra hne
        have := hsep z hz hne
        linarith
      rw [hz', hc₀inv, dist_self]
      exact hr
    · rw [← GForm_eq_zero_iff]
      exact h w hw
  have hpos := (continuous_cpx.tendsto A₀).eventually (eventually_posIndex_eq c₀ r M₀ hcirc hnd)
  filter_upwards [eventually_facts c₀ hr hsep (by linarith : 0 < r / 2) (by linarith),
    hpos.filter_mono nhdsWithin_le_nhds] with A hA hApos
  obtain ⟨hA, hclose, hcount, -⟩ := hA
  have hstab := stab_of_close hA hc₀n hr4 hclose
  rw [sum_sigma_eq hA hstab, hApos, discSpace_self hr hsep, discSpace, fPoly_eq_fS,
    finrank_kerAeval_fS, hcount, sigma, mPos]

open Classical in
/-- **The circle case.**  If every eigenvalue in the disc is neither `-1` nor real in
`(-1, 0)`, the local product is `∏ μ^{σ(μ)}` over the circle eigenvalues with positive
imaginary part in the disc, and it converges as soon as `c₀^{∑ σ(μ)}` is eventually
constant. -/
theorem tendsto_localProd_circle {A₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ} {c₀ : ℂ} (hc₀n : ‖c₀‖ = 1)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ z ∈ (cpx A₀).charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀)
    (hD : ∀ z, dist z c₀ < r → z ≠ -1 ∧ ¬(z.im = 0 ∧ -1 < z.re ∧ z.re < 0)) {c : ℂ}
    (hc : ∀ᶠ A in 𝓝[Matrix.symplecticGroup l ℝ] A₀,
      c₀ ^ (∑ μ ∈ (cpx A).charpoly.roots.toFinset.filter
        (fun z => dist z c₀ < r ∧ ‖z‖ = 1 ∧ 0 < z.im), sigma (cpx A) μ) = c) :
    Tendsto (fun A => localProd (cpx A) c₀ r) (𝓝[Matrix.symplecticGroup l ℝ] A₀) (𝓝 c) := by
  set N := Fintype.card (l ⊕ l) with hN
  set T : Matrix (l ⊕ l) (l ⊕ l) ℝ → Finset ℂ := fun A =>
    (cpx A).charpoly.roots.toFinset.filter (fun z => dist z c₀ < r ∧ ‖z‖ = 1 ∧ 0 < z.im) with hT
  have e : ∀ A, localProd (cpx A) c₀ r = 1 * ∏ μ ∈ T A, μ ^ sigma (cpx A) μ := by
    intro A
    rw [one_mul, localProd, hT]
    show ∏ μ ∈ discRoots (cpx A) c₀ r, factor (cpx A) μ
      = ∏ μ ∈ (cpx A).charpoly.roots.toFinset.filter
          (fun z => dist z c₀ < r ∧ ‖z‖ = 1 ∧ 0 < z.im), μ ^ sigma (cpx A) μ
    rw [← Finset.filter_filter, Finset.prod_filter]
    refine Finset.prod_congr rfl fun μ hμ => ?_
    rw [Finset.mem_filter] at hμ
    obtain ⟨h2, h3⟩ := hD μ hμ.2
    split_ifs with h
    · exact factor_of_circle h
    · exact factor_eq_one h h2 h3
  simp_rw [e]
  refine tendsto_prod_zpow N hc₀n (fun _ => 1) T (fun A => sigma (cpx A)) (fun _ => by simp)
    (fun A => ?_) (fun A μ hμ => ?_) (fun A μ hμ => ?_) (fun ε hε => ?_) ?_
  · exact (Finset.card_filter_le _ _).trans (card_toFinset_le _)
  · exact (natAbs_sigma_le _ _).trans (count_le_card _ _)
  · rw [hT, Finset.mem_filter] at hμ
    exact hμ.2.2.1
  · rcases le_or_gt ε r with hεr | hεr
    · filter_upwards [eventually_facts c₀ hr hsep hε hεr] with A hA
      obtain ⟨-, hclose, -, -⟩ := hA
      intro μ hμ
      rw [hT, Finset.mem_filter, Multiset.mem_toFinset] at hμ
      rw [← dist_eq_norm]
      exact hclose μ hμ.1 hμ.2.1
    · refine Eventually.of_forall fun A μ hμ => ?_
      rw [hT, Finset.mem_filter] at hμ
      rw [← dist_eq_norm]
      exact hμ.2.1.trans hεr
  · filter_upwards [hc] with A hA
    rw [one_mul]
    exact hA

/-! ### The case `c₀ = -1`, Proposition 7.3.10 -/

open Classical in
/-- **The parity identity of Proposition 7.3.10.**  For a symplectic `A` whose eigenvalues in
the disc `D(-1, r)` all have negative real part and are stable under `μ ↦ 1/μ̄`, and if the
disc contains `m₀` eigenvalues, then `m(-1)/2 + p + ∑ σ(μ) ≡ m₀/2 (mod 2)`, where `p` is the
number of eigenvalues in `(-1, 0)` and the sum runs over the circle eigenvalues with positive
imaginary part. -/
theorem parity_neg_one {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    {r : ℝ} (hr : 0 < r) (hD : ∀ z : ℂ, dist z (-1) < r → z.re < 0)
    (hstab : ∀ z ∈ (cpx A).charpoly.roots, dist z (-1) < r →
      dist (starRingEnd ℂ z)⁻¹ (-1) < r) {m₀ : ℕ}
    (hm₀ : Multiset.card ((cpx A).charpoly.roots.filter fun z => dist z (-1) < r) = m₀) :
    (-1 : ℂ) ^ ((cpx A).charpoly.roots.count (-1) / 2
        + Multiset.card ((cpx A).charpoly.roots.filter fun z =>
            dist z (-1) < r ∧ z.im = 0 ∧ -1 < z.re ∧ z.re < 0))
      * (-1) ^ (∑ μ ∈ (cpx A).charpoly.roots.toFinset.filter
          (fun z => dist z (-1) < r ∧ ‖z‖ = 1 ∧ 0 < z.im), sigma (cpx A) μ)
      = (-1) ^ (m₀ / 2) := by
  set M := cpx A with hM
  set s := M.charpoly.roots with hs
  have hconj : ∀ z : ℂ, dist (starRingEnd ℂ z) (-1) < r ↔ dist z (-1) < r := fun z => by
    have e : (-1 : ℂ) = starRingEnd ℂ (-1) := by simp
    conv_lhs => rw [e]
    rw [Complex.dist_conj_conj]
  -- the counts
  set c₁ := s.count (-1) with hc₁
  set p := Multiset.card (s.filter fun z => dist z (-1) < r ∧ z.im = 0 ∧ -1 < z.re ∧ z.re < 0)
    with hp
  set n₁ := Multiset.card (s.filter fun z => dist z (-1) < r ∧ z.im = 0 ∧ z.re < 0 ∧ z ≠ -1)
    with hn₁
  set n₂ := Multiset.card (s.filter fun z => dist z (-1) < r ∧ z.im ≠ 0) with hn₂
  set n₃ := Multiset.card (s.filter fun z => dist z (-1) < r ∧ 0 < z.im) with hn₃
  set n₄ := Multiset.card (s.filter fun z => (dist z (-1) < r ∧ 0 < z.im) ∧ ‖z‖ = 1) with hn₄
  set n₅ := Multiset.card (s.filter fun z => (dist z (-1) < r ∧ 0 < z.im) ∧ ‖z‖ ≠ 1) with hn₅
  set q := Multiset.card (s.filter fun z => (dist z (-1) < r ∧ 0 < z.im) ∧ ‖z‖ < 1) with hq
  set T := s.toFinset.filter (fun z => dist z (-1) < r ∧ ‖z‖ = 1 ∧ 0 < z.im) with hT
  set S₁ := ∑ μ ∈ T, mPos M μ with hS₁
  set S₂ := ∑ μ ∈ T, s.count μ with hS₂
  have hc₁' : c₁ = Multiset.card (s.filter fun z => z = -1) := by
    rw [hc₁, Multiset.count_eq_card_filter_eq]
    congr 1
    exact Multiset.filter_congr fun z _ => eq_comm
  -- `m₀ = c₁ + n₁ + n₂`: `-1`, the other real eigenvalues, the non-real ones
  have h1 : m₀ = Multiset.card (s.filter fun z => dist z (-1) < r ∧ z.im = 0) + n₂ := by
    rw [← hm₀]
    exact card_filter_eq_add s _ _ _ (fun z _ => by tauto) (fun z _ => by tauto)
  have h2 : Multiset.card (s.filter fun z => dist z (-1) < r ∧ z.im = 0)
      = Multiset.card (s.filter fun z => z = -1) + n₁ := by
    refine card_filter_eq_add s _ _ _ (fun z _ => ?_) (fun z _ h => h.2.2.2.2 h.1)
    constructor
    · rintro ⟨hz1, hz2⟩
      by_cases hz : z = -1
      · exact Or.inl hz
      · exact Or.inr ⟨hz1, hz2, hD z hz1, hz⟩
    · rintro (rfl | ⟨hz1, hz2, -, -⟩)
      · exact ⟨by rw [dist_self]; exact hr, by simp⟩
      · exact ⟨hz1, hz2⟩
  -- the pairings
  have h3 : n₁ = 2 * p := card_filter_neg_real hA (fun z => dist z (-1) < r) hstab
  have h4 : n₂ = 2 * n₃ := card_filter_im_ne_zero A (fun z => dist z (-1) < r) hconj
  have h5 : n₃ = n₄ + n₅ :=
    card_filter_eq_add s _ _ _ (fun z _ => by tauto) (fun z _ => by tauto)
  have h6 : n₅ = 2 * q := by
    refine card_filter_norm_ne_one hA (fun z => dist z (-1) < r ∧ 0 < z.im) fun z hz h => ?_
    refine ⟨hstab z hz h.1, ?_⟩
    have hz0 : z ≠ 0 := fun h0 => zero_notMem_roots hA (h0 ▸ hz)
    rw [Complex.inv_im, Complex.conj_im, Complex.normSq_conj, neg_neg]
    exact div_pos h.2 (Complex.normSq_pos.2 hz0)
  have h7 : n₄ = S₂ := by
    rw [hS₂, hT, sum_count_filter, hn₄]
    congr 1
    exact Multiset.filter_congr fun z _ => by tauto
  have hc₁even : Even c₁ := even_count_neg_one hA
  have hsigma : ∑ μ ∈ T, sigma M μ = 2 * (S₁ : ℤ) - (S₂ : ℤ) := by
    simp only [hS₁, hS₂, sigma, Finset.sum_sub_distrib, ← Finset.mul_sum, Nat.cast_sum, hs]
  -- assemble
  rw [hsigma, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  apply neg_one_zpow_eq_of_even
  obtain ⟨k, hk⟩ := hc₁even
  rw [Int.even_iff]
  omega

open Classical in
/-- **The case `c₀ = -1`.**  The local product is `(-1)^{m(-1)/2 + p} ∏ μ^{σ(μ)}`, and it
converges to `(-1)^{m(-1)(A₀)/2}` by the parity identity. -/
theorem tendsto_localProd_neg_one {A₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ} {r : ℝ} (hr : 0 < r)
    (hsep : ∀ z ∈ (cpx A₀).charpoly.roots, z ≠ -1 → 3 * r ≤ dist z (-1)) (hr4 : r ≤ 1 / 4)
    (hD : ∀ z : ℂ, dist z (-1) < r → z.re < 0) :
    Tendsto (fun A => localProd (cpx A) (-1) r) (𝓝[Matrix.symplecticGroup l ℝ] A₀)
      (𝓝 (factor (cpx A₀) (-1))) := by
  set N := Fintype.card (l ⊕ l) with hN
  set T : Matrix (l ⊕ l) (l ⊕ l) ℝ → Finset ℂ := fun A =>
    (cpx A).charpoly.roots.toFinset.filter (fun z => dist z (-1) < r ∧ ‖z‖ = 1 ∧ 0 < z.im)
    with hT
  set g : Matrix (l ⊕ l) (l ⊕ l) ℝ → ℂ := fun A =>
    (-1) ^ ((cpx A).charpoly.roots.count (-1) / 2
      + Multiset.card ((cpx A).charpoly.roots.filter fun z =>
          dist z (-1) < r ∧ z.im = 0 ∧ -1 < z.re ∧ z.re < 0)) with hg
  -- the decomposition of the local product
  have e : ∀ A, localProd (cpx A) (-1) r = g A * ∏ μ ∈ T A, μ ^ sigma (cpx A) μ := by
    intro A
    set M := cpx A with hM
    have hne1 : ∀ z : ℂ, ¬(‖z‖ = 1 ∧ 0 < z.im) → z ≠ -1 →
        ¬(z.im = 0 ∧ -1 < z.re ∧ z.re < 0) → factor M z = 1 := fun z h1 h2 h3 =>
      factor_eq_one h1 h2 h3
    have hsplit1 : localProd M (-1) r
        = (∏ μ ∈ (discRoots M (-1) r).filter (fun z => z = -1), factor M μ)
          * ∏ μ ∈ (discRoots M (-1) r).filter (fun z => ¬z = -1), factor M μ :=
      (Finset.prod_filter_mul_prod_filter_not (discRoots M (-1) r) (fun z => z = -1)
        (factor M)).symm
    have hsplit2 : ∏ μ ∈ (discRoots M (-1) r).filter (fun z => ¬z = -1), factor M μ
        = (∏ μ ∈ ((discRoots M (-1) r).filter (fun z => ¬z = -1)).filter
              (fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0), factor M μ)
          * ∏ μ ∈ ((discRoots M (-1) r).filter (fun z => ¬z = -1)).filter
              (fun z => ¬(z.im = 0 ∧ -1 < z.re ∧ z.re < 0)), factor M μ :=
      (Finset.prod_filter_mul_prod_filter_not ((discRoots M (-1) r).filter (fun z => ¬z = -1))
        (fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0) (factor M)).symm
    have hsplit3 : ∏ μ ∈ ((discRoots M (-1) r).filter (fun z => ¬z = -1)).filter
          (fun z => ¬(z.im = 0 ∧ -1 < z.re ∧ z.re < 0)), factor M μ
        = ∏ μ ∈ (((discRoots M (-1) r).filter (fun z => ¬z = -1)).filter
            (fun z => ¬(z.im = 0 ∧ -1 < z.re ∧ z.re < 0))).filter
              (fun z => ‖z‖ = 1 ∧ 0 < z.im), factor M μ := by
      symm
      refine Finset.prod_filter_of_ne (s := ((discRoots M (-1) r).filter (fun z => ¬z = -1)).filter
        (fun z => ¬(z.im = 0 ∧ -1 < z.re ∧ z.re < 0))) (f := factor M)
        (p := fun z => ‖z‖ = 1 ∧ 0 < z.im) fun z hz hne => ?_
      by_contra h
      simp only [Finset.mem_filter, mem_discRoots] at hz
      exact hne (hne1 z h hz.1.2 hz.2)
    rw [hsplit1, hsplit2, hsplit3]
    -- the factor at `-1`
    have e1 : ∏ μ ∈ (discRoots M (-1) r).filter (fun z => z = -1), factor M μ
        = (-1) ^ (M.charpoly.roots.count (-1) / 2) := by
      by_cases hm : (-1 : ℂ) ∈ M.charpoly.roots
      · have : (discRoots M (-1) r).filter (fun z => z = -1) = {-1} := by
          ext z
          rw [Finset.mem_filter, mem_discRoots, Finset.mem_singleton]
          constructor
          · rintro ⟨-, h⟩; exact h
          · rintro rfl; exact ⟨⟨hm, by rw [dist_self]; exact hr⟩, rfl⟩
        rw [this, Finset.prod_singleton, factor_neg_one]
      · have : (discRoots M (-1) r).filter (fun z => z = -1) = ∅ := by
          ext z
          rw [Finset.mem_filter, mem_discRoots]
          simp only [Finset.notMem_empty, iff_false, not_and]
          rintro ⟨hz, -⟩ rfl
          exact hm hz
        rw [this, Finset.prod_empty, Multiset.count_eq_zero.2 hm]
        simp
    -- the factors on `(-1, 0)`
    have e2 : ∏ μ ∈ ((discRoots M (-1) r).filter (fun z => ¬z = -1)).filter
          (fun z => z.im = 0 ∧ -1 < z.re ∧ z.re < 0), factor M μ
        = (-1) ^ Multiset.card (M.charpoly.roots.filter fun z =>
            dist z (-1) < r ∧ z.im = 0 ∧ -1 < z.re ∧ z.re < 0) := by
      rw [← prod_neg_one_pow_count]
      refine Finset.prod_congr ?_ fun μ hμ => ?_
      · ext z
        simp only [Finset.mem_filter, mem_discRoots, Multiset.mem_toFinset]
        constructor
        · rintro ⟨⟨⟨h0, h1⟩, -⟩, h2⟩
          exact ⟨h0, h1, h2⟩
        · rintro ⟨h0, h1, h2⟩
          refine ⟨⟨⟨h0, h1⟩, fun h => ?_⟩, h2⟩
          rw [h] at h2
          simp at h2
      · obtain ⟨-, -, him, hre1, hre2⟩ := Finset.mem_filter.1 hμ
        refine factor_of_real (fun h => ?_) (fun h => ?_) ⟨him, hre1, hre2⟩
        · rw [him] at h
          exact lt_irrefl _ h.2
        · rw [h] at hre1
          simp at hre1
    -- the circle factors
    have e3 : (((discRoots M (-1) r).filter (fun z => ¬z = -1)).filter
          (fun z => ¬(z.im = 0 ∧ -1 < z.re ∧ z.re < 0))).filter (fun z => ‖z‖ = 1 ∧ 0 < z.im)
        = T A := by
      rw [hT]
      ext z
      simp only [Finset.mem_filter, mem_discRoots, Multiset.mem_toFinset]
      constructor
      · rintro ⟨⟨⟨⟨hz, h1⟩, -⟩, -⟩, h2, h3⟩
        exact ⟨hz, h1, h2, h3⟩
      · rintro ⟨hz, h1, h2, h3⟩
        refine ⟨⟨⟨⟨hz, h1⟩, fun h => ?_⟩, fun h => ?_⟩, h2, h3⟩
        · rw [h] at h3
          simp at h3
        · rw [h.1] at h3
          exact lt_irrefl _ h3
    rw [e1, e2, e3, hg]
    dsimp only
    rw [pow_add, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun μ hμ => ?_
    simp only [hT, Finset.mem_filter] at hμ
    exact factor_of_circle hμ.2.2
  simp_rw [e]
  have hgn : ∀ A, ‖g A‖ ≤ 1 := fun A => by
    show ‖(-1 : ℂ) ^ ((cpx A).charpoly.roots.count (-1) / 2
      + Multiset.card ((cpx A).charpoly.roots.filter fun z =>
          dist z (-1) < r ∧ z.im = 0 ∧ -1 < z.re ∧ z.re < 0))‖ ≤ 1
    rw [norm_pow, norm_neg, norm_one, one_pow]
  have hn1 : ‖(-1 : ℂ)‖ = 1 := by simp
  refine tendsto_prod_zpow N hn1 g T (fun A => sigma (cpx A)) hgn (fun A => ?_)
    (fun A μ hμ => ?_) (fun A μ hμ => ?_) (fun ε hε => ?_) ?_
  · exact (Finset.card_filter_le _ _).trans (card_toFinset_le _)
  · exact (natAbs_sigma_le _ _).trans (count_le_card _ _)
  · rw [hT, Finset.mem_filter] at hμ
    exact hμ.2.2.1
  · rcases le_or_gt ε r with hεr | hεr
    · filter_upwards [eventually_facts (-1) hr hsep hε hεr] with A hA
      obtain ⟨-, hclose, -, -⟩ := hA
      intro μ hμ
      rw [hT, Finset.mem_filter, Multiset.mem_toFinset] at hμ
      rw [← dist_eq_norm]
      exact hclose μ hμ.1 hμ.2.1
    · refine Eventually.of_forall fun A μ hμ => ?_
      rw [hT, Finset.mem_filter] at hμ
      rw [← dist_eq_norm]
      exact hμ.2.1.trans hεr
  · filter_upwards [eventually_facts (-1) hr hsep (by linarith : 0 < r / 2) (by linarith)]
      with A hA
    obtain ⟨hA, hclose, hcount, -⟩ := hA
    have hstab := stab_of_close hA (by simp) hr4 hclose
    rw [Multiset.countP_eq_card_filter] at hcount
    rw [factor_neg_one]
    exact parity_neg_one hA hr hD hstab hcount

/-! ### The classification, and the continuity of `ρ` -/

/-- **The local product converges to the factor of `c₀`**, in all cases. -/
theorem tendsto_localProd {A₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA₀ : A₀ ∈ Matrix.symplecticGroup l ℝ) {c₀ : ℂ} (hc₀ : c₀ ∈ (cpx A₀).charpoly.roots)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ z ∈ (cpx A₀).charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀)
    (hrb : r ≤ radiusBound c₀) :
    Tendsto (fun A => localProd (cpx A) c₀ r) (𝓝[Matrix.symplecticGroup l ℝ] A₀)
      (𝓝 (factor (cpx A₀) c₀)) := by
  classical
  have hr4 := radius_le_quarter hrb
  have hc₀0 : c₀ ≠ 0 := fun h => zero_notMem_roots hA₀ (h ▸ hc₀)
  by_cases h1 : ‖c₀‖ = 1 ∧ 0 < c₀.im
  · -- the circle, upper half
    have him : c₀.im ≠ 0 := h1.2.ne'
    have hD : ∀ z, dist z c₀ < r → z ≠ -1 ∧ ¬(z.im = 0 ∧ -1 < z.re ∧ z.re < 0) := by
      intro z hz
      obtain ⟨h, hne⟩ := disc_im hrb him hz
      exact ⟨fun h' => hne (by rw [h']; simp), fun h' => hne h'.1⟩
    rw [factor_of_circle h1]
    refine tendsto_localProd_circle h1.1 hr hsep hD ?_
    filter_upwards [eventually_sum_sigma hA₀ h1.1 hr hsep hr4] with A hA
    rw [← hA]
    congr 1
    refine Finset.sum_congr (Finset.filter_congr fun z _ => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨hz1, hz2, -⟩; exact ⟨hz1, hz2⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨hz1, hz2, (disc_im hrb him hz1).1.2 h1.2⟩
  by_cases h2 : c₀ = -1
  · subst h2
    exact tendsto_localProd_neg_one hr hsep hr4 fun z hz => disc_re_neg_of_neg_one hrb rfl hz
  by_cases h3 : c₀.im = 0 ∧ -1 < c₀.re ∧ c₀.re < 0
  · -- the interval `(-1, 0)`
    have hnorm : ‖c₀‖ ≠ 1 := by
      have e : c₀ = (c₀.re : ℂ) := Complex.ext (by simp) (by simp [h3.1])
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_neg h3.2.2]
      linarith [h3.2.1]
    have hre0 : c₀.re ≠ 0 := h3.2.2.ne
    have hre1 : c₀.re ≠ -1 := h3.2.1.ne'
    have hD : ∀ z, dist z c₀ < r → ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ z ≠ -1 ∧
        (z.im = 0 → -1 < z.re ∧ z.re < 0) := by
      intro z hz
      have hn := (disc_norm hrb hnorm hz).2
      refine ⟨fun h => hn h.1, fun h => hn (by rw [h]; simp), fun _ => ?_⟩
      refine ⟨(disc_re_add_one hrb hre1 hz).1.2 h3.2.1, ?_⟩
      have h4 := disc_re hrb hre0 hz
      rcases lt_or_gt_of_ne h4.2 with h5 | h5
      · exact h5
      · exact absurd (h4.1.1 h5) (by linarith [h3.2.2])
    have h := eventually_localProd_eq_of_real h3 hr hsep hD
    exact tendsto_const_nhds.congr' (h.mono fun A hA => hA.symm)
  by_cases h4 : c₀ = 1
  · -- the eigenvalue `1`
    subst h4
    have hD : ∀ z, dist z (1 : ℂ) < r → z ≠ -1 ∧ ¬(z.im = 0 ∧ -1 < z.re ∧ z.re < 0) := by
      intro z hz
      have h := (disc_re hrb (by simp) hz).1.2 (by simp)
      exact ⟨fun h' => by rw [h'] at h; norm_num at h, fun h' => by linarith [h'.2.2]⟩
    have hf : factor (cpx A₀) 1 = 1 := factor_eq_one (by simp) (by norm_num) (by simp)
    rw [hf]
    refine tendsto_localProd_circle (by simp) hr hsep hD (Eventually.of_forall fun A => ?_)
    rw [_root_.one_zpow]
  -- the trivial case
  have hD : ∀ z, dist z c₀ < r → ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ z ≠ -1 ∧
      ¬(z.im = 0 ∧ -1 < z.re ∧ z.re < 0) := by
    intro z hz
    by_cases him : c₀.im = 0
    · have hre0 : c₀.re ≠ 0 := fun h => hc₀0 (Complex.ext h him)
      have hre1 : c₀.re ≠ -1 := fun h => h2 (Complex.ext (by simp [h]) (by simp [him]))
      have hre1' : c₀.re ≠ 1 := fun h => h4 (Complex.ext (by simp [h]) (by simp [him]))
      have hnorm : ‖c₀‖ ≠ 1 := by
        have e : c₀ = (c₀.re : ℂ) := Complex.ext (by simp) (by simp [him])
        rw [e, Complex.norm_real, Real.norm_eq_abs]
        intro h
        rcases (abs_eq (zero_le_one' ℝ)).1 h with h' | h'
        · exact hre1' h'
        · exact hre1 h'
      have hn := (disc_norm hrb hnorm hz).2
      refine ⟨fun h => hn h.1, fun h => hn (by rw [h]; simp), fun h => ?_⟩
      rcases lt_or_gt_of_ne hre0 with h5 | h5
      · rcases lt_or_gt_of_ne hre1 with h6 | h6
        · exact absurd ((disc_re_add_one hrb hre1 hz).1.1 h.2.1) (by linarith)
        · exact h3 ⟨him, h6, h5⟩
      · exact absurd ((disc_re hrb hre0 hz).1.2 h5) (by linarith [h.2.2])
    · obtain ⟨hs, hne⟩ := disc_im hrb him hz
      refine ⟨fun h => ?_, fun h => hne (by rw [h]; simp), fun h => hne h.1⟩
      by_cases hn : ‖c₀‖ = 1
      · have : ¬0 < c₀.im := fun h' => h1 ⟨hn, h'⟩
        exact this (hs.1 h.2)
      · exact (disc_norm hrb hn hz).2 h.1
  have hf : factor (cpx A₀) c₀ = 1 := by
    obtain ⟨h1', h2', h3'⟩ := hD c₀ (by rw [dist_self]; exact hr)
    exact factor_eq_one h1' h2' h3'
  rw [hf]
  exact tendsto_const_nhds.congr fun A => (localProd_eq_one (M := cpx A) hD).symm

/-- A positive lower bound for a positive function on a finset. -/
theorem exists_pos_le {ι : Type*} (s : Finset ι) (g : ι → ℝ) (hg : ∀ i ∈ s, 0 < g i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, r ≤ g i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨r, hr, hrs⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    refine ⟨min r (g a), lt_min hr (hg a (Finset.mem_insert_self a s)), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hrs i hi)

/-- The radius of the discs about the eigenvalues of `A₀`. -/
theorem exists_radius (R : Finset ℂ) :
    ∃ r : ℝ, 0 < r ∧ (∀ c ∈ R, r ≤ radiusBound c) ∧
      ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' → 3 * r ≤ dist c c' := by
  classical
  obtain ⟨r₁, hr₁, h₁⟩ := exists_pos_le R radiusBound fun c _ => radiusBound_pos c
  obtain ⟨r₂, hr₂, h₂⟩ := exists_pos_le ((R ×ˢ R).filter fun p => p.1 ≠ p.2)
    (fun p => dist p.1 p.2 / 3) fun p hp => by
      rw [Finset.mem_filter] at hp
      exact div_pos (dist_pos.2 hp.2) (by norm_num)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun c hc => (min_le_left _ _).trans (h₁ c hc),
    fun c hc c' hc' hne => ?_⟩
  have := h₂ (c, c') (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hc, hc'⟩, hne⟩)
  have h3 := min_le_right r₁ r₂
  simp only at this
  linarith

/-- **`ρ` is continuous on the symplectic group** (Theorem 7.1.3, the continuity clause). -/
theorem tendsto_rhoC {A₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA₀ : A₀ ∈ Matrix.symplecticGroup l ℝ) :
    Tendsto (fun A => rhoC (cpx A)) (𝓝[Matrix.symplecticGroup l ℝ] A₀) (𝓝 (rhoC (cpx A₀))) := by
  classical
  set R := (cpx A₀).charpoly.roots.toFinset with hR
  obtain ⟨r, hr, hrb, hsep⟩ := exists_radius R
  have hsep' : ∀ c ∈ R, ∀ z ∈ (cpx A₀).charpoly.roots, z ≠ c → 3 * r ≤ dist z c :=
    fun c hc z hz hne => hsep z (Multiset.mem_toFinset.2 hz) c hc hne
  have hcover := (continuous_cpx.tendsto A₀).eventually (eventually_roots_near (cpx A₀) hr)
  have hloc : Tendsto (fun A => ∏ c ∈ R, localProd (cpx A) c r)
      (𝓝[Matrix.symplecticGroup l ℝ] A₀) (𝓝 (∏ c ∈ R, factor (cpx A₀) c)) :=
    tendsto_finsetProd R fun c hc =>
      tendsto_localProd hA₀ (Multiset.mem_toFinset.1 hc) hr (hsep' c hc) (hrb c hc)
  refine hloc.congr' ?_
  filter_upwards [hcover.filter_mono nhdsWithin_le_nhds] with A hA
  refine (rhoC_eq_prod_localProd (cpx A) R r ?_ ?_).symm
  · intro z hz
    obtain ⟨w, hw, hzw⟩ := hA z hz
    exact ⟨w, Multiset.mem_toFinset.2 hw, hzw⟩
  · intro c hc c' hc' hne
    linarith [hsep c hc c' hc' hne]

/-- **Theorem 7.1.3, the continuity of `ρ`.** -/
theorem continuousOn_rho (n : ℕ) :
    ContinuousOn (rho n) (Matrix.symplecticGroup (Fin n) ℝ) :=
  fun _ hA₀ => tendsto_rhoC hA₀

end Rho
end MorseFloer
