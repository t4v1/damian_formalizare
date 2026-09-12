import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Order.Interval.Set.IsoIoo

/-!
# Compact connected one-manifolds are circles

This file proves, with no `sorry`, that a compact connected Hausdorff space
locally homeomorphic to `ℝ` is homeomorphic to the unit circle of `ℝ²`
(`MorseFloer.OneManifold.nonempty_homeomorph_sphere_of_chartedSpace`, and the
smooth form `MorseFloer.OneManifold.classification_dim_one_general`). This is
the closed case of Theorem 2.3.2 of the book, which `Chapter2.classification_dim_one`
states. The smooth structure plays no role, and neither does paracompactness:
the proof is purely topological, after Gale ("The classification of
1-manifolds: a take-home exam", Amer. Math. Monthly, 1987).

Hausdorffness cannot be dropped: the circle with one point doubled is compact,
connected and locally homeomorphic to `ℝ`. Its essential use is the Hausdorff
step `not_isBounded_image` below; it is used once more, routinely, to see that
the compact image of a circle is closed.

## The route

An *arc* is an open embedding `γ : ℝ → V`. Every point lies on an arc (a chart,
restricted to a small interval, `exists_arc_of_openPartialHomeomorph`).

* **Invariance of domain on the line** (`isOpenMap_of_injective`). A continuous
  injective map `ℝ → V` is open. Read in an arc it is a continuous injective map
  of an interval into `ℝ`, hence strictly monotone, and the intermediate value
  theorem makes it open. This spares all openness checks for glued arcs.

* **Two arcs** (`two_arcs`). Let `γ, δ` be arcs whose images `U, W` meet, with
  neither image inside the other. Put `A = γ⁻¹ W` and let `τ = δ⁻¹ ∘ γ : A → ℝ`
  be the transition map, continuous and injective.
  - *Hausdorff step* (`not_isBounded_image`). If `c ∉ A` is a limit of a set
    `S ⊆ A`, then `τ` is unbounded on `S`: otherwise `τ` has a cluster value `L`
    at `c`, and `δ L` and `γ c` are both limits of `γ` along `S`, so `γ c = δ L`
    lies in `W`.
  - Consequently every point of `A` sees a whole ray of `A` on one side
    (`Iic_or_Ici_subset`): a bounded interval `(c, d)` of `A` would be mapped
    by the monotone map `τ` onto all of `ℝ`, forcing `W ⊆ U`.
  - After reflecting `γ` and `δ`, `A ⊇ (c, ∞)` with `c ∉ A` and `τ` increasing
    there (`two_arcs_core`). If `A` has no point left of `c`, then `U ∪ W` is
    one arc: follow `γ` up to a point `t₀`, then `δ` (`glue_arc`). Otherwise `A`
    also contains a ray `(-∞, d)` with `d ≤ c`, and then `γ` on `[t₁, t₀]`
    followed by `δ` on `[τ t₀, τ t₁]` is a loop.
  - *The circle* (`glue_circle`). The loop descends to a continuous injection of
    `AddCircle` with image `U ∪ W`. That image is compact, hence closed, and open,
    hence everything by connectedness; a continuous bijection from a compact
    space to a Hausdorff space is a homeomorphism.

* **Induction** (`circle_of_locallyArc`). Cover `V` by finitely many arcs.
  Starting from one of them, repeatedly take a point on the frontier of the
  current arc and a covering arc through it. That arc either contains the
  current one (swap them), or merges with it into a longer arc, or closes up
  into a circle. An arc can never be all of `V`, since `ℝ` is not compact, so
  the process must end with a circle before the cover runs out.

The last step identifies `AddCircle` with the unit sphere of
`EuclideanSpace ℝ (Fin 2)` through Mathlib's `Circle`.
-/

open Set Filter Topology Function Bornology
open scoped Manifold ContDiff

namespace MorseFloer
namespace OneManifold

/-! ### The real line -/

/-- Starting from a point `t` of an open set `A ⊆ ℝ` and moving right towards a
point `y ∉ A`, one reaches a first point `d` outside `A`. -/
theorem exists_right_end {A : Set ℝ} (hA : IsOpen A) {t y : ℝ} (ht : t ∈ A) (hty : t ≤ y)
    (hy : y ∉ A) : ∃ d, t < d ∧ d ≤ y ∧ Ico t d ⊆ A ∧ d ∉ A := by
  have hK : IsClosed (Icc t y ∩ Aᶜ) := isClosed_Icc.inter hA.isClosed_compl
  have hne : (Icc t y ∩ Aᶜ).Nonempty := ⟨y, ⟨hty, le_rfl⟩, hy⟩
  have hbdd : BddBelow (Icc t y ∩ Aᶜ) := ⟨t, fun z hz => hz.1.1⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hK.csInf_mem hne hbdd
  refine ⟨sInf (Icc t y ∩ Aᶜ), lt_of_le_of_ne h1 (fun h => h3 (by rw [← h]; exact ht)), h2,
    ?_, h3⟩
  intro z hz
  by_contra hzA
  exact absurd (csInf_le hbdd ⟨⟨hz.1, hz.2.le.trans h2⟩, hzA⟩) (not_le.2 hz.2)

/-- Starting from a point `t` of an open set `A ⊆ ℝ` and moving left towards a
point `x ∉ A`, one reaches a first point `c` outside `A`. -/
theorem exists_left_end {A : Set ℝ} (hA : IsOpen A) {t x : ℝ} (ht : t ∈ A) (hxt : x ≤ t)
    (hx : x ∉ A) : ∃ c, x ≤ c ∧ c < t ∧ Ioc c t ⊆ A ∧ c ∉ A := by
  have hK : IsClosed (Icc x t ∩ Aᶜ) := isClosed_Icc.inter hA.isClosed_compl
  have hne : (Icc x t ∩ Aᶜ).Nonempty := ⟨x, ⟨le_rfl, hxt⟩, hx⟩
  have hbdd : BddAbove (Icc x t ∩ Aᶜ) := ⟨t, fun z hz => hz.1.2⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hK.csSup_mem hne hbdd
  refine ⟨sSup (Icc x t ∩ Aᶜ), h1, lt_of_le_of_ne h2 (fun h => h3 (by rw [h]; exact ht)),
    ?_, h3⟩
  intro z hz
  by_contra hzA
  exact absurd (le_csSup hbdd ⟨⟨h1.trans hz.1.le, hz.2⟩, hzA⟩) (not_le.2 hz.1)

/-- A continuous injective real function on an interval is strictly monotone
or strictly antitone. -/
theorem strictMonoOn_or_strictAntiOn {I : Set ℝ} [I.OrdConnected] (hne : I.Nonempty)
    {τ : ℝ → ℝ} (hc : ContinuousOn τ I) (hi : InjOn τ I) :
    StrictMonoOn τ I ∨ StrictAntiOn τ I := by
  have : Inhabited I := ⟨⟨hne.some, hne.some_mem⟩⟩
  exact (Continuous.strictMono_of_inj hc.domRestrict hi.injective).imp strictMono_domRestrict.mp
    strictAntiOn_iff_strictAnti.mpr

/-- Intermediate values: a continuous function on a preconnected set that is
unbounded above takes every value above any value it takes. -/
theorem Ici_subset_image {I : Set ℝ} (hI : IsPreconnected I) {τ : ℝ → ℝ}
    (hτ : ContinuousOn τ I) {t : ℝ} (ht : t ∈ I) (hub : ¬ BddAbove (τ '' I)) :
    Ici (τ t) ⊆ τ '' I := by
  intro s hs
  obtain ⟨_, ⟨t', ht', rfl⟩, hlt⟩ := not_bddAbove_iff.1 hub s
  exact (hI.image τ hτ).Icc_subset ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩ ⟨hs, hlt.le⟩

/-- Intermediate values: a continuous function on a preconnected set that is
unbounded below takes every value below any value it takes. -/
theorem Iic_subset_image {I : Set ℝ} (hI : IsPreconnected I) {τ : ℝ → ℝ}
    (hτ : ContinuousOn τ I) {t : ℝ} (ht : t ∈ I) (hlb : ¬ BddBelow (τ '' I)) :
    Iic (τ t) ⊆ τ '' I := by
  intro s hs
  obtain ⟨_, ⟨t', ht', rfl⟩, hlt⟩ := not_bddBelow_iff.1 hlb s
  exact (hI.image τ hτ).Icc_subset ⟨t', ht', rfl⟩ ⟨t, ht, rfl⟩ ⟨hlt.le, hs⟩

/-- An unbounded set of reals that is bounded above is unbounded below. -/
theorem not_bddBelow_of_not_isBounded {S : Set ℝ} (h : ¬ IsBounded S) (hb : BddAbove S) :
    ¬ BddBelow S :=
  fun h' => h (isBounded_iff_bddBelow_bddAbove.2 ⟨h', hb⟩)

/-- An unbounded set of reals that is bounded below is unbounded above. -/
theorem not_bddAbove_of_not_isBounded {S : Set ℝ} (h : ¬ IsBounded S) (hb : BddBelow S) :
    ¬ BddAbove S :=
  fun h' => h (isBounded_iff_bddBelow_bddAbove.2 ⟨hb, h'⟩)

/-- A neighbourhood of a real number contains a closed interval around it. -/
theorem exists_Icc_subset_of_mem_nhds {s : Set ℝ} {x : ℝ} (hs : s ∈ 𝓝 x) :
    ∃ a b, a < x ∧ x < b ∧ Icc a b ⊆ s := by
  obtain ⟨a, b, ⟨ha, hb⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hs
  exact ⟨(a + x) / 2, (x + b) / 2, by linarith, by linarith,
    fun z hz => hsub ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩

/-! ### Arcs and transition maps -/

variable {V : Type*} [TopologicalSpace V]

/-- `V` is covered by arcs: every point lies in the image of an open embedding
of the real line. This is all of the manifold structure the proof uses. -/
def LocallyArc (V : Type*) [TopologicalSpace V] : Prop :=
  ∀ x : V, ∃ δ : ℝ → V, IsOpenEmbedding δ ∧ x ∈ range δ

/-- The transition map `δ⁻¹ ∘ γ` from an arc (or any continuous map) `γ` to an
arc `δ`, defined and continuous where `γ` meets the image of `δ`. -/
theorem exists_transition {γ δ : ℝ → V} (hγ : Continuous γ) (hδ : IsOpenEmbedding δ) :
    ∃ τ : ℝ → ℝ, (∀ t, γ t ∈ range δ → δ (τ t) = γ t) ∧
      ContinuousOn τ (γ ⁻¹' range δ) := by
  refine ⟨fun t => (hδ.toOpenPartialHomeomorph δ).symm (γ t),
    fun t ht => hδ.toOpenPartialHomeomorph_right_inv δ ht, ?_⟩
  refine (hδ.toOpenPartialHomeomorph δ).continuousOn_symm.comp hγ.continuousOn ?_
  intro t ht
  rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact ht

omit [TopologicalSpace V] in
/-- A transition map is injective where it is defined. -/
theorem transition_injOn {γ δ : ℝ → V} (hγ : Injective γ) {τ : ℝ → ℝ}
    (hτ : ∀ t, γ t ∈ range δ → δ (τ t) = γ t) : InjOn τ (γ ⁻¹' range δ) := by
  intro t ht t' ht' h
  apply hγ
  rw [← hτ t ht, ← hτ t' ht', h]

omit [TopologicalSpace V] in
/-- If `γ t = δ s` then `t` lies in the domain of the transition map and `τ t = s`. -/
theorem transition_eq {γ δ : ℝ → V} (hδ : Injective δ) {τ : ℝ → ℝ}
    (hτ : ∀ t, γ t ∈ range δ → δ (τ t) = γ t) {t s : ℝ} (h : γ t = δ s) :
    γ t ∈ range δ ∧ τ t = s :=
  ⟨⟨s, h.symm⟩, hδ (by rw [hτ t ⟨s, h.symm⟩, h])⟩

omit [TopologicalSpace V] in
/-- Reversing the parametrisation does not change the image. -/
theorem range_comp_neg (f : ℝ → V) : range (fun t => f (-t)) = range f := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨-t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨-t, by simp⟩

/-- Reversing the parametrisation of an arc gives an arc. -/
theorem isOpenEmbedding_comp_neg {f : ℝ → V} (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (fun t => f (-t)) :=
  hf.comp (Homeomorph.neg ℝ).isOpenEmbedding

/-- **The Hausdorff step.** Let `τ` be a transition map from `γ` to `δ` on a set
`S`, and let `c` be a limit point of `S` at which `γ` does not meet the image
of `δ`. Then `τ` is unbounded on `S`. Otherwise `τ` would have a cluster value
`L` at `c`, and `γ c` and `δ L` would both be limits of `γ` along `S`. -/
theorem not_isBounded_image [T2Space V] {γ δ : ℝ → V} (hγ : Continuous γ) (hδ : Continuous δ)
    {τ : ℝ → ℝ} {S : Set ℝ} (hτ : ∀ t ∈ S, δ (τ t) = γ t) {c : ℝ} (hc : c ∈ closure S)
    (hcA : γ c ∉ range δ) : ¬ IsBounded (τ '' S) := by
  intro hb
  have : (𝓝[S] c).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hc
  have hle : map τ (𝓝[S] c) ≤ 𝓟 (closure (τ '' S)) := by
    rw [le_principal_iff, mem_map]
    exact mem_of_superset self_mem_nhdsWithin fun t ht => subset_closure ⟨t, ht, rfl⟩
  obtain ⟨L, -, hL⟩ := hb.isCompact_closure hle
  have hmap : map γ (𝓝[S] c) = map δ (map τ (𝓝[S] c)) := by
    rw [map_map]
    exact map_congr (eventually_nhdsWithin_of_forall fun t ht => (hτ t ht).symm)
  have h1 : ClusterPt (δ L) (map γ (𝓝[S] c)) := by
    rw [hmap]
    exact hL.map hδ.continuousAt tendsto_map
  have h2 : map γ (𝓝[S] c) ≤ 𝓝 (γ c) := hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact hcA ⟨L, eq_of_nhds_neBot (h1.neBot.mono (inf_le_inf_left _ h2))⟩

/-! ### Invariance of domain on the line -/

/-- **Invariance of domain in dimension one.** A continuous injective map from
the line to a space covered by arcs is open. -/
theorem isOpenMap_of_injective (hloc : LocallyArc V) {f : ℝ → V} (hf : Continuous f)
    (hinj : Injective f) : IsOpenMap f := by
  rw [isOpenMap_iff_nhds_le]
  intro x O hO
  obtain ⟨δ, hδ, s, hs⟩ := hloc (f x)
  obtain ⟨g, hg, hgc⟩ := exists_transition hf hδ
  have hA : f ⁻¹' range δ ∈ 𝓝 x :=
    hf.continuousAt.preimage_mem_nhds (hδ.isOpen_range.mem_nhds ⟨s, hs⟩)
  obtain ⟨a, b, hax, hxb, hsub⟩ := exists_Icc_subset_of_mem_nhds (inter_mem hO hA)
  have hab : a ≤ b := (hax.trans hxb).le
  have hgc' : ContinuousOn g (Icc a b) := hgc.mono fun t ht => (hsub ht).2
  have hfg : ∀ t ∈ Icc a b, δ (g t) = f t := fun t ht => hg t (hsub ht).2
  have hgi : InjOn g (Icc a b) := fun t ht t' ht' h =>
    hinj (by rw [← hfg t ht, ← hfg t' ht', h])
  have hxI : x ∈ Icc a b := ⟨hax.le, hxb.le⟩
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have key : ∃ u v, u < g x ∧ g x < v ∧ Icc u v ⊆ g '' Icc a b := by
    rcases hgc'.strictMonoOn_of_injOn_Icc' hab hgi with hm | hm
    · exact ⟨g a, g b, hm haI hxI hax, hm hxI hbI hxb, intermediate_value_Icc hab hgc'⟩
    · exact ⟨g b, g a, hm hxI hbI hxb, hm haI hxI hax, intermediate_value_Icc' hab hgc'⟩
  obtain ⟨u, v, hu, hv, huv⟩ := key
  have hnhds : δ '' Ioo u v ∈ 𝓝 (f x) := by
    rw [← hfg x hxI]
    exact (hδ.isOpenMap _ isOpen_Ioo).mem_nhds ⟨g x, ⟨hu, hv⟩, rfl⟩
  refine mem_of_superset hnhds ?_
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨t, ht, rfl⟩ := huv (Ioo_subset_Icc_self hw)
  show δ (g t) ∈ O
  rw [hfg t ht]
  exact (hsub ht).1

/-- The line itself is covered by arcs. -/
theorem locallyArc_real : LocallyArc ℝ :=
  fun x => ⟨id, IsOpenEmbedding.id, x, rfl⟩

/-! ### Gluing two arcs -/

/-- **Gluing into an arc.** Suppose that `γ` and `δ` agree at `γ t₀ = δ s₀`,
that the part of `γ` after `t₀` lies on `δ` after `s₀`, that the part of `δ`
before `s₀` lies on `γ` before `t₀`, and that `γ` before `t₀` never meets `δ`
after `s₀`. Then following `γ` up to `t₀` and `δ` from `s₀` on is an arc whose
image is the union of the two. -/
theorem glue_arc (hloc : LocallyArc V) {γ δ : ℝ → V} (hγ : IsOpenEmbedding γ)
    (hδ : IsOpenEmbedding δ) {t₀ s₀ : ℝ} (h0 : γ t₀ = δ s₀)
    (hγδ : ∀ t, t₀ < t → ∃ s, s₀ < s ∧ δ s = γ t)
    (hδγ : ∀ s, s < s₀ → ∃ t, t < t₀ ∧ γ t = δ s)
    (hdisj : ∀ t s, t < t₀ → s₀ < s → γ t ≠ δ s) :
    ∃ ε : ℝ → V, IsOpenEmbedding ε ∧ range ε = range γ ∪ range δ := by
  let ε : ℝ → V := fun x => if x ≤ t₀ then γ x else δ (x - t₀ + s₀)
  have hεl : ∀ x, x ≤ t₀ → ε x = γ x := fun x hx => if_pos hx
  have hεr : ∀ x, t₀ < x → ε x = δ (x - t₀ + s₀) := fun x hx => if_neg (not_le.2 hx)
  have hc : Continuous ε := by
    refine Continuous.if_le hγ.continuous (hδ.continuous.comp (by fun_prop)) continuous_id
      continuous_const ?_
    intro x hx
    simp [hx, h0]
  have hinj : Injective ε := by
    have key : ∀ x y, x ≤ t₀ → t₀ < y → ε x ≠ ε y := by
      intro x y hx hy hxy
      rw [hεl x hx, hεr y hy] at hxy
      rcases hx.lt_or_eq with hx | hx
      · exact hdisj x _ hx (by linarith) hxy
      · rw [hx, h0] at hxy
        have := hδ.injective hxy
        linarith
    intro x y hxy
    rcases le_or_gt x t₀ with hx | hx <;> rcases le_or_gt y t₀ with hy | hy
    · rw [hεl x hx, hεl y hy] at hxy
      exact hγ.injective hxy
    · exact absurd hxy (key x y hx hy)
    · exact absurd hxy.symm (key y x hy hx)
    · rw [hεr x hx, hεr y hy] at hxy
      have := hδ.injective hxy
      linarith
  have hrange : range ε = range γ ∪ range δ := by
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      rcases le_or_gt x t₀ with hx | hx
      · exact Or.inl ⟨x, (hεl x hx).symm⟩
      · exact Or.inr ⟨_, (hεr x hx).symm⟩
    · have hδmem : ∀ s, s₀ ≤ s → δ s ∈ range ε := by
        intro s hs
        rcases hs.lt_or_eq with hs | hs
        · refine ⟨s - s₀ + t₀, ?_⟩
          rw [hεr _ (by linarith)]
          congr 1
          ring
        · exact ⟨t₀, by rw [hεl _ le_rfl, h0, hs]⟩
      rintro _ (⟨t, rfl⟩ | ⟨s, rfl⟩)
      · rcases le_or_gt t t₀ with ht | ht
        · exact ⟨t, hεl t ht⟩
        · obtain ⟨s, hs, hst⟩ := hγδ t ht
          rw [← hst]
          exact hδmem s hs.le
      · rcases le_or_gt s₀ s with hs | hs
        · exact hδmem s hs
        · obtain ⟨t, ht, hts⟩ := hδγ s hs
          exact ⟨t, by rw [hεl t ht.le, hts]⟩
  exact ⟨ε, IsOpenEmbedding.of_continuous_injective_isOpenMap hc hinj
    (isOpenMap_of_injective hloc hc hinj), hrange⟩

/-- **Gluing into a circle.** Suppose `γ t₀ = δ s₀` and `γ t₁ = δ s₁` with
`t₁ < t₀` and `s₀ < s₁`, that `γ` outside `[t₁, t₀]` lies on `δ([s₀, s₁])`,
that `δ` outside `[s₀, s₁]` lies on `γ([t₁, t₀])`, and that the open pieces
`γ((t₁, t₀))` and `δ((s₀, s₁))` are disjoint. Then `γ` on `[t₁, t₀]` followed by
`δ` on `[s₀, s₁]` is a simple loop through all of `U ∪ W`, and in a connected
Hausdorff space this makes the whole space a circle. -/
theorem glue_circle [T2Space V] [ConnectedSpace V] {γ δ : ℝ → V} (hγ : IsOpenEmbedding γ)
    (hδ : IsOpenEmbedding δ) {t₁ t₀ s₀ s₁ : ℝ} (ht : t₁ < t₀) (hs : s₀ < s₁)
    (h0 : γ t₀ = δ s₀) (h1 : γ t₁ = δ s₁)
    (hγc : ∀ t, t ∉ Icc t₁ t₀ → ∃ s ∈ Icc s₀ s₁, δ s = γ t)
    (hδc : ∀ s, s ∉ Icc s₀ s₁ → ∃ t ∈ Icc t₁ t₀, γ t = δ s)
    (hdisj : ∀ t ∈ Ioo t₁ t₀, ∀ s ∈ Ioo s₀ s₁, γ t ≠ δ s) :
    Nonempty (V ≃ₜ Circle) := by
  obtain ⟨a, rfl⟩ : ∃ a, t₀ = t₁ + a := ⟨t₀ - t₁, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, s₁ = s₀ + b := ⟨s₁ - s₀, by ring⟩
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have : Fact (0 < a + b) := ⟨by linarith⟩
  -- the loop, parametrised by `[0, a + b]`
  let F : ℝ → V := fun x => if x ≤ a then γ (t₁ + x) else δ (s₀ + (x - a))
  have hFl : ∀ x, x ≤ a → F x = γ (t₁ + x) := fun x hx => if_pos hx
  have hFr : ∀ x, a < x → F x = δ (s₀ + (x - a)) := fun x hx => if_neg (not_le.2 hx)
  have hFc : Continuous F := by
    refine Continuous.if_le (hγ.continuous.comp (by fun_prop)) (hδ.continuous.comp (by fun_prop))
      continuous_id continuous_const ?_
    intro x hx
    simp [hx, h0]
  have hFp : F 0 = F (a + b) := by
    rw [hFl 0 ha.le, hFr (a + b) (by linarith), add_zero, add_sub_cancel_left]
    exact h1
  have hFi : InjOn F (Ico 0 (a + b)) := by
    have key : ∀ x y, x ∈ Icc 0 a → y ∈ Ioo a (a + b) → F x ≠ F y := by
      intro x y hx hy hxy
      rw [hFl x hx.2, hFr y hy.1] at hxy
      have hs' : s₀ + (y - a) ∈ Ioo s₀ (s₀ + b) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      rcases hx.1.lt_or_eq with hx0 | hx0
      · rcases hx.2.lt_or_eq with hxa | hxa
        · exact hdisj (t₁ + x) ⟨by linarith, by linarith⟩ _ hs' hxy
        · rw [hxa, h0] at hxy
          have := hδ.injective hxy
          linarith [hs'.1]
      · rw [← hx0, add_zero, h1] at hxy
        have := hδ.injective hxy
        linarith [hs'.2]
    intro x hx y hy hxy
    rcases le_or_gt x a with hxa | hxa <;> rcases le_or_gt y a with hya | hya
    · rw [hFl x hxa, hFl y hya] at hxy
      have := hγ.injective hxy
      linarith
    · exact absurd hxy (key x y ⟨hx.1, hxa⟩ ⟨hya, hy.2⟩)
    · exact absurd hxy.symm (key y x ⟨hy.1, hya⟩ ⟨hxa, hx.2⟩)
    · rw [hFr x hxa, hFr y hya] at hxy
      have := hδ.injective hxy
      linarith
  have hγmem : ∀ t ∈ Icc t₁ (t₁ + a), γ t ∈ F '' Ico 0 (a + b) := by
    intro t ht
    refine ⟨t - t₁, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [hFl _ (by linarith [ht.2])]
    congr 1
    ring
  have hδmem : ∀ s ∈ Icc s₀ (s₀ + b), δ s ∈ F '' Ico 0 (a + b) := by
    intro s hs
    rcases hs.1.lt_or_eq with hs0 | hs0
    · rcases hs.2.lt_or_eq with hsb | hsb
      · refine ⟨s - s₀ + a, ⟨by linarith, by linarith⟩, ?_⟩
        rw [hFr _ (by linarith)]
        congr 1
        ring
      · rw [hsb, ← h1]
        exact hγmem t₁ ⟨le_rfl, by linarith⟩
    · rw [← hs0, ← h0]
      exact hγmem _ ⟨by linarith, le_rfl⟩
  have hrange : F '' Ico 0 (a + b) = range γ ∪ range δ := by
    apply Subset.antisymm
    · rintro _ ⟨x, -, rfl⟩
      rcases le_or_gt x a with hx | hx
      · exact Or.inl ⟨_, (hFl x hx).symm⟩
      · exact Or.inr ⟨_, (hFr x hx).symm⟩
    · rintro _ (⟨t, rfl⟩ | ⟨s, rfl⟩)
      · by_cases ht' : t ∈ Icc t₁ (t₁ + a)
        · exact hγmem t ht'
        · obtain ⟨s, hs, hst⟩ := hγc t ht'
          rw [← hst]
          exact hδmem s hs
      · by_cases hs' : s ∈ Icc s₀ (s₀ + b)
        · exact hδmem s hs'
        · obtain ⟨t, ht, hts⟩ := hδc s hs'
          rw [← hts]
          exact hγmem t ht
  -- the loop on the circle `AddCircle (a + b)`
  let G : AddCircle (a + b) → V := AddCircle.liftIco (a + b) 0 F
  have hGc : Continuous G := AddCircle.liftIco_zero_continuous hFp hFc.continuousOn
  have hmem : ∀ z : AddCircle (a + b), (AddCircle.equivIco (a + b) 0 z : ℝ) ∈ Ico 0 (a + b) := by
    intro z
    have := (AddCircle.equivIco (a + b) 0 z).2
    exact ⟨this.1, this.2.trans_eq (zero_add _)⟩
  have hGi : Injective G := by
    intro z z' h
    apply (AddCircle.equivIco (a + b) 0).injective
    exact Subtype.ext (hFi (hmem z) (hmem z') h)
  have hGr : range G = range γ ∪ range δ := by
    rw [← hrange]
    apply Subset.antisymm
    · rintro _ ⟨z, rfl⟩
      exact ⟨_, hmem z, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨(x : AddCircle (a + b)), AddCircle.liftIco_zero_coe_apply hx⟩
  have hGs : Surjective G := by
    have hopen : IsOpen (range G) := by
      rw [hGr]
      exact hγ.isOpen_range.union hδ.isOpen_range
    exact range_eq_univ.1
      (IsClopen.eq_univ ⟨(isCompact_range hGc).isClosed, hopen⟩ (range_nonempty G))
  exact ⟨(hGc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G ⟨hGi, hGs⟩)).symm.trans
    (AddCircle.homeomorphCircle (ne_of_gt (show (0 : ℝ) < a + b by linarith)))⟩

/-! ### Two overlapping arcs -/

/-- If the image of `δ` is not inside that of `γ`, then each point of the
domain `A = γ⁻¹(im δ)` of the transition map sees a whole ray of `A`, to its
left or to its right. A bounded interval `(c, d)` of `A` with `c, d ∉ A` would
be mapped by the monotone transition map onto all of `ℝ` (it is unbounded at
both ends by the Hausdorff step), putting the image of `δ` inside that of `γ`. -/
theorem Iic_or_Ici_subset [T2Space V] {γ δ : ℝ → V} (hγ : IsOpenEmbedding γ)
    (hδ : IsOpenEmbedding δ) {τ : ℝ → ℝ} (hτ : ∀ t, γ t ∈ range δ → δ (τ t) = γ t)
    (hτc : ContinuousOn τ (γ ⁻¹' range δ)) (hWU : ¬ range δ ⊆ range γ) {t : ℝ}
    (ht : t ∈ γ ⁻¹' range δ) :
    Iic t ⊆ γ ⁻¹' range δ ∨ Ici t ⊆ γ ⁻¹' range δ := by
  have hAo : IsOpen (γ ⁻¹' range δ) := hδ.isOpen_range.preimage hγ.continuous
  by_contra h
  simp only [not_or, not_subset] at h
  obtain ⟨⟨x, hx, hxA⟩, ⟨y, hy, hyA⟩⟩ := h
  obtain ⟨c, -, hct, hcA, hc⟩ := exists_left_end hAo ht hx hxA
  obtain ⟨d, htd, -, hdA, hd⟩ := exists_right_end hAo ht hy hyA
  have hI : Ioo c d ⊆ γ ⁻¹' range δ := fun z hz =>
    (le_or_gt z t).elim (fun h => hcA ⟨hz.1, h⟩) (fun h => hdA ⟨h.le, hz.2⟩)
  have hτI : ContinuousOn τ (Ioo c d) := hτc.mono hI
  have hiI : InjOn τ (Ioo c d) := (transition_injOn hγ.injective hτ).mono hI
  have hL : ¬ IsBounded (τ '' Ioo c t) :=
    not_isBounded_image hγ.continuous hδ.continuous
      (fun z hz => hτ z (hcA (Ioo_subset_Ioc_self hz)))
      (by rw [closure_Ioo hct.ne]; exact left_mem_Icc.2 hct.le) hc
  have hR : ¬ IsBounded (τ '' Ioo t d) :=
    not_isBounded_image hγ.continuous hδ.continuous
      (fun z hz => hτ z (hdA (Ioo_subset_Ico_self hz)))
      (by rw [closure_Ioo htd.ne]; exact right_mem_Icc.2 htd.le) hd
  have hLsub : τ '' Ioo c t ⊆ τ '' Ioo c d := image_mono (Ioo_subset_Ioo_right htd.le)
  have hRsub : τ '' Ioo t d ⊆ τ '' Ioo c d := image_mono (Ioo_subset_Ioo_left hct.le)
  have hub : ¬ BddAbove (τ '' Ioo c d) ∧ ¬ BddBelow (τ '' Ioo c d) := by
    rcases strictMonoOn_or_strictAntiOn (nonempty_Ioo.2 (hct.trans htd)) hτI hiI with hm | hm
    · refine ⟨fun hb => ?_, fun hb => ?_⟩
      · refine not_bddAbove_of_not_isBounded hR ⟨τ t, ?_⟩ (hb.mono hRsub)
        rintro _ ⟨z, hz, rfl⟩
        exact (hm ⟨hct, htd⟩ ⟨hct.trans hz.1, hz.2⟩ hz.1).le
      · refine not_bddBelow_of_not_isBounded hL ⟨τ t, ?_⟩ (hb.mono hLsub)
        rintro _ ⟨z, hz, rfl⟩
        exact (hm ⟨hz.1, hz.2.trans htd⟩ ⟨hct, htd⟩ hz.2).le
    · refine ⟨fun hb => ?_, fun hb => ?_⟩
      · refine not_bddAbove_of_not_isBounded hL ⟨τ t, ?_⟩ (hb.mono hLsub)
        rintro _ ⟨z, hz, rfl⟩
        exact (hm ⟨hz.1, hz.2.trans htd⟩ ⟨hct, htd⟩ hz.2).le
      · refine not_bddBelow_of_not_isBounded hR ⟨τ t, ?_⟩ (hb.mono hRsub)
        rintro _ ⟨z, hz, rfl⟩
        exact (hm ⟨hct, htd⟩ ⟨hct.trans hz.1, hz.2⟩ hz.1).le
  apply hWU
  rintro _ ⟨s, rfl⟩
  obtain ⟨_, ⟨z₁, hz₁, rfl⟩, h₁⟩ := not_bddAbove_iff.1 hub.1 s
  obtain ⟨_, ⟨z₂, hz₂, rfl⟩, h₂⟩ := not_bddBelow_iff.1 hub.2 s
  obtain ⟨z, hz, rfl⟩ :=
    (isPreconnected_Ioo.image τ hτI).Icc_subset ⟨z₂, hz₂, rfl⟩ ⟨z₁, hz₁, rfl⟩ ⟨h₂.le, h₁.le⟩
  exact ⟨z, (hτ z (hI hz)).symm⟩

/-- **Two arcs, normalised.** Suppose the domain of the transition map `τ`
contains the ray `(c, ∞)`, but not `c`, and `τ` increases there. Then the union
of the two images is an arc, or the whole space is a circle. -/
theorem two_arcs_core [T2Space V] [ConnectedSpace V] (hloc : LocallyArc V) {γ δ : ℝ → V}
    (hγ : IsOpenEmbedding γ) (hδ : IsOpenEmbedding δ) {τ : ℝ → ℝ}
    (hτ : ∀ t, γ t ∈ range δ → δ (τ t) = γ t) (hτc : ContinuousOn τ (γ ⁻¹' range δ))
    (hWU : ¬ range δ ⊆ range γ) {c : ℝ} (hc : γ c ∉ range δ)
    (hcA : Ioi c ⊆ γ ⁻¹' range δ) (hmono : StrictMonoOn τ (Ioi c)) :
    (∃ ε : ℝ → V, IsOpenEmbedding ε ∧ range ε = range γ ∪ range δ) ∨
      Nonempty (V ≃ₜ Circle) := by
  have hAo : IsOpen (γ ⁻¹' range δ) := hδ.isOpen_range.preimage hγ.continuous
  have hinj : InjOn τ (γ ⁻¹' range δ) := transition_injOn hγ.injective hτ
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, c < t₀ := ⟨c + 1, by linarith⟩
  -- `τ` runs down to `-∞` on `(c, t₀]`
  have hLb : ¬ IsBounded (τ '' Ioo c t₀) :=
    not_isBounded_image hγ.continuous hδ.continuous
      (fun z hz => hτ z (hcA hz.1))
      (by rw [closure_Ioo ht₀.ne]; exact left_mem_Icc.2 ht₀.le) hc
  have hL : ∀ s ≤ τ t₀, ∃ t ∈ Ioc c t₀, τ t = s := by
    have h1 : BddAbove (τ '' Ioc c t₀) := by
      refine ⟨τ t₀, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hmono.monotoneOn hz.1 ht₀ hz.2
    have h2 : ¬ BddBelow (τ '' Ioc c t₀) :=
      not_bddBelow_of_not_isBounded
        (fun hb => hLb (hb.subset (image_mono Ioo_subset_Ioc_self))) h1
    intro s hs
    exact Iic_subset_image isPreconnected_Ioc (hτc.mono fun z hz => hcA hz.1) ⟨ht₀, le_rfl⟩
      h2 hs
  by_cases hleft : ∀ t ∈ γ ⁻¹' range δ, c < t
  · -- one component: the union is an arc
    left
    refine glue_arc hloc hγ hδ (t₀ := t₀) (s₀ := τ t₀) (hτ t₀ (hcA ht₀)).symm ?_ ?_ ?_
    · intro t ht
      exact ⟨τ t, hmono ht₀ (ht₀.trans ht) ht, hτ t (hcA (ht₀.trans ht))⟩
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := hL s hs.le
      refine ⟨t, lt_of_le_of_ne ht.2 ?_, (hτ t (hcA ht.1)).symm⟩
      rintro rfl
      exact lt_irrefl _ hs
    · intro t s ht hs h
      obtain ⟨htA, rfl⟩ := transition_eq hδ.injective hτ h
      exact lt_asymm hs (hmono (hleft t htA) ht₀ ht)
  · -- two components: the whole space is a circle
    right
    push Not at hleft
    obtain ⟨t₁, ht₁A, ht₁c⟩ := hleft
    have ht₁c' : t₁ < c := lt_of_le_of_ne ht₁c (fun h => hc (by rw [← h]; exact ht₁A))
    have hIic : Iic t₁ ⊆ γ ⁻¹' range δ :=
      (Iic_or_Ici_subset hγ hδ hτ hτc hWU ht₁A).resolve_right (fun h => hc (h ht₁c))
    obtain ⟨d, ht₁d, hdc, hdA, hd⟩ := exists_right_end hAo ht₁A ht₁c hc
    have hIio : Iio d ⊆ γ ⁻¹' range δ := fun z hz =>
      (le_or_gt z t₁).elim (fun h => hIic h) (fun h => hdA ⟨h.le, hz⟩)
    -- the ray `(-∞, d)` is mapped above `τ t₀`
    have hgt : ∀ t < d, τ t₀ < τ t := by
      intro t ht
      by_contra hle
      push Not at hle
      obtain ⟨t', ht', heq⟩ := hL (τ t) hle
      have := hinj (hcA ht'.1) (hIio ht) heq
      linarith [ht'.1]
    have hRb : ¬ IsBounded (τ '' Ioo t₁ d) :=
      not_isBounded_image hγ.continuous hδ.continuous
        (fun z hz => hτ z (hdA (Ioo_subset_Ico_self hz)))
        (by rw [closure_Ioo ht₁d.ne]; exact right_mem_Icc.2 ht₁d.le) hd
    have hR1 : ¬ BddAbove (τ '' Ioo t₁ d) := by
      refine not_bddAbove_of_not_isBounded hRb ⟨τ t₀, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (hgt z hz.2).le
    have hmono' : StrictMonoOn τ (Iio d) := by
      rcases strictMonoOn_or_strictAntiOn (I := Iio d) ⟨t₁, ht₁d⟩ (hτc.mono hIio) (hinj.mono hIio)
        with hm | hm
      · exact hm
      · refine absurd ⟨τ t₁, ?_⟩ hR1
        rintro _ ⟨z, hz, rfl⟩
        exact (hm ht₁d hz.2 hz.1).le
    have hR : ∀ s ≥ τ t₁, ∃ t ∈ Ico t₁ d, τ t = s := by
      intro s hs
      exact Ici_subset_image isPreconnected_Ico (hτc.mono hdA) ⟨le_rfl, ht₁d⟩
        (fun hb => hR1 (hb.mono (image_mono Ioo_subset_Ico_self))) hs
    refine glue_circle hγ hδ (ht₁c'.trans ht₀) (hgt t₁ ht₁d) (hτ t₀ (hcA ht₀)).symm
      (hτ t₁ (hIio ht₁d)).symm ?_ ?_ ?_
    · intro t ht
      rw [mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with ht | ht
      · refine ⟨τ t, ⟨(hgt t (ht.trans ht₁d)).le, (hmono' (ht.trans ht₁d) ht₁d ht).le⟩,
          hτ t (hIio (ht.trans ht₁d))⟩
      · have htc : c < t := ht₀.trans ht
        refine ⟨τ t, ⟨(hmono ht₀ htc ht).le, ?_⟩, hτ t (hcA htc)⟩
        by_contra hlt
        push Not at hlt
        obtain ⟨t', ht', heq⟩ := hR (τ t) hlt.le
        have := hinj (hdA ht') (hcA htc) heq
        linarith [ht'.2]
    · intro s hs
      rw [mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with hs | hs
      · obtain ⟨t, ht, rfl⟩ := hL s hs.le
        exact ⟨t, ⟨by linarith [ht.1], ht.2⟩, (hτ t (hcA ht.1)).symm⟩
      · obtain ⟨t, ht, rfl⟩ := hR s hs.le
        exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, (hτ t (hdA ht)).symm⟩
    · intro t ht s hs h
      obtain ⟨htA, rfl⟩ := transition_eq hδ.injective hτ h
      rcases lt_or_ge t d with htd | htd
      · exact lt_asymm hs.2 (hmono' ht₁d htd ht.1)
      · rcases lt_or_ge c t with hct | hct
        · exact lt_asymm hs.1 (hmono hct ht₀ ht.2)
        · have htd' : d < t := lt_of_le_of_ne htd (fun h => hd (by rw [h]; exact htA))
          have htc' : t < c := lt_of_le_of_ne hct (fun h => hc (by rw [← h]; exact htA))
          rcases Iic_or_Ici_subset hγ hδ hτ hτc hWU htA with h' | h'
          · exact hd (h' htd'.le)
          · exact hc (h' htc'.le)

/-- **Two arcs, half normalised.** As `two_arcs`, when the domain of the
transition map contains a ray `[t₀, ∞)`. Reflecting `δ` makes the transition
map increasing, reducing to `two_arcs_core`. -/
theorem two_arcs_of_Ici [T2Space V] [ConnectedSpace V] (hloc : LocallyArc V) {γ δ : ℝ → V}
    (hγ : IsOpenEmbedding γ) (hδ : IsOpenEmbedding δ) {τ : ℝ → ℝ}
    (hτ : ∀ t, γ t ∈ range δ → δ (τ t) = γ t) (hτc : ContinuousOn τ (γ ⁻¹' range δ))
    (hWU : ¬ range δ ⊆ range γ) (hUW : ¬ range γ ⊆ range δ) {t₀ : ℝ}
    (ht₀ : Ici t₀ ⊆ γ ⁻¹' range δ) :
    (∃ ε : ℝ → V, IsOpenEmbedding ε ∧ range ε = range γ ∪ range δ) ∨
      Nonempty (V ≃ₜ Circle) := by
  have hAo : IsOpen (γ ⁻¹' range δ) := hδ.isOpen_range.preimage hγ.continuous
  obtain ⟨x, hx⟩ : ∃ x, γ x ∉ range δ := by
    by_contra h
    push Not at h
    exact hUW (by rintro _ ⟨x, rfl⟩; exact h x)
  have hxt : x < t₀ := lt_of_not_ge (fun h => hx (ht₀ h))
  obtain ⟨c, -, hct, hcA, hc⟩ := exists_left_end hAo (ht₀ (le_refl t₀)) hxt.le hx
  have hIoi : Ioi c ⊆ γ ⁻¹' range δ := fun z hz =>
    (le_or_gt z t₀).elim (fun h => hcA ⟨hz, h⟩) (fun h => ht₀ h.le)
  rcases strictMonoOn_or_strictAntiOn (I := Ioi c) ⟨t₀, hct⟩ (hτc.mono hIoi)
    ((transition_injOn hγ.injective hτ).mono hIoi) with hm | hm
  · exact two_arcs_core hloc hγ hδ hτ hτc hWU hc hIoi hm
  · have hr := range_comp_neg δ
    have H := two_arcs_core hloc hγ (isOpenEmbedding_comp_neg hδ) (τ := fun t => -τ t)
      (by intro t ht; rw [hr] at ht; simp only [neg_neg]; exact hτ t ht)
      (by rw [hr]; exact hτc.neg) (by rw [hr]; exact hWU) (by rw [hr]; exact hc)
      (by rw [hr]; exact hIoi) hm.neg
    rwa [hr] at H

/-- **Two arcs.** If the images of two arcs meet and neither contains the
other, then their union is the image of an arc, or the whole (connected,
Hausdorff) space is a circle. -/
theorem two_arcs [T2Space V] [ConnectedSpace V] (hloc : LocallyArc V) {γ δ : ℝ → V}
    (hγ : IsOpenEmbedding γ) (hδ : IsOpenEmbedding δ) (hne : (range γ ∩ range δ).Nonempty)
    (hWU : ¬ range δ ⊆ range γ) (hUW : ¬ range γ ⊆ range δ) :
    (∃ ε : ℝ → V, IsOpenEmbedding ε ∧ range ε = range γ ∪ range δ) ∨
      Nonempty (V ≃ₜ Circle) := by
  obtain ⟨τ, hτ, hτc⟩ := exists_transition hγ.continuous hδ
  obtain ⟨_, ⟨t₀, rfl⟩, ht₀⟩ := hne
  rcases Iic_or_Ici_subset hγ hδ hτ hτc hWU ht₀ with h | h
  · have hr := range_comp_neg γ
    have H := two_arcs_of_Ici hloc (isOpenEmbedding_comp_neg hγ) hδ (τ := fun t => τ (-t))
      (fun t ht => hτ (-t) ht) (hτc.comp continuous_neg.continuousOn fun t ht => ht)
      (by rw [hr]; exact hWU) (by rw [hr]; exact hUW) (t₀ := -t₀)
      (fun t (ht : -t₀ ≤ t) => h (show -t ≤ t₀ from neg_le.2 ht))
    rwa [hr] at H
  · exact two_arcs_of_Ici hloc hγ hδ hτ hτc hWU hUW h

/-! ### The induction on a finite cover by arcs -/

/-- An arc in a compact space is never onto: `ℝ` is not compact. -/
theorem range_ne_univ [CompactSpace V] {γ : ℝ → V} (hγ : IsOpenEmbedding γ) :
    range γ ≠ univ := by
  intro h
  have : IsCompact (univ : Set ℝ) := by
    rw [hγ.isEmbedding.isCompact_iff, image_univ, h]
    exact isCompact_univ
  exact noncompact_univ ℝ this

/-- **Compact connected Hausdorff spaces covered by arcs are circles.** -/
theorem circle_of_locallyArc [T2Space V] [CompactSpace V] [ConnectedSpace V]
    (hloc : LocallyArc V) : Nonempty (V ≃ₜ Circle) := by
  classical
  have hloc' := hloc
  choose arc harc hmem using (hloc' : ∀ x : V, ∃ δ : ℝ → V, IsOpenEmbedding δ ∧ x ∈ range δ)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => range (arc x))
    (fun x => (harc x).isOpen_range) (fun x _ => mem_iUnion.2 ⟨x, hmem x⟩)
  obtain ⟨x₀⟩ : Nonempty V := inferInstance
  suffices H : ∀ s : Finset V, ∀ γ : ℝ → V, IsOpenEmbedding γ →
      (∀ y, y ∈ range γ ∨ ∃ x ∈ s, y ∈ range (arc x)) → Nonempty (V ≃ₜ Circle) by
    refine H s (arc x₀) (harc x₀) fun y => Or.inr ?_
    simpa using hs (mem_univ y)
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro γ hγ hcov
    -- a point on the frontier of the current arc
    have hnc : ¬ IsClosed (range γ) := fun hcl =>
      range_ne_univ hγ (IsClopen.eq_univ ⟨hcl, hγ.isOpen_range⟩ (range_nonempty γ))
    obtain ⟨p, hpcl, hp⟩ : ∃ p ∈ closure (range γ), p ∉ range γ := by
      by_contra h
      push Not at h
      exact hnc (closure_subset_iff_isClosed.1 fun p hp => h p hp)
    obtain ⟨x, hxs, hpx⟩ := (hcov p).resolve_left hp
    have hmeet : (range γ ∩ range (arc x)).Nonempty := by
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hpcl (range (arc x)) (harc x).isOpen_range hpx
      exact ⟨z, hz2, hz1⟩
    have hWU : ¬ range (arc x) ⊆ range γ := fun h => hp (h hpx)
    have hcov' : ∀ R : Set V, range γ ∪ range (arc x) ⊆ R →
        ∀ y, y ∈ R ∨ ∃ x' ∈ s.erase x, y ∈ range (arc x') := by
      intro R hR y
      rcases hcov y with hy | ⟨x', hx', hy⟩
      · exact Or.inl (hR (Or.inl hy))
      · by_cases hxx : x' = x
        · rw [hxx] at hy
          exact Or.inl (hR (Or.inr hy))
        · exact Or.inr ⟨x', Finset.mem_erase.2 ⟨hxx, hx'⟩, hy⟩
    by_cases hUW : range γ ⊆ range (arc x)
    · exact ih _ (Finset.erase_ssubset hxs) (arc x) (harc x)
        (hcov' _ (union_subset hUW subset_rfl))
    · rcases two_arcs hloc hγ (harc x) hmeet hWU hUW with ⟨ε, hε, hεr⟩ | h
      · exact ih _ (Finset.erase_ssubset hxs) ε hε (hcov' _ hεr.symm.subset)
      · exact h

/-! ### Charts give arcs -/

/-- A point in the source of a real-valued chart lies on an arc: pull back a
small open interval around its image. -/
theorem exists_arc_of_openPartialHomeomorph (e : OpenPartialHomeomorph V ℝ) {x : V}
    (hx : x ∈ e.source) : ∃ γ : ℝ → V, IsOpenEmbedding γ ∧ x ∈ range γ := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hx)
  let φ : ℝ ≃o Ioo (-1 : ℝ) 1 := orderIsoIooNegOneOne ℝ
  let ψ : ℝ → ℝ := fun u => e x + r * (φ u : ℝ)
  have hψc : Continuous ψ :=
    continuous_const.add (continuous_const.mul (continuous_subtype_val.comp φ.continuous))
  have hψi : Injective ψ := by
    intro u v h
    apply φ.injective
    apply Subtype.ext
    have h' : r * (φ u : ℝ) = r * (φ v : ℝ) := by
      simpa only [ψ, add_right_inj] using h
    exact mul_left_cancel₀ hr.ne' h'
  have hψ : IsOpenEmbedding ψ := IsOpenEmbedding.of_continuous_injective_isOpenMap hψc hψi
    (isOpenMap_of_injective locallyArc_real hψc hψi)
  have hψt : ∀ u, ψ u ∈ e.target := by
    intro u
    apply hsub
    have h1 : |(φ u : ℝ)| < 1 := abs_lt.2 (φ u).2
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_pos hr]
    calc r * |(φ u : ℝ)| < r * 1 := mul_lt_mul_of_pos_left h1 hr
      _ = r := mul_one r
  refine ⟨fun u => e.symm (ψ u), ?_, ?_⟩
  · refine IsOpenEmbedding.of_continuous_injective_isOpenMap
      (e.continuousOn_symm.comp_continuous hψc hψt) ?_ ?_
    · intro u v h
      apply hψi
      have := congrArg e h
      rwa [e.right_inv (hψt u), e.right_inv (hψt v)] at this
    · intro O hO
      rw [show (fun u => e.symm (ψ u)) '' O = e.symm '' (ψ '' O) from (image_image _ _ _).symm]
      exact e.isOpen_image_symm_of_subset_target (hψ.isOpenMap O hO)
        (by rintro _ ⟨u, -, rfl⟩; exact hψt u)
  · refine ⟨φ.symm ⟨0, by norm_num, by norm_num⟩, ?_⟩
    simp [ψ, e.left_inv hx]

/-- The line `EuclideanSpace ℝ (Fin 1)` is homeomorphic to `ℝ`. -/
noncomputable def euclideanOneHomeomorph : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).toHomeomorph.trans (Homeomorph.funUnique (Fin 1) ℝ)

/-- A topological manifold modelled on `EuclideanSpace ℝ (Fin 1)` is covered by
arcs. -/
theorem locallyArc_of_chartedSpace [ChartedSpace (EuclideanSpace ℝ (Fin 1)) V] :
    LocallyArc V := by
  intro x
  refine exists_arc_of_openPartialHomeomorph
    ((chartAt (EuclideanSpace ℝ (Fin 1)) x).trans
      euclideanOneHomeomorph.toOpenPartialHomeomorph) ?_
  simp

/-! ### The circle -/

/-- Mathlib's unit circle in `ℂ` is homeomorphic to the unit sphere of
`EuclideanSpace ℝ (Fin 2)`, by the isometry `ℂ ≃ ℝ²` of the basis `1, i`. -/
noncomputable def circleHomeomorphSphere :
    Circle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
    show z ∈ Metric.sphere (0 : ℂ) 1 ↔ _
    simp

/-- **Classification of compact connected one-manifolds, topological form.** A
compact connected Hausdorff space with an atlas of charts to
`EuclideanSpace ℝ (Fin 1)` is homeomorphic to the unit circle of `ℝ²`. -/
theorem nonempty_homeomorph_sphere_of_chartedSpace [T2Space V] [CompactSpace V]
    [ConnectedSpace V] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) V] :
    Nonempty (V ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  let ⟨h⟩ := circle_of_locallyArc (locallyArc_of_chartedSpace (V := V))
  ⟨h.trans circleHomeomorphSphere⟩

/-- **Theorem 2.3.2, closed case, up to homeomorphism.** A compact connected
Hausdorff smooth one-manifold is homeomorphic to the unit circle of `ℝ²`. The
statement is exactly that of `Chapter2.classification_dim_one`. The smooth
structure is not used: this is `nonempty_homeomorph_sphere_of_chartedSpace`. -/
theorem classification_dim_one_general {V : Type*} [TopologicalSpace V] [T2Space V]
    [CompactSpace V] [ConnectedSpace V] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) V]
    [IsManifold (𝓡 1) ω V] :
    Nonempty (V ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  nonempty_homeomorph_sphere_of_chartedSpace

end OneManifold
end MorseFloer
