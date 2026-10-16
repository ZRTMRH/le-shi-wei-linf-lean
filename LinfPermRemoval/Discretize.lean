/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.Geometry

/-!
# Tools for Theorem 4.1: discretization, symmetries, and copies of point sets

Auxiliary results used to assemble Theorem 4.1, Corollaries 4.27, 4.37, 4.38 and Theorem 1.2:

* the discretization principle (tex l.633–637, an unnumbered paragraph of the paper);
* invariance of `GeomConclusion` under the dihedral symmetries of the square (reverse,
  complement, inverse of the pattern);
* the correspondence between `σ`-copies in a point set associated with `π` and `σ`-copies of `π`.
-/

open Equiv Finset

namespace LinfPermRemoval

namespace DISC

variable {n k : ℕ}

/-! ## Point sets associated with a permutation -/

theorem represents_injective {π : Perm (Fin n)} {Θ : Fin n → ℝ × ℝ} (h : Represents π Θ) :
    Function.Injective Θ := fun _ _ hij => h.1.injective (congrArg Prod.fst hij)

theorem represents_snd_eq {π : Perm (Fin n)} {Θ : Fin n → ℝ × ℝ} (h : Represents π Θ)
    {i j : Fin n} (e : (Θ i).2 = (Θ j).2) : i = j := by
  apply π.injective
  rcases lt_trichotomy (π i) (π j) with hlt | heq | hgt
  · exact absurd e ((h.2 i j).2 hlt).ne
  · exact heq
  · exact absurd e ((h.2 j i).2 hgt).ne'

theorem isAssoc_card {P : Finset (ℝ × ℝ)} {π : Perm (Fin n)} (h : IsAssoc P π) : P.card = n := by
  obtain ⟨Θ, hΘ, rfl⟩ := h
  rw [card_image_of_injective _ (represents_injective hΘ), card_univ, Fintype.card_fin]

theorem isAssoc_injOn {P : Finset (ℝ × ℝ)} {π : Perm (Fin n)} (h : IsAssoc P π) :
    Set.InjOn Prod.fst (P : Set (ℝ × ℝ)) ∧ Set.InjOn Prod.snd (P : Set (ℝ × ℝ)) := by
  obtain ⟨Θ, hΘ, rfl⟩ := h
  constructor
  · rintro _ hp _ hq e
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hp hq
    obtain ⟨i, rfl⟩ := hp
    obtain ⟨j, rfl⟩ := hq
    rw [hΘ.1.injective e]
  · rintro _ hp _ hq e
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hp hq
    obtain ⟨i, rfl⟩ := hp
    obtain ⟨j, rfl⟩ := hq
    rw [represents_snd_eq hΘ e]

theorem exists_isAssoc_of {P : Finset (ℝ × ℝ)} (hc : P.card = n) (hx : Set.InjOn Prod.fst (P : Set (ℝ × ℝ)))
    (hy : Set.InjOn Prod.snd (P : Set (ℝ × ℝ))) : ∃ π : Perm (Fin n), IsAssoc P π := by
  classical
  have hX : (P.image Prod.fst).card = n := by rw [card_image_of_injOn hx, hc]
  have hY : (P.image Prod.snd).card = n := by rw [card_image_of_injOn hy, hc]
  set ex := (P.image Prod.fst).orderEmbOfFin hX
  set ey := (P.image Prod.snd).orderEmbOfFin hY
  have hmem : ∀ i, ∃ p ∈ P, p.1 = ex i := fun i => by
    have := (P.image Prod.fst).orderEmbOfFin_mem hX i
    simp only [mem_image] at this
    exact this
  choose Θ hΘP hΘx using hmem
  have hΘinj : Function.Injective Θ := fun i j e => ex.injective (by rw [← hΘx, ← hΘx, e])
  have hrank : ∀ i, ∃ j, ey j = (Θ i).2 := fun i => by
    have h1 : (Θ i).2 ∈ (↑(P.image Prod.snd) : Set ℝ) := by
      rw [coe_image]; exact Set.mem_image_of_mem _ (hΘP i)
    rw [← range_orderEmbOfFin _ hY] at h1
    exact h1
  choose f hf using hrank
  have finj : Function.Injective f := by
    intro i j e
    have h1 : (Θ i).2 = (Θ j).2 := by rw [← hf, ← hf, e]
    exact hΘinj (hy (hΘP i) (hΘP j) h1)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp finj), Θ, ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    simp only [hΘx]
    exact ex.strictMono hij
  · intro i j
    simp only [Equiv.ofBijective_apply]
    rw [← hf i, ← hf j]
    exact ey.lt_iff_lt
  · symm
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      simp only [mem_image, mem_univ, true_and] at hp
      obtain ⟨i, rfl⟩ := hp
      exact hΘP i
    · rw [card_image_of_injective _ hΘinj, card_univ, Fintype.card_fin, hc]

/-- `P` is associated with some permutation of length `n` iff it has `n` points with pairwise
distinct `x`- and `y`-coordinates. -/
theorem exists_isAssoc_iff (P : Finset (ℝ × ℝ)) (n : ℕ) :
    (∃ π : Perm (Fin n), IsAssoc P π) ↔
      P.card = n ∧ Set.InjOn Prod.fst (P : Set (ℝ × ℝ)) ∧ Set.InjOn Prod.snd (P : Set (ℝ × ℝ)) := by
  constructor
  · rintro ⟨π, h⟩
    exact ⟨isAssoc_card h, isAssoc_injOn h⟩
  · rintro ⟨h1, h2, h3⟩
    exact exists_isAssoc_of h1 h2 h3

theorem isPermPointSet_iff (P : Finset (ℝ × ℝ)) :
    IsPermPointSet P ↔ Set.InjOn Prod.fst (P : Set (ℝ × ℝ)) ∧ Set.InjOn Prod.snd (P : Set (ℝ × ℝ)) := by
  unfold IsPermPointSet
  rw [exists_isAssoc_iff]
  simp

/-! ## The canonical point set -/

theorem canonPt_fst (σ : Perm (Fin k)) (i : Fin k) : (canonPt σ i).1 = (i : ℝ) + 1 := rfl
theorem canonPt_snd (σ : Perm (Fin k)) (i : Fin k) : (canonPt σ i).2 = ((σ i : ℕ) : ℝ) + 1 := rfl

theorem canonPt_strictMono (σ : Perm (Fin k)) : StrictMono fun i => (canonPt σ i).1 := by
  intro i j h
  simp only [canonPt_fst]
  have : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast h
  linarith

theorem represents_canonPt (σ : Perm (Fin k)) : Represents σ (canonPt σ) := by
  refine ⟨canonPt_strictMono σ, fun i j => ?_⟩
  simp only [canonPt_snd, add_lt_add_iff_right, Nat.cast_lt, Fin.val_fin_lt]

theorem isAssoc_canon (σ : Perm (Fin k)) : IsAssoc (canon σ) σ :=
  ⟨canonPt σ, represents_canonPt σ, rfl⟩

theorem canon_card (σ : Perm (Fin k)) : (canon σ).card = k := isAssoc_card (isAssoc_canon σ)

theorem mem_canon {σ : Perm (Fin k)} {p : ℝ × ℝ} : p ∈ canon σ ↔ ∃ i, canonPt σ i = p := by
  simp [canon]

/-! ## Segments -/

/-- An open segment with non-axis-parallel direction contains a point avoiding finitely many
`x`- and `y`-coordinates. -/
theorem exists_openSeg_avoid (a v : ℝ × ℝ) (hv1 : v.1 ≠ 0) (hv2 : v.2 ≠ 0) (F G : Finset ℝ) :
    ∃ p ∈ openSeg a v, p.1 ∉ F ∧ p.2 ∉ G := by
  classical
  set B : Finset ℝ := F.image (fun f => (f - a.1) / v.1) ∪ G.image (fun g => (g - a.2) / v.2)
  obtain ⟨t, ⟨ht0, ht1⟩, htB⟩ :=
    ((Set.Ioo_infinite (zero_lt_one' ℝ)).sdiff B.finite_toSet).nonempty
  refine ⟨(a.1 + t * v.1, a.2 + t * v.2), ⟨t, ht0, ht1, rfl⟩, fun hF => htB ?_, fun hG => htB ?_⟩
  · simp only [B, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe]
    left; exact ⟨_, hF, by field_simp; ring⟩
  · simp only [B, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe]
    right; exact ⟨_, hG, by field_simp; ring⟩

/-- An open segment whose two endpoints lie in the closed stripe `[i, i+1]` (in `y`) and which is
not horizontal lies in the open stripe `H_i`. -/
theorem openSeg_subset_hStripe (a v : ℝ × ℝ) (i : ℕ) (hv : v.2 ≠ 0) (h1 : (i : ℝ) ≤ a.2)
    (h2 : a.2 ≤ (i : ℝ) + 1) (h3 : (i : ℝ) ≤ a.2 + v.2) (h4 : a.2 + v.2 ≤ (i : ℝ) + 1) :
    openSeg a v ⊆ hStripe i := by
  rintro _ ⟨t, ht0, ht1, rfl⟩
  rcases lt_or_gt_of_ne hv with hv | hv
  · constructor <;> simp only <;> nlinarith
  · constructor <;> simp only <;> nlinarith

/-- An open segment whose two endpoints lie in the closed stripe `[i, i+1]` (in `x`) and which is
not vertical lies in the open stripe `V_i`. -/
theorem openSeg_subset_vStripe (a v : ℝ × ℝ) (i : ℕ) (hv : v.1 ≠ 0) (h1 : (i : ℝ) ≤ a.1)
    (h2 : a.1 ≤ (i : ℝ) + 1) (h3 : (i : ℝ) ≤ a.1 + v.1) (h4 : a.1 + v.1 ≤ (i : ℝ) + 1) :
    openSeg a v ⊆ vStripe i := by
  rintro _ ⟨t, ht0, ht1, rfl⟩
  rcases lt_or_gt_of_ne hv with hv | hv
  · constructor <;> simp only <;> nlinarith
  · constructor <;> simp only <;> nlinarith

/-- The open sub-segment `a + (s, s+c) v` lies in the closed segment `a + [0, T] v`. -/
theorem openSeg_subset_closedSeg (a v : ℝ × ℝ) (s c T : ℝ) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hT : s + c ≤ T) :
    openSeg (a.1 + s * v.1, a.2 + s * v.2) (c * v.1, c * v.2) ⊆ closedSeg a v T := by
  rintro _ ⟨t, ht0, ht1, rfl⟩
  refine ⟨s + t * c, by positivity, by nlinarith, ?_⟩
  simp only [Prod.mk.injEq]; constructor <;> ring

theorem notMem_lattice_of_hStripe {p : ℝ × ℝ} {i : ℕ} (h : p ∈ hStripe i) : p ∉ lattice := by
  rintro ⟨a, b, rfl⟩
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  have h1' : (i : ℤ) < b := by exact_mod_cast h1
  have h2' : b < (i : ℤ) + 1 := by exact_mod_cast h2
  omega

theorem notMem_lattice_of_vStripe {p : ℝ × ℝ} {i : ℕ} (h : p ∈ vStripe i) : p ∉ lattice := by
  rintro ⟨a, b, rfl⟩
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  have h1' : (i : ℤ) < a := by exact_mod_cast h1
  have h2' : a < (i : ℤ) + 1 := by exact_mod_cast h2
  omega

/-! ## Greedy choice of the new points -/

/-- The number of `s < m` with `s % M = t` (for `t < M`: with `s ≡ t (mod M)`). -/
def cnt (M m t : ℕ) : ℕ := ((Finset.range m).filter (fun s => s % M = t)).card

theorem cnt_zero (M t : ℕ) : cnt M 0 t = 0 := by simp [cnt]

theorem cnt_succ (M m t : ℕ) : cnt M (m + 1) t = cnt M m t + if m % M = t then 1 else 0 := by
  unfold cnt
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · simp

theorem div_le_cnt {M m t : ℕ} (hM : 0 < M) (ht : t < M) : m / M ≤ cnt M m t := by
  have hsub : (Finset.range (m / M)).image (fun j => t + M * j) ⊆
      (Finset.range m).filter (fun s => s % M = t) := by
    intro s hs
    simp only [mem_image, mem_range] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    simp only [mem_filter, mem_range]
    refine ⟨?_, ?_⟩
    · have h1 : M * (j + 1) ≤ M * (m / M) := Nat.mul_le_mul_left _ hj
      have h2 : M * (m / M) ≤ m := Nat.mul_div_le m M
      nlinarith
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  have hinj : Function.Injective (fun j => t + M * j) := by
    intro a b h
    simp only [add_right_inj] at h
    exact Nat.eq_of_mul_eq_mul_left hM h
  calc m / M = ((Finset.range (m / M)).image (fun j => t + M * j)).card := by
        rw [card_image_of_injective _ hinj, card_range]
    _ ≤ _ := card_le_card hsub

open Classical in
/-- Greedy round-robin choice: point number `s` goes to the set `S (s mod M)`, avoiding all
coordinates used before. -/
theorem greedy (C : Finset (ℝ × ℝ)) (hCx : Set.InjOn Prod.fst (C : Set (ℝ × ℝ)))
    (hCy : Set.InjOn Prod.snd (C : Set (ℝ × ℝ))) (M : ℕ) (hM : 0 < M) (S : ℕ → Set (ℝ × ℝ))
    (hS : ∀ t < M, ∀ F G : Finset ℝ, ∃ p ∈ S t, p.1 ∉ F ∧ p.2 ∉ G) (m : ℕ) :
    ∃ Q : Finset (ℝ × ℝ), Disjoint C Q ∧ Q.card = m ∧
      Set.InjOn Prod.fst ((C ∪ Q : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) ∧
      Set.InjOn Prod.snd ((C ∪ Q : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) ∧
      (∀ q ∈ Q, ∃ t < M, q ∈ S t) ∧
      ∀ t < M, cnt M m t ≤ (Q.filter (· ∈ S t)).card := by
  classical
  induction m with
  | zero =>
    refine ⟨∅, disjoint_empty_right _, rfl, by simpa using hCx, by simpa using hCy,
      by simp, fun t _ => by simp [cnt_zero]⟩
  | succ m ih =>
    obtain ⟨Q, hdis, hcard, hx, hy, hQS, hcnt⟩ := ih
    obtain ⟨p, hpS, hpx, hpy⟩ :=
      hS (m % M) (Nat.mod_lt _ hM) ((C ∪ Q).image Prod.fst) ((C ∪ Q).image Prod.snd)
    have hpCQ : p ∉ C ∪ Q := fun h => hpx (mem_image_of_mem _ h)
    have hpC : p ∉ C := fun h => hpCQ (mem_union_left _ h)
    have hpQ : p ∉ Q := fun h => hpCQ (mem_union_right _ h)
    have hins : C ∪ insert p Q = insert p (C ∪ Q) := by
      ext q; simp only [mem_union, mem_insert]; tauto
    refine ⟨insert p Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [disjoint_insert_right]; exact ⟨hpC, hdis⟩
    · rw [card_insert_of_notMem hpQ, hcard]
    · rw [hins, coe_insert, Set.injOn_insert (by exact_mod_cast hpCQ)]
      refine ⟨hx, fun h => hpx ?_⟩
      rw [mem_image]; obtain ⟨q, hq, e⟩ := h; exact ⟨q, hq, e⟩
    · rw [hins, coe_insert, Set.injOn_insert (by exact_mod_cast hpCQ)]
      refine ⟨hy, fun h => hpy ?_⟩
      rw [mem_image]; obtain ⟨q, hq, e⟩ := h; exact ⟨q, hq, e⟩
    · intro q hq
      rw [mem_insert] at hq
      rcases hq with rfl | hq
      · exact ⟨m % M, Nat.mod_lt _ hM, hpS⟩
      · exact hQS q hq
    · intro t ht
      rw [cnt_succ, filter_insert]
      have := hcnt t ht
      split_ifs with h1 h2
      · rw [card_insert_of_notMem (fun h => hpQ (mem_filter.1 h).1)]; omega
      · exact absurd (h1 ▸ hpS) h2
      · calc cnt M m t + 0 ≤ (Q.filter (· ∈ S t)).card := by omega
          _ ≤ _ := card_le_card (subset_insert _ _)
      · omega

/-! ## The discretization principle (tex l.633–637) -/

/-- The threshold of the discretization: `N₀(k) = k + 2k(k-1)`, the paper's `N - k ≥ 2k(k-1)`. -/
def N0 (k : ℕ) : ℕ := k + 2 * k * (k - 1)

/-- `GeomConclusion` is monotone in the threshold. -/
theorem GeomConclusion.mono {σ : Perm (Fin k)} {N₀ N₁ : ℕ} (h : GeomConclusion σ N₀)
    (hle : N₀ ≤ N₁) : GeomConclusion σ N₁ := fun N hN => h N (le_trans hle hN)

/-- `⌊m / (2(k-1))⌋ ≥ m / (2k)` once `m ≥ 2k(k-1)` (tex l.637). -/
theorem stripe_bound_nat {k m : ℕ} (hk : 2 ≤ k) (hm : 2 * k * (k - 1) ≤ m) :
    m ≤ 2 * k * (m / (2 * (k - 1))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hm ⊢
  have hM : 0 < 2 * j := by omega
  have hq : j + 1 ≤ m / (2 * j) := by
    rw [Nat.le_div_iff_mul_le hM]; nlinarith
  have hdm := Nat.div_add_mod m (2 * j)
  have hr := Nat.mod_lt m hM
  set q := m / (2 * j)
  set r := m % (2 * j)
  nlinarith

open Classical in
/-- **Discretization (tex l.633–637).** For `k ≥ 2`: if every stripe `H_i`, `V_i`
(`i ∈ [k-1]`) contains a non-axis-parallel open segment inside `D`, and every point set
associated with a permutation with `Σ ⊆ Π ⊆ Σ ∪ D` has `Σ` as its unique `σ`-copy, then the
conclusion of Theorem 4.1 holds for `σ` with threshold `N₀(k) = k + 2k(k-1)`. -/
theorem geomConclusion_of_segs (σ : Perm (Fin k)) (hk : 2 ≤ k) (D : Set (ℝ × ℝ))
    (hH : ∀ i, 1 ≤ i → i ≤ k - 1 → ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧
      openSeg a v ⊆ D ∧ openSeg a v ⊆ hStripe i)
    (hV : ∀ i, 1 ≤ i → i ≤ k - 1 → ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧
      openSeg a v ⊆ D ∧ openSeg a v ⊆ vStripe i)
    (huniq : ∀ P : Finset (ℝ × ℝ), IsPermPointSet P → (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
      (↑P : Set (ℝ × ℝ)) ⊆ ↑(canon σ) ∪ D → IsUniqueCopy σ ↑P) :
    GeomConclusion σ (N0 k) := by
  have hH' : ∀ i, ∃ a v : ℝ × ℝ, 1 ≤ i → i ≤ k - 1 → v.1 ≠ 0 ∧ v.2 ≠ 0 ∧
      openSeg a v ⊆ D ∧ openSeg a v ⊆ hStripe i := by
    intro i
    by_cases h : 1 ≤ i ∧ i ≤ k - 1
    · obtain ⟨a, v, hv⟩ := hH i h.1 h.2; exact ⟨a, v, fun _ _ => hv⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  have hV' : ∀ i, ∃ a v : ℝ × ℝ, 1 ≤ i → i ≤ k - 1 → v.1 ≠ 0 ∧ v.2 ≠ 0 ∧
      openSeg a v ⊆ D ∧ openSeg a v ⊆ vStripe i := by
    intro i
    by_cases h : 1 ≤ i ∧ i ≤ k - 1
    · obtain ⟨a, v, hv⟩ := hV i h.1 h.2; exact ⟨a, v, fun _ _ => hv⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose aH vH hHP using hH'
  choose aV vV hVP using hV'
  set M := 2 * (k - 1) with hMdef
  have hM : 0 < M := by omega
  let S : ℕ → Set (ℝ × ℝ) := fun t =>
    if t < k - 1 then openSeg (aH (t + 1)) (vH (t + 1))
    else openSeg (aV (t - (k - 1) + 1)) (vV (t - (k - 1) + 1))
  have hS : ∀ t < M, ∀ F G : Finset ℝ, ∃ p ∈ S t, p.1 ∉ F ∧ p.2 ∉ G := by
    intro t ht F G
    by_cases h : t < k - 1
    · obtain ⟨h1, h2, -, -⟩ := hHP (t + 1) (by omega) (by omega)
      simp only [S, h, ↓reduceIte]; exact exists_openSeg_avoid _ _ h1 h2 F G
    · obtain ⟨h1, h2, -, -⟩ := hVP (t - (k - 1) + 1) (by omega) (by omega)
      simp only [S, h, ↓reduceIte]; exact exists_openSeg_avoid _ _ h1 h2 F G
  have hSD : ∀ t < M, S t ⊆ D := by
    intro t ht
    by_cases h : t < k - 1
    · simp only [S, h, ↓reduceIte]; exact (hHP (t + 1) (by omega) (by omega)).2.2.1
    · simp only [S, h, ↓reduceIte]; exact (hVP (t - (k - 1) + 1) (by omega) (by omega)).2.2.1
  have hSH : ∀ i, 1 ≤ i → i ≤ k - 1 → S (i - 1) ⊆ hStripe i := by
    intro i h1 h2
    have h : i - 1 < k - 1 := by omega
    have e : i - 1 + 1 = i := by omega
    simp only [S, h, ↓reduceIte, e]
    exact (hHP i h1 h2).2.2.2
  have hSV : ∀ i, 1 ≤ i → i ≤ k - 1 → S (k - 1 + (i - 1)) ⊆ vStripe i := by
    intro i h1 h2
    have h : ¬ (k - 1 + (i - 1) < k - 1) := by omega
    have e : k - 1 + (i - 1) - (k - 1) + 1 = i := by omega
    simp only [S, h, ↓reduceIte, e]
    exact (hVP i h1 h2).2.2.2
  obtain ⟨hCx, hCy⟩ := isAssoc_injOn (isAssoc_canon σ)
  intro N hN
  have hNk : N0 k ≤ N := hN
  unfold N0 at hNk
  obtain ⟨Q, hdis, hcard, hx, hy, hQS, hcnt⟩ := greedy (canon σ) hCx hCy M hM S hS (N - k)
  have hcardP : (canon σ ∪ Q).card = N := by
    rw [card_union_of_disjoint hdis, canon_card, hcard]; omega
  obtain ⟨π, hπ⟩ := exists_isAssoc_of hcardP hx hy
  refine ⟨canon σ ∪ Q, π, hπ, ?_, ?_⟩
  · apply huniq
    · exact (isPermPointSet_iff _).2 ⟨hx, hy⟩
    · rw [coe_union]; exact Set.subset_union_left
    · intro p hp
      rw [coe_union] at hp
      rcases hp with hp | hp
      · exact Or.inl hp
      · obtain ⟨t, ht, hpt⟩ := hQS p hp
        exact Or.inr (hSD t ht hpt)
  · intro i h1 h2
    have hb := stripe_bound_nat hk (m := N - k) (by omega)
    set q := (N - k) / M
    have hreal : ((N : ℝ) - k) / (2 * k) ≤ (q : ℝ) := by
      have hb' : ((N - k : ℕ) : ℝ) ≤ 2 * k * (q : ℝ) := by exact_mod_cast hb
      rw [Nat.cast_sub (by omega)] at hb'
      rw [div_le_iff₀ (by positivity)]
      linarith
    constructor
    · refine hreal.trans ?_
      have h3 : q ≤ cnt M (N - k) (i - 1) := div_le_cnt hM (by omega)
      have h4 := hcnt (i - 1) (by omega)
      have h5 : (Q.filter (· ∈ S (i - 1))).card ≤
          ((canon σ ∪ Q).filter (· ∈ hStripe i)).card := by
        apply card_le_card
        intro p hp
        rw [mem_filter] at hp ⊢
        exact ⟨mem_union_right _ hp.1, hSH i h1 h2 hp.2⟩
      exact_mod_cast h3.trans (h4.trans h5)
    · refine hreal.trans ?_
      have h3 : q ≤ cnt M (N - k) (k - 1 + (i - 1)) := div_le_cnt hM (by omega)
      have h4 := hcnt (k - 1 + (i - 1)) (by omega)
      have h5 : (Q.filter (· ∈ S (k - 1 + (i - 1)))).card ≤
          ((canon σ ∪ Q).filter (· ∈ vStripe i)).card := by
        apply card_le_card
        intro p hp
        rw [mem_filter] at hp ⊢
        exact ⟨mem_union_right _ hp.1, hSV i h1 h2 hp.2⟩
      exact_mod_cast h3.trans (h4.trans h5)

/-- **Discretization**, form for supports `D ⊇ Σ` (Constructions 4.15, 4.19, 4.28, 4.39). -/
theorem geomConclusion_of_segs' (σ : Perm (Fin k)) (hk : 2 ≤ k) (D : Set (ℝ × ℝ))
    (hD : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ D)
    (hH : ∀ i, 1 ≤ i → i ≤ k - 1 → ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧
      openSeg a v ⊆ D ∧ openSeg a v ⊆ hStripe i)
    (hV : ∀ i, 1 ≤ i → i ≤ k - 1 → ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧
      openSeg a v ⊆ D ∧ openSeg a v ⊆ vStripe i)
    (huniq : ∀ P : Finset (ℝ × ℝ), IsPermPointSet P → (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
      (↑P : Set (ℝ × ℝ)) ⊆ D → IsUniqueCopy σ ↑P) :
    GeomConclusion σ (N0 k) :=
  geomConclusion_of_segs σ hk D hH hV fun P h1 h2 h3 =>
    huniq P h1 h2 (h3.trans (Set.union_subset hD le_rfl))

/-! ## From the geometric conclusion to Theorem 1.2 -/

/-- Two listings of the same finite set, both strictly increasing in `x`, coincide. -/
theorem eq_of_image_eq {f g : Fin k → ℝ × ℝ} (hf : StrictMono fun i => (f i).1)
    (hg : StrictMono fun i => (g i).1) (h : univ.image f = univ.image g) : f = g := by
  classical
  set s := (univ.image f).image Prod.fst
  have hs : s.card = k := by
    simp only [s, image_image]
    rw [card_image_of_injective _ (show Function.Injective (Prod.fst ∘ f) from hf.injective),
      card_univ, Fintype.card_fin]
  have e1 := orderEmbOfFin_unique hs (f := fun i => (f i).1)
    (fun i => mem_image_of_mem _ (mem_image_of_mem _ (mem_univ i))) hf
  have e2 := orderEmbOfFin_unique hs (f := fun i => (g i).1)
    (fun i => by simp only [s, h]; exact mem_image_of_mem _ (mem_image_of_mem _ (mem_univ i))) hg
  have hx : ∀ i, (f i).1 = (g i).1 := fun i => by
    have := congrFun (e1.trans e2.symm) i; exact this
  funext i
  have hi : f i ∈ univ.image g := h ▸ mem_image_of_mem _ (mem_univ i)
  obtain ⟨j, -, hj⟩ := mem_image.1 hi
  have : j = i := hg.injective (show (g j).1 = (g i).1 by rw [hj, hx i])
  rw [← hj, this]

theorem image_univ_orderEmbOfFin {α : Type*} {S : Finset (Fin n)} (h : S.card = k)
    (Θ : Fin n → α) [DecidableEq α] :
    univ.image (fun a => Θ (S.orderEmbOfFin h a)) = S.image Θ := by
  conv_rhs => rw [← image_orderEmbOfFin_univ S h]
  rw [image_image]; rfl

/-- A copy `S` of `σ` in `π` gives a copy of `σ` in a representation of `π`. -/
theorem represents_comp {σ : Perm (Fin k)} {π : Perm (Fin n)} {Θ : Fin n → ℝ × ℝ}
    (hΘ : Represents π Θ) {S : Finset (Fin n)} (h : S.card = k)
    (hS : ∀ a b : Fin k, π (S.orderEmbOfFin h a) < π (S.orderEmbOfFin h b) ↔ σ a < σ b) :
    Represents σ (fun a => Θ (S.orderEmbOfFin h a)) := by
  refine ⟨fun a b hab => hΘ.1 ((S.orderEmbOfFin h).strictMono hab), fun a b => ?_⟩
  rw [hΘ.2, hS]

/-- The positions of the canonical points in a representation. -/
noncomputable def canonIdx (σ : Perm (Fin k)) (Θ : Fin n → ℝ × ℝ) : Finset (Fin n) := by
  classical exact univ.filter fun i => Θ i ∈ canon σ

theorem mem_canonIdx {σ : Perm (Fin k)} {Θ : Fin n → ℝ × ℝ} {i : Fin n} :
    i ∈ canonIdx σ Θ ↔ Θ i ∈ canon σ := by
  classical
  unfold canonIdx; convert mem_filter (s := univ) (p := fun i => Θ i ∈ canon σ) using 1; simp

theorem canonIdx_image {σ : Perm (Fin k)} {Θ : Fin n → ℝ × ℝ}
    (hc : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑(univ.image Θ)) :
    (canonIdx σ Θ).image Θ = canon σ := by
  ext p
  simp only [mem_image, mem_canonIdx]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hp
    have := hc hp
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at this
    obtain ⟨i, rfl⟩ := this
    exact ⟨i, hp, rfl⟩

theorem canonIdx_card {σ : Perm (Fin k)} {π : Perm (Fin n)} {Θ : Fin n → ℝ × ℝ}
    (hΘ : Represents π Θ) (hc : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑(univ.image Θ)) :
    (canonIdx σ Θ).card = k := by
  have e := congrArg Finset.card (canonIdx_image hc)
  rw [card_image_of_injective _ (represents_injective hΘ), canon_card] at e
  exact e

theorem canonIdx_comp {σ : Perm (Fin k)} {π : Perm (Fin n)} {Θ : Fin n → ℝ × ℝ}
    (hΘ : Represents π Θ) (hc : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑(univ.image Θ)) :
    (fun a => Θ ((canonIdx σ Θ).orderEmbOfFin (canonIdx_card hΘ hc) a)) = canonPt σ := by
  apply eq_of_image_eq
  · exact fun a b hab => hΘ.1 ((orderEmbOfFin _ _).strictMono hab)
  · exact canonPt_strictMono σ
  · rw [image_univ_orderEmbOfFin, canonIdx_image hc]; rfl

theorem isCopy_canonIdx {σ : Perm (Fin k)} {π : Perm (Fin n)} {Θ : Fin n → ℝ × ℝ}
    (hΘ : Represents π Θ) (hc : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑(univ.image Θ)) :
    IsCopy σ π (canonIdx σ Θ) := by
  refine ⟨canonIdx_card hΘ hc, fun a b => ?_⟩
  rw [← hΘ.2]
  have e := canonIdx_comp hΘ hc
  have ea := congrFun e a
  have eb := congrFun e b
  rw [ea, eb]
  exact (represents_canonPt σ).2 a b

/-- If `Π` is associated with `π` and `Σ` is the unique `σ`-copy in `Π`, then `π` has exactly
one `σ`-copy. -/
theorem numCopies_eq_one {σ : Perm (Fin k)} {π : Perm (Fin n)} {P : Finset (ℝ × ℝ)}
    (hP : IsAssoc P π) (hU : IsUniqueCopy σ ↑P) : numCopies σ π = 1 := by
  classical
  obtain ⟨Θ, hΘ, rfl⟩ := hP
  unfold numCopies
  rw [card_eq_one]
  refine ⟨canonIdx σ Θ, ?_⟩
  ext S
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨h, hS⟩
    have hrep := represents_comp hΘ h hS
    have himg := hU.2 _ ⟨hrep, fun a => by
      simp only [coe_image, coe_univ, Set.image_univ]; exact Set.mem_range_self _⟩
    rw [image_univ_orderEmbOfFin] at himg
    ext i
    rw [mem_canonIdx]
    constructor
    · intro hi; rw [← himg]; exact mem_image_of_mem _ hi
    · intro hi
      rw [← himg, mem_image] at hi
      obtain ⟨j, hj, e⟩ := hi
      rwa [← represents_injective hΘ e]
  · rintro rfl
    exact isCopy_canonIdx hΘ hU.1

open Classical in
/-- Rank gap in `x`: if `Θ(i)_x ≤ c` and `Θ(j)_x ≥ c+1`, the positions `i < j` differ by more
than the number of points in `V_c`. -/
theorem gap_x {π : Perm (Fin n)} {Θ : Fin n → ℝ × ℝ} (hΘ : Represents π Θ) (i j : Fin n) (c : ℕ)
    (hi : (Θ i).1 ≤ c) (hj : (c : ℝ) + 1 ≤ (Θ j).1) :
    (((univ.image Θ).filter (· ∈ vStripe c)).card : ℝ) + 1 ≤ ((j : ℕ) : ℝ) - (i : ℕ) := by
  have hij : i < j := hΘ.1.lt_iff_lt.1 (by linarith)
  have hsub : (univ.image Θ).filter (· ∈ vStripe c) ⊆ (Ioo i j).image Θ := by
    intro p hp
    simp only [mem_filter, mem_image, mem_univ, true_and] at hp
    obtain ⟨⟨m, rfl⟩, h1, h2⟩ := hp
    refine mem_image_of_mem _ (mem_Ioo.2 ⟨hΘ.1.lt_iff_lt.1 ?_, hΘ.1.lt_iff_lt.1 ?_⟩)
    · show (Θ i).1 < (Θ m).1; linarith
    · show (Θ m).1 < (Θ j).1; linarith
  have h1 := (card_le_card hsub).trans card_image_le
  rw [Fin.card_Ioo] at h1
  have h2 : (i : ℕ) < j := hij
  have h3 : ((univ.image Θ).filter (· ∈ vStripe c)).card + 1 + (i : ℕ) ≤ j := by omega
  have h4 : (((univ.image Θ).filter (· ∈ vStripe c)).card : ℝ) + 1 + (i : ℕ) ≤ (j : ℕ) := by
    exact_mod_cast h3
  linarith

open Classical in
/-- Rank gap in `y`: if `Θ(i)_y ≤ c` and `Θ(j)_y ≥ c+1`, the values `π(i) < π(j)` differ by more
than the number of points in `H_c`. -/
theorem gap_y {π : Perm (Fin n)} {Θ : Fin n → ℝ × ℝ} (hΘ : Represents π Θ) (i j : Fin n) (c : ℕ)
    (hi : (Θ i).2 ≤ c) (hj : (c : ℝ) + 1 ≤ (Θ j).2) :
    (((univ.image Θ).filter (· ∈ hStripe c)).card : ℝ) + 1 ≤ ((π j : ℕ) : ℝ) - (π i : ℕ) := by
  have hij : π i < π j := (hΘ.2 i j).1 (by linarith)
  have hsub : (univ.image Θ).filter (· ∈ hStripe c) ⊆
      (Ioo (π i) (π j)).image (fun m => Θ (π.symm m)) := by
    intro p hp
    simp only [mem_filter, mem_image, mem_univ, true_and] at hp
    obtain ⟨⟨m, rfl⟩, h1, h2⟩ := hp
    refine mem_image.2 ⟨π m, mem_Ioo.2 ⟨(hΘ.2 _ _).1 ?_, (hΘ.2 _ _).1 ?_⟩, by simp⟩
    · show (Θ i).2 < (Θ m).2; linarith
    · show (Θ m).2 < (Θ j).2; linarith
  have h1 := (card_le_card hsub).trans card_image_le
  rw [Fin.card_Ioo] at h1
  have h2 : (π i : ℕ) < π j := hij
  have h3 : ((univ.image Θ).filter (· ∈ hStripe c)).card + 1 + (π i : ℕ) ≤ π j := by omega
  have h4 : (((univ.image Θ).filter (· ∈ hStripe c)).card : ℝ) + 1 + (π i : ℕ) ≤ (π j : ℕ) := by
    exact_mod_cast h3
  linarith

theorem natCast_fin_lt {a b : Fin k} (h : a < b) : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by
  have : (a : ℕ) + 1 ≤ b := h
  exact_mod_cast this

open Classical in
/-- The stripe bounds of Theorem 4.1 and Fact 2.4 give `1/(8k)`-farness from `σ`-freeness.
Thanks to the `+1` in the rank gap, no lower bound on `N` beyond `N ≥ 2` is needed. -/
theorem isFarFromFree_of_stripes (σ : Perm (Fin k)) (hk : 2 ≤ k) {N : ℕ} (hN : 2 ≤ N)
    (P : Finset (ℝ × ℝ)) (π : Perm (Fin N)) (hP : IsAssoc P π) (hc : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P)
    (hs : ∀ i : ℕ, 1 ≤ i → i ≤ k - 1 →
      ((N : ℝ) - k) / (2 * k) ≤ ((P.filter (· ∈ hStripe i)).card : ℝ) ∧
      ((N : ℝ) - k) / (2 * k) ≤ ((P.filter (· ∈ vStripe i)).card : ℝ)) :
    IsFarFromFree (1 / (8 * k)) σ π := by
  obtain ⟨Θ, hΘ, rfl⟩ := hP
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkey : 2 * (1 / (8 * (k : ℝ))) * ((N : ℝ) - 1) ≤ ((N : ℝ) - k) / (2 * k) + 1 := by
    have e : ((N : ℝ) - k) / (2 * k) + 1 - 2 * (1 / (8 * (k : ℝ))) * ((N : ℝ) - 1) =
        ((N : ℝ) + 2 * k + 1) / (4 * k) := by field_simp; ring
    have : 0 ≤ ((N : ℝ) + 2 * k + 1) / (4 * k) := by positivity
    linarith
  have hcan : ∀ i ∈ canonIdx σ Θ, ∃ a, Θ i = canonPt σ a := fun i hi => by
    obtain ⟨a, ha⟩ := mem_canon.1 (mem_canonIdx.1 hi); exact ⟨a, ha.symm⟩
  -- the x-separation and the y-separation for an ordered pair
  have hx : ∀ i j : Fin N, ∀ a b : Fin k, Θ i = canonPt σ a → Θ j = canonPt σ b → a < b →
      ((N : ℝ) - k) / (2 * k) + 1 ≤ ((j : ℕ) : ℝ) - (i : ℕ) := by
    intro i j a b hi hj hab
    have h1 := gap_x hΘ i j ((a : ℕ) + 1) (by rw [hi, canonPt_fst]; push_cast; rfl)
      (by rw [hj, canonPt_fst]; have := natCast_fin_lt hab; push_cast; linarith)
    have h2 := (hs ((a : ℕ) + 1) (by omega) (by have := b.isLt; omega)).2
    linarith
  have hy : ∀ i j : Fin N, ∀ a b : Fin k, Θ i = canonPt σ a → Θ j = canonPt σ b → σ a < σ b →
      ((N : ℝ) - k) / (2 * k) + 1 ≤ ((π j : ℕ) : ℝ) - (π i : ℕ) := by
    intro i j a b hi hj hab
    have h1 := gap_y hΘ i j ((σ a : ℕ) + 1) (by rw [hi, canonPt_snd]; push_cast; rfl)
      (by rw [hj, canonPt_snd]; have := natCast_fin_lt hab; push_cast; linarith)
    have h2 := (hs ((σ a : ℕ) + 1) (by omega) (by have := (σ b).isLt; omega)).1
    linarith
  refine fact_2_4 σ π (canonIdx σ Θ) _ (by positivity) hN (isCopy_canonIdx hΘ hc) ?_
  intro i hi j hj hij
  obtain ⟨a, ha⟩ := hcan i hi
  obtain ⟨b, hb⟩ := hcan j hj
  have hab : a ≠ b := fun e => hij (represents_injective hΘ (by rw [ha, hb, e]))
  constructor
  · refine hkey.trans ?_
    rcases lt_or_gt_of_ne hab with h | h
    · rw [abs_sub_comm]; exact (hx i j a b ha hb h).trans (le_abs_self _)
    · exact (hx j i b a hb ha h).trans (le_abs_self _)
  · refine hkey.trans ?_
    have hσ : σ a ≠ σ b := fun e => hab (σ.injective e)
    rcases lt_or_gt_of_ne hσ with h | h
    · rw [abs_sub_comm]; exact (hy i j a b ha hb h).trans (le_abs_self _)
    · exact (hy j i b a hb ha h).trans (le_abs_self _)

theorem length_oneLine (σ : Perm (Fin k)) : (oneLine σ).length = k := by simp [oneLine]

/-- The patterns of Theorems 1.2 and 4.1 have length at least `3`. -/
theorem thmHyp_three_le {σ : Perm (Fin k)} (h : ThmHyp σ) : 3 ≤ k := by
  rcases h with h | h | h
  · omega
  · have := congrArg List.length h; rw [length_oneLine] at this; simp at this; omega
  · have := congrArg List.length h; rw [length_oneLine] at this; simp at this; omega

/-- **Theorem 4.1 implies Theorem 1.2** (tex l.618–625). The statement only asserts that
`n₀` and `ε_σ` exist; the proof takes `ε_σ = 1/(8k)` and `n₀ = max(N₀, 2)`. -/
theorem thm_1_2_of_geom (k : ℕ)
    (h : ∃ N₀ : ℕ, ∀ σ : Perm (Fin k), ThmHyp σ → GeomConclusion σ N₀) :
    ∃ n₀ : ℕ, ∀ σ : Perm (Fin k), ThmHyp σ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ n ≥ n₀, ∃ π : Perm (Fin n),
        IsFarFromFree ε σ π ∧ numCopies σ π = 1 := by
  obtain ⟨N₀, hN₀⟩ := h
  refine ⟨max N₀ 2, fun σ hσ => ⟨1 / (8 * k), ?_, fun n hn => ?_⟩⟩
  · have := thmHyp_three_le hσ
    have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  · obtain ⟨P, π, hP, hU, hs⟩ := hN₀ σ hσ n (le_of_max_le_left hn)
    exact ⟨π, isFarFromFree_of_stripes σ (by have := thmHyp_three_le hσ; omega)
      (le_of_max_le_right hn) P π hP hU.1 hs, numCopies_eq_one hP hU⟩

/-! ## Dihedral symmetries of patterns -/

/-- The reverse of `σ`: `revP σ (i) = σ(k+1-i)` (0-based: `σ (Fin.rev i)`). -/
def revP (σ : Perm (Fin k)) : Perm (Fin k) := Fin.revPerm.trans σ

/-- The complement of `σ`: `compP σ (i) = k+1-σ(i)` (0-based: `Fin.rev (σ i)`). -/
def compP (σ : Perm (Fin k)) : Perm (Fin k) := σ.trans Fin.revPerm

/-- The inverse of `σ`. -/
def invP (σ : Perm (Fin k)) : Perm (Fin k) := σ.symm

@[simp] theorem revP_apply (σ : Perm (Fin k)) (i : Fin k) : revP σ i = σ (Fin.rev i) := rfl
@[simp] theorem compP_apply (σ : Perm (Fin k)) (i : Fin k) : compP σ i = Fin.rev (σ i) := rfl

@[simp] theorem revP_symm_apply (σ : Perm (Fin k)) (j : Fin k) :
    (revP σ).symm j = Fin.rev (σ.symm j) := by
  apply (revP σ).injective; simp

@[simp] theorem compP_symm_apply (σ : Perm (Fin k)) (j : Fin k) :
    (compP σ).symm j = σ.symm (Fin.rev j) := by
  apply (compP σ).injective; simp

@[simp] theorem revP_revP (σ : Perm (Fin k)) : revP (revP σ) = σ := by ext i; simp
@[simp] theorem compP_compP (σ : Perm (Fin k)) : compP (compP σ) = σ := by ext i; simp
@[simp] theorem invP_invP (σ : Perm (Fin k)) : invP (invP σ) = σ := by ext i; simp [invP]

/-- The reflection `(x, y) ↦ (k+1-x, y)` (reverse). -/
def reflX (k : ℕ) (p : ℝ × ℝ) : ℝ × ℝ := ((k : ℝ) + 1 - p.1, p.2)

/-- The reflection `(x, y) ↦ (x, k+1-y)` (complement). -/
def reflY (k : ℕ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, (k : ℝ) + 1 - p.2)

theorem reflX_involutive (k : ℕ) : Function.Involutive (reflX k) := fun p => by
  simp only [reflX, sub_sub_cancel]

theorem reflY_involutive (k : ℕ) : Function.Involutive (reflY k) := fun p => by
  simp only [reflY, sub_sub_cancel]

theorem image_univ_comp_perm {α : Type*} [DecidableEq α] (g : Fin k → α) (e : Perm (Fin k)) :
    univ.image (fun i => g (e i)) = univ.image g := by
  ext p
  simp only [mem_image, mem_univ, true_and]
  exact ⟨fun ⟨i, h⟩ => ⟨e i, h⟩, fun ⟨i, h⟩ => ⟨e.symm i, by simp [h]⟩⟩

open Classical in
theorem card_filter_image_of_involutive {f : ℝ × ℝ → ℝ × ℝ} (hf : Function.Involutive f)
    (P : Finset (ℝ × ℝ)) (A B : Set (ℝ × ℝ)) (hAB : ∀ p, f p ∈ A ↔ p ∈ B) :
    ((P.image f).filter (· ∈ A)).card = (P.filter (· ∈ B)).card := by
  rw [filter_image, card_image_of_injective _ hf.injective]
  congr 1
  exact filter_congr fun p _ => hAB p

open Classical in
/-- **Generic transfer of the conclusion of Theorem 4.1** along an involutive plane map `f` that
preserves "distinct coordinates", sends `Σ_σ` to `Σ_τ`, pulls `τ`-copies back to `σ`-copies, and
permutes the stripes `H_i`, `V_i` (`i ∈ [k-1]`). -/
theorem geomConclusion_transfer {σ τ : Perm (Fin k)} {N₀ : ℕ} (f : ℝ × ℝ → ℝ × ℝ)
    (hf : Function.Involutive f)
    (hinj : ∀ P : Finset (ℝ × ℝ), Set.InjOn Prod.fst (P : Set (ℝ × ℝ)) →
      Set.InjOn Prod.snd (P : Set (ℝ × ℝ)) →
      Set.InjOn Prod.fst ((P.image f : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) ∧
      Set.InjOn Prod.snd ((P.image f : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)))
    (hcanon : (canon σ).image f = canon τ)
    (hcopy : ∀ Θ : Fin k → ℝ × ℝ, Represents τ Θ →
      ∃ Θ' : Fin k → ℝ × ℝ, Represents σ Θ' ∧ univ.image Θ' = (univ.image Θ).image f)
    (hstrH : ∀ i, 1 ≤ i → i ≤ k - 1 → ∃ j, 1 ≤ j ∧ j ≤ k - 1 ∧
      ((∀ p, f p ∈ hStripe i ↔ p ∈ hStripe j) ∨ (∀ p, f p ∈ hStripe i ↔ p ∈ vStripe j)))
    (hstrV : ∀ i, 1 ≤ i → i ≤ k - 1 → ∃ j, 1 ≤ j ∧ j ≤ k - 1 ∧
      ((∀ p, f p ∈ vStripe i ↔ p ∈ hStripe j) ∨ (∀ p, f p ∈ vStripe i ↔ p ∈ vStripe j)))
    (h : GeomConclusion σ N₀) : GeomConclusion τ N₀ := by
  intro N hN
  obtain ⟨P, π, hP, hU, hs⟩ := h N hN
  have hff : ∀ s : Finset (ℝ × ℝ), (s.image f).image f = s := fun s => by
    rw [image_image, hf.comp_self, image_id]
  obtain ⟨hx, hy⟩ := isAssoc_injOn hP
  obtain ⟨hx', hy'⟩ := hinj P hx hy
  obtain ⟨π', hπ'⟩ := exists_isAssoc_of
    (by rw [card_image_of_injective _ hf.injective, isAssoc_card hP]) hx' hy'
  refine ⟨P.image f, π', hπ', ⟨?_, ?_⟩, ?_⟩
  · rw [← hcanon, coe_image, coe_image]; exact Set.image_mono hU.1
  · intro Θ hΘ
    obtain ⟨Θ', hΘ', himg⟩ := hcopy Θ hΘ.1
    have hin : ∀ i, Θ' i ∈ P := fun i => by
      have h1 : Θ' i ∈ univ.image Θ' := mem_image_of_mem _ (mem_univ i)
      rw [himg, mem_image] at h1
      obtain ⟨q, hq, e0⟩ := h1
      rw [← e0]
      obtain ⟨j, -, rfl⟩ := mem_image.1 hq
      have h2 := hΘ.2 j
      simp only [coe_image, Set.mem_image, mem_coe] at h2
      obtain ⟨p, hp, e⟩ := h2
      rw [← e, hf p]; exact hp
    have hc := hU.2 Θ' ⟨hΘ', hin⟩
    rw [← hff (univ.image Θ), ← himg, hc, hcanon]
  · intro i h1 h2
    constructor
    · obtain ⟨j, hj1, hj2, hj | hj⟩ := hstrH i h1 h2
      · rw [card_filter_image_of_involutive hf P _ _ hj]; exact (hs j hj1 hj2).1
      · rw [card_filter_image_of_involutive hf P _ _ hj]; exact (hs j hj1 hj2).2
    · obtain ⟨j, hj1, hj2, hj | hj⟩ := hstrV i h1 h2
      · rw [card_filter_image_of_involutive hf P _ _ hj]; exact (hs j hj1 hj2).1
      · rw [card_filter_image_of_involutive hf P _ _ hj]; exact (hs j hj1 hj2).2

theorem val_rev_add (i : Fin k) : ((Fin.rev i : ℕ) : ℝ) = (k : ℝ) - 1 - (i : ℕ) := by
  have h := Fin.val_rev i
  have : (Fin.rev i : ℕ) + (i : ℕ) + 1 = k := by omega
  have : ((Fin.rev i : ℕ) : ℝ) + (i : ℕ) + 1 = k := by exact_mod_cast this
  linarith

theorem canon_revP (σ : Perm (Fin k)) : (canon σ).image (reflX k) = canon (revP σ) := by
  unfold canon
  rw [image_image, ← image_univ_comp_perm (canonPt (revP σ)) Fin.revPerm]
  congr 1
  funext i
  simp only [Function.comp_apply, reflX, canonPt, Fin.revPerm_apply, revP_apply, Fin.rev_rev,
    val_rev_add, Prod.mk.injEq, and_true]
  ring

theorem canon_compP (σ : Perm (Fin k)) : (canon σ).image (reflY k) = canon (compP σ) := by
  unfold canon
  rw [image_image]
  congr 1
  funext i
  simp only [Function.comp_apply, reflY, canonPt, compP_apply, val_rev_add, Prod.mk.injEq,
    true_and]
  ring

theorem canon_invP (σ : Perm (Fin k)) : (canon σ).image Prod.swap = canon (invP σ) := by
  unfold canon
  rw [image_image, ← image_univ_comp_perm (canonPt (invP σ)) σ]
  congr 1
  funext i
  simp [canonPt, invP]

/-- Stripe bookkeeping for `reflX`. -/
theorem reflX_mem_vStripe {i : ℕ} (hi : i ≤ k) (p : ℝ × ℝ) :
    reflX k p ∈ vStripe i ↔ p ∈ vStripe (k - i) := by
  simp only [reflX, vStripe, Set.mem_ofPred_eq, Nat.cast_sub hi]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem reflY_mem_hStripe {i : ℕ} (hi : i ≤ k) (p : ℝ × ℝ) :
    reflY k p ∈ hStripe i ↔ p ∈ hStripe (k - i) := by
  simp only [reflY, hStripe, Set.mem_ofPred_eq, Nat.cast_sub hi]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Reverse.** The conclusion of Theorem 4.1 transfers from `σ` to its reverse. -/
theorem geomConclusion_revP {σ : Perm (Fin k)} {N₀ : ℕ} (h : GeomConclusion σ N₀) :
    GeomConclusion (revP σ) N₀ := by
  refine geomConclusion_transfer (reflX k) (reflX_involutive k) ?_ (canon_revP σ) ?_ ?_ ?_ h
  · intro P hx hy
    rw [coe_image]
    constructor
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ e
      have : p.1 = q.1 := by simp only [reflX] at e; linarith
      rw [hx hp hq this]
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ e
      rw [hy hp hq e]
  · intro Θ hΘ
    refine ⟨fun i => reflX k (Θ (Fin.rev i)), ⟨fun i j hij => ?_, fun i j => ?_⟩, ?_⟩
    · have := hΘ.1 (Fin.rev_lt_rev.2 hij)
      simp only [reflX]; linarith
    · simp only [reflX]; rw [hΘ.2]; simp
    · rw [image_image]
      exact image_univ_comp_perm (reflX k ∘ Θ) Fin.revPerm
  · intro i h1 h2
    exact ⟨i, h1, h2, Or.inl fun p => Iff.rfl⟩
  · intro i h1 h2
    refine ⟨k - i, by omega, by omega, Or.inr (reflX_mem_vStripe (by omega))⟩

/-- **Complement.** The conclusion of Theorem 4.1 transfers from `σ` to its complement. -/
theorem geomConclusion_compP {σ : Perm (Fin k)} {N₀ : ℕ} (h : GeomConclusion σ N₀) :
    GeomConclusion (compP σ) N₀ := by
  refine geomConclusion_transfer (reflY k) (reflY_involutive k) ?_ (canon_compP σ) ?_ ?_ ?_ h
  · intro P hx hy
    rw [coe_image]
    constructor
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ e
      rw [hx hp hq e]
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ e
      have : p.2 = q.2 := by simp only [reflY] at e; linarith
      rw [hy hp hq this]
  · intro Θ hΘ
    refine ⟨fun i => reflY k (Θ i), ⟨fun i j hij => hΘ.1 hij, fun i j => ?_⟩, ?_⟩
    · simp only [reflY, sub_lt_sub_iff_left]; rw [hΘ.2]; simp [Fin.rev_lt_rev]
    · rw [image_image]; rfl
  · intro i h1 h2
    exact ⟨k - i, by omega, by omega, Or.inl (reflY_mem_hStripe (by omega))⟩
  · intro i h1 h2
    exact ⟨i, h1, h2, Or.inr fun p => Iff.rfl⟩

/-- **Inverse.** The conclusion of Theorem 4.1 transfers from `σ` to its inverse. -/
theorem geomConclusion_invP {σ : Perm (Fin k)} {N₀ : ℕ} (h : GeomConclusion σ N₀) :
    GeomConclusion (invP σ) N₀ := by
  refine geomConclusion_transfer Prod.swap (fun p => Prod.swap_swap p) ?_ (canon_invP σ) ?_ ?_ ?_ h
  · intro P hx hy
    rw [coe_image]
    constructor
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ e
      rw [hy hp hq e]
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ e
      rw [hx hp hq e]
  · intro Θ hΘ
    refine ⟨fun j => Prod.swap (Θ (σ j)), ⟨fun i j hij => ?_, fun i j => ?_⟩, ?_⟩
    · simp only [Prod.fst_swap]; rw [hΘ.2]; simpa [invP] using hij
    · simp only [Prod.snd_swap]; exact hΘ.1.lt_iff_lt
    · rw [image_image]
      exact image_univ_comp_perm (Prod.swap ∘ Θ) σ
  · intro i h1 h2
    exact ⟨i, h1, h2, Or.inr fun p => Iff.rfl⟩
  · intro i h1 h2
    exact ⟨i, h1, h2, Or.inl fun p => Iff.rfl⟩

/-! ## The 1-based accessors under the symmetries -/

theorem sval_eq (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    sval σ i = (σ ⟨i - 1, by omega⟩ : ℕ) + 1 := by
  simp only [sval, h1, h2, and_self, ↓reduceDIte]

theorem spos_eq (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    spos σ j = (σ.symm ⟨j - 1, by omega⟩ : ℕ) + 1 := by
  simp only [spos, h1, h2, and_self, ↓reduceDIte]

theorem sval_le (σ : Perm (Fin k)) (i : ℕ) : sval σ i ≤ k := by
  unfold sval; split_ifs
  · have := (σ ⟨i - 1, by omega⟩).isLt; omega
  · omega

theorem spos_le (σ : Perm (Fin k)) (j : ℕ) : spos σ j ≤ k := by
  unfold spos; split_ifs
  · have := (σ.symm ⟨j - 1, by omega⟩).isLt; omega
  · omega

theorem one_le_sval (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) : 1 ≤ sval σ i := by
  rw [sval_eq σ h1 h2]; omega

theorem one_le_spos (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) : 1 ≤ spos σ j := by
  rw [spos_eq σ h1 h2]; omega

/-- `σ⁻¹(j) = i ↔ σ(i) = j` (1-based, both in range). -/
theorem spos_eq_iff (σ : Perm (Fin k)) {i j : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ k) (hj1 : 1 ≤ j)
    (hj2 : j ≤ k) : spos σ j = i ↔ sval σ i = j := by
  rw [spos_eq σ hj1 hj2, sval_eq σ hi1 hi2]
  constructor
  · intro h
    have e : σ.symm ⟨j - 1, by omega⟩ = ⟨i - 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [Equiv.symm_apply_eq] at e
    rw [← e]; simp only; omega
  · intro h
    have e : σ ⟨i - 1, by omega⟩ = ⟨j - 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [← Equiv.eq_symm_apply] at e
    rw [← e]; simp only; omega

theorem spos_sval (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    spos σ (sval σ i) = i :=
  (spos_eq_iff σ h1 h2 (one_le_sval σ h1 h2) (sval_le σ i)).2 rfl

theorem sval_spos (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    sval σ (spos σ j) = j :=
  (spos_eq_iff σ (one_le_spos σ h1 h2) (spos_le σ j) h1 h2).1 rfl

theorem sval_revP (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    sval (revP σ) i = sval σ (k + 1 - i) := by
  rw [sval_eq _ h1 h2, sval_eq _ (by omega) (by omega), revP_apply,
    show Fin.rev (⟨i - 1, by omega⟩ : Fin k) = ⟨k + 1 - i - 1, by omega⟩ from
      Fin.ext (by simp [Fin.val_rev]; omega)]

theorem sval_compP (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    sval (compP σ) i = k + 1 - sval σ i := by
  rw [sval_eq _ h1 h2, sval_eq _ h1 h2, compP_apply, Fin.val_rev]
  have := (σ ⟨i - 1, by omega⟩).isLt
  omega

theorem sval_invP (σ : Perm (Fin k)) (i : ℕ) : sval (invP σ) i = spos σ i := rfl

theorem spos_invP (σ : Perm (Fin k)) (j : ℕ) : spos (invP σ) j = sval σ j := rfl

theorem spos_revP (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    spos (revP σ) j = k + 1 - spos σ j := by
  rw [spos_eq _ h1 h2, spos_eq _ h1 h2, revP_symm_apply, Fin.val_rev]
  have := (σ.symm ⟨j - 1, by omega⟩).isLt
  omega

theorem spos_compP (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    spos (compP σ) j = spos σ (k + 1 - j) := by
  rw [spos_eq _ h1 h2, spos_eq _ (by omega) (by omega), compP_symm_apply,
    show Fin.rev (⟨j - 1, by omega⟩ : Fin k) = ⟨k + 1 - j - 1, by omega⟩ from
      Fin.ext (by simp [Fin.val_rev]; omega)]

theorem lv_revP (σ : Perm (Fin k)) : lv (revP σ) = rv σ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [lv, rv, sval]
  · rw [lv, rv, sval_revP σ le_rfl hk, Nat.add_sub_cancel]

theorem rv_revP (σ : Perm (Fin k)) : rv (revP σ) = lv σ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [lv, rv, sval]
  · rw [lv, rv, sval_revP σ hk le_rfl]; congr 1; omega

theorem bp_revP (σ : Perm (Fin k)) (hk : 1 ≤ k) : bp (revP σ) = k + 1 - bp σ := by
  rw [bp, bp, spos_revP σ le_rfl hk]

theorem up_revP (σ : Perm (Fin k)) (hk : 1 ≤ k) : up (revP σ) = k + 1 - up σ := by
  rw [up, up, spos_revP σ hk le_rfl]

theorem lv_compP (σ : Perm (Fin k)) (hk : 1 ≤ k) : lv (compP σ) = k + 1 - lv σ := by
  rw [lv, lv, sval_compP σ le_rfl hk]

theorem rv_compP (σ : Perm (Fin k)) (hk : 1 ≤ k) : rv (compP σ) = k + 1 - rv σ := by
  rw [rv, rv, sval_compP σ hk le_rfl]

theorem bp_compP (σ : Perm (Fin k)) : bp (compP σ) = up σ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [bp, up, spos]
  · rw [bp, up, spos_compP σ le_rfl hk, Nat.add_sub_cancel]

theorem up_compP (σ : Perm (Fin k)) : up (compP σ) = bp σ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [bp, up, spos]
  · rw [bp, up, spos_compP σ hk le_rfl]; congr 1; omega

theorem lv_invP (σ : Perm (Fin k)) : lv (invP σ) = bp σ := rfl
theorem rv_invP (σ : Perm (Fin k)) : rv (invP σ) = up σ := rfl
theorem bp_invP (σ : Perm (Fin k)) : bp (invP σ) = lv σ := rfl
theorem up_invP (σ : Perm (Fin k)) : up (invP σ) = rv σ := rfl

/-- `b = 1 ↔ ℓ = 1`. -/
theorem bp_eq_one_iff (σ : Perm (Fin k)) : bp σ = 1 ↔ lv σ = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [bp, lv, spos, sval]
  · exact spos_eq_iff σ le_rfl hk le_rfl hk

/-- `b = k ↔ r = 1`. -/
theorem bp_eq_k_iff (σ : Perm (Fin k)) (hk : 1 ≤ k) : bp σ = k ↔ rv σ = 1 :=
  spos_eq_iff σ hk le_rfl le_rfl hk

/-- `u = 1 ↔ ℓ = k`. -/
theorem up_eq_one_iff (σ : Perm (Fin k)) (hk : 1 ≤ k) : up σ = 1 ↔ lv σ = k :=
  spos_eq_iff σ le_rfl hk hk le_rfl

/-- `u = k ↔ r = k`. -/
theorem up_eq_k_iff (σ : Perm (Fin k)) (hk : 1 ≤ k) : up σ = k ↔ rv σ = k :=
  spos_eq_iff σ hk le_rfl hk le_rfl

/-! ## The pattern families under the symmetries -/

theorem isTwoBlockA_revP {σ : Perm (Fin k)} {ℓ : ℕ} (h : IsTwoBlockA σ ℓ) :
    IsTwoBlockB (revP σ) ℓ := by
  obtain ⟨h1, h2, h⟩ := h
  refine ⟨h1, h2, fun i hi1 hi2 => ?_⟩
  rw [sval_revP σ hi1 hi2, h (k + 1 - i) (by omega) (by omega)]
  split_ifs <;> omega

theorem isTwoBlockB_revP {σ : Perm (Fin k)} {r : ℕ} (h : IsTwoBlockB σ r) :
    IsTwoBlockA (revP σ) r := by
  obtain ⟨h1, h2, h⟩ := h
  refine ⟨h1, h2, fun i hi1 hi2 => ?_⟩
  rw [sval_revP σ hi1 hi2, h (k + 1 - i) (by omega) (by omega)]
  split_ifs <;> omega

theorem isTwoBlockA_compP {σ : Perm (Fin k)} {ℓ : ℕ} (h : IsTwoBlockA σ ℓ) :
    IsTwoBlockB (compP σ) (k - ℓ) := by
  obtain ⟨h1, h2, h⟩ := h
  refine ⟨by omega, by omega, fun i hi1 hi2 => ?_⟩
  rw [sval_compP σ hi1 hi2, h i hi1 hi2]
  split_ifs <;> omega

theorem isTwoBlockB_compP {σ : Perm (Fin k)} {r : ℕ} (h : IsTwoBlockB σ r) :
    IsTwoBlockA (compP σ) (k - r) := by
  obtain ⟨h1, h2, h⟩ := h
  refine ⟨by omega, by omega, fun i hi1 hi2 => ?_⟩
  rw [sval_compP σ hi1 hi2, h i hi1 hi2]
  split_ifs <;> omega

theorem isTwoBlockA_invP {σ : Perm (Fin k)} {ℓ : ℕ} (h : IsTwoBlockA σ ℓ) :
    IsTwoBlockA (invP σ) ℓ := by
  obtain ⟨h1, h2, h⟩ := h
  refine ⟨h1, h2, fun j hj1 hj2 => ?_⟩
  rw [sval_invP]
  by_cases hj : j ≤ ℓ
  · have hh : ℓ + 1 - j ≤ ℓ := by omega
    simp only [hj, ↓reduceIte]
    rw [spos_eq_iff σ (by omega) (by omega) hj1 hj2, h _ (by omega) (by omega)]
    split_ifs; omega
  · have hh : ¬ (k + ℓ + 1 - j ≤ ℓ) := by omega
    simp only [hj, ↓reduceIte]
    rw [spos_eq_iff σ (by omega) (by omega) hj1 hj2, h _ (by omega) (by omega)]
    split_ifs; omega

theorem isTwoBlockB_invP {σ : Perm (Fin k)} {r : ℕ} (h : IsTwoBlockB σ r) :
    IsTwoBlockB (invP σ) (k - r) := by
  obtain ⟨h1, h2, h⟩ := h
  refine ⟨by omega, by omega, fun j hj1 hj2 => ?_⟩
  rw [sval_invP]
  by_cases hj : j ≤ k - (k - r)
  · have hh : ¬ (k - r + j ≤ k - r) := by omega
    simp only [hj, ↓reduceIte]
    rw [spos_eq_iff σ (by omega) (by omega) hj1 hj2, h _ (by omega) (by omega)]
    split_ifs; omega
  · have hh : j - r ≤ k - r := by omega
    simp only [hj, ↓reduceIte]
    rw [spos_eq_iff σ (by omega) (by omega) hj1 hj2, h _ (by omega) (by omega)]
    split_ifs <;> omega

theorem isTwoBlock_revP {σ : Perm (Fin k)} (h : IsTwoBlock σ) : IsTwoBlock (revP σ) := by
  rcases h with ⟨ℓ, h⟩ | ⟨r, h⟩
  · exact Or.inr ⟨ℓ, isTwoBlockA_revP h⟩
  · exact Or.inl ⟨r, isTwoBlockB_revP h⟩

theorem isTwoBlock_compP {σ : Perm (Fin k)} (h : IsTwoBlock σ) : IsTwoBlock (compP σ) := by
  rcases h with ⟨ℓ, h⟩ | ⟨r, h⟩
  · exact Or.inr ⟨_, isTwoBlockA_compP h⟩
  · exact Or.inl ⟨_, isTwoBlockB_compP h⟩

theorem isTwoBlock_invP {σ : Perm (Fin k)} (h : IsTwoBlock σ) : IsTwoBlock (invP σ) := by
  rcases h with ⟨ℓ, h⟩ | ⟨r, h⟩
  · exact Or.inl ⟨_, isTwoBlockA_invP h⟩
  · exact Or.inr ⟨_, isTwoBlockB_invP h⟩

theorem isTwoBlock_revP_iff (σ : Perm (Fin k)) : IsTwoBlock (revP σ) ↔ IsTwoBlock σ :=
  ⟨fun h => by simpa using isTwoBlock_revP h, isTwoBlock_revP⟩

theorem isTwoBlock_compP_iff (σ : Perm (Fin k)) : IsTwoBlock (compP σ) ↔ IsTwoBlock σ :=
  ⟨fun h => by simpa using isTwoBlock_compP h, isTwoBlock_compP⟩

theorem isTwoBlock_invP_iff (σ : Perm (Fin k)) : IsTwoBlock (invP σ) ↔ IsTwoBlock σ :=
  ⟨fun h => by simpa using isTwoBlock_invP h, isTwoBlock_invP⟩

theorem oneLine_injective {σ τ : Perm (Fin k)} (h : oneLine σ = oneLine τ) : σ = τ := by
  unfold oneLine at h
  rw [List.ofFn_inj] at h
  ext i
  have := congrFun h i
  omega

/-- An explicit permutation of `Fin 5` from its values and inverse values. -/
def mk5 (f g : Fin 5 → Fin 5) (h1 : Function.LeftInverse g f)
    (h2 : Function.RightInverse g f) : Perm (Fin 5) := ⟨f, g, h1, h2⟩

def e31524 : Perm (Fin 5) := mk5 ![2, 0, 4, 1, 3] ![1, 3, 0, 4, 2] (by decide) (by decide)
def e24153 : Perm (Fin 5) := mk5 ![1, 3, 0, 4, 2] ![2, 0, 4, 1, 3] (by decide) (by decide)
def e42513 : Perm (Fin 5) := mk5 ![3, 1, 4, 0, 2] ![3, 1, 4, 0, 2] (by decide) (by decide)
def e35142 : Perm (Fin 5) := mk5 ![2, 4, 0, 3, 1] ![2, 4, 0, 3, 1] (by decide) (by decide)

theorem isExcFive_cases {σ : Perm (Fin k)} (h : IsExcFive σ) :
    ∃ hk : k = 5, (hk ▸ σ) = e31524 ∨ (hk ▸ σ) = e24153 ∨ (hk ▸ σ) = e42513 ∨
      (hk ▸ σ) = e35142 := by
  have hk : k = 5 := by
    unfold IsExcFive at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;>
    · have := congrArg List.length h; rw [length_oneLine] at this; simpa using this
  subst hk
  refine ⟨rfl, ?_⟩
  unfold IsExcFive at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h
  · exact Or.inl (oneLine_injective (h.trans (by decide)))
  · exact Or.inr (Or.inl (oneLine_injective (h.trans (by decide))))
  · exact Or.inr (Or.inr (Or.inl (oneLine_injective (h.trans (by decide)))))
  · exact Or.inr (Or.inr (Or.inr (oneLine_injective (h.trans (by decide)))))

theorem isExcFive_revP {σ : Perm (Fin k)} (h : IsExcFive σ) : IsExcFive (revP σ) := by
  obtain ⟨rfl, h | h | h | h⟩ := isExcFive_cases h <;> subst h <;> unfold IsExcFive <;> decide

theorem isExcFive_compP {σ : Perm (Fin k)} (h : IsExcFive σ) : IsExcFive (compP σ) := by
  obtain ⟨rfl, h | h | h | h⟩ := isExcFive_cases h <;> subst h <;> unfold IsExcFive <;> decide

theorem isExcFive_invP {σ : Perm (Fin k)} (h : IsExcFive σ) : IsExcFive (invP σ) := by
  obtain ⟨rfl, h | h | h | h⟩ := isExcFive_cases h <;> subst h <;> unfold IsExcFive <;> decide

theorem isExcFive_revP_iff (σ : Perm (Fin k)) : IsExcFive (revP σ) ↔ IsExcFive σ :=
  ⟨fun h => by simpa using isExcFive_revP h, isExcFive_revP⟩

theorem isExcFive_compP_iff (σ : Perm (Fin k)) : IsExcFive (compP σ) ↔ IsExcFive σ :=
  ⟨fun h => by simpa using isExcFive_compP h, isExcFive_compP⟩

theorem isExcFive_invP_iff (σ : Perm (Fin k)) : IsExcFive (invP σ) ↔ IsExcFive σ :=
  ⟨fun h => by simpa using isExcFive_invP h, isExcFive_invP⟩

theorem thmHyp_cases {σ : Perm (Fin k)} (h : ThmHyp σ) :
    4 ≤ k ∨ ∃ hk : k = 3, (hk ▸ σ) = 1 ∨ (hk ▸ σ) = Fin.revPerm := by
  rcases h with h | h | h
  · exact Or.inl h
  · have hk : k = 3 := by
      have := congrArg List.length h; rw [length_oneLine] at this; simpa using this
    subst hk
    exact Or.inr ⟨rfl, Or.inl (oneLine_injective (h.trans (by decide)))⟩
  · have hk : k = 3 := by
      have := congrArg List.length h; rw [length_oneLine] at this; simpa using this
    subst hk
    exact Or.inr ⟨rfl, Or.inr (oneLine_injective (h.trans (by decide)))⟩

theorem thmHyp_revP {σ : Perm (Fin k)} (h : ThmHyp σ) : ThmHyp (revP σ) := by
  rcases thmHyp_cases h with h | ⟨rfl, h | h⟩
  · exact Or.inl h
  · subst h; unfold ThmHyp; decide
  · subst h; unfold ThmHyp; decide

theorem thmHyp_compP {σ : Perm (Fin k)} (h : ThmHyp σ) : ThmHyp (compP σ) := by
  rcases thmHyp_cases h with h | ⟨rfl, h | h⟩
  · exact Or.inl h
  · subst h; unfold ThmHyp; decide
  · subst h; unfold ThmHyp; decide

/-! ## The anti-diagonal reflection (reduction of Corollary 4.38 to Corollary 4.37)

The reflection `(x, y) ↦ (k+1-y, k+1-x)` in the anti-diagonal sends `Σ_σ` to `Σ_{antiD σ}`
with `antiD σ = compP (revP (invP σ))`, i.e. `antiD σ (j) = k+1-σ⁻¹(k+1-j)`. It exchanges
`ℓ ↔ k+1-u`, `r ↔ k+1-b`, and turns (LD) into (UD) and (RD) into (BD). -/

/-- The anti-diagonal reflection of a pattern (0-based, by unfolding:
`antiD σ i = Fin.rev (σ.symm (Fin.rev i))`). -/
def antiD (σ : Perm (Fin k)) : Perm (Fin k) := compP (revP (invP σ))

@[simp] theorem antiD_antiD (σ : Perm (Fin k)) : antiD (antiD σ) = σ := by
  ext i; simp [antiD, invP]

theorem geomConclusion_antiD {σ : Perm (Fin k)} {N₀ : ℕ} (h : GeomConclusion σ N₀) :
    GeomConclusion (antiD σ) N₀ :=
  geomConclusion_compP (geomConclusion_revP (geomConclusion_invP h))

theorem geomConclusion_of_antiD {σ : Perm (Fin k)} {N₀ : ℕ} (h : GeomConclusion (antiD σ) N₀) :
    GeomConclusion σ N₀ := by
  have := geomConclusion_antiD h; rwa [antiD_antiD] at this

theorem spos_antiD (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    spos (antiD σ) j = k + 1 - sval σ (k + 1 - j) := by
  rw [antiD, spos_compP _ h1 h2, spos_revP _ (by omega) (by omega), spos_invP]

theorem lv_antiD (σ : Perm (Fin k)) (hk : 1 ≤ k) : lv (antiD σ) = k + 1 - up σ := by
  rw [antiD, lv_compP _ hk, lv_revP, rv_invP]

theorem rv_antiD (σ : Perm (Fin k)) (hk : 1 ≤ k) : rv (antiD σ) = k + 1 - bp σ := by
  rw [antiD, rv_compP _ hk, rv_revP, lv_invP]

theorem bp_antiD (σ : Perm (Fin k)) (hk : 1 ≤ k) : bp (antiD σ) = k + 1 - rv σ := by
  rw [antiD, bp_compP, up_revP _ hk, up_invP]

theorem up_antiD (σ : Perm (Fin k)) (hk : 1 ≤ k) : up (antiD σ) = k + 1 - lv σ := by
  rw [antiD, up_compP, bp_revP _ hk, bp_invP]

theorem isTwoBlock_antiD_iff (σ : Perm (Fin k)) : IsTwoBlock (antiD σ) ↔ IsTwoBlock σ := by
  rw [antiD, isTwoBlock_compP_iff, isTwoBlock_revP_iff, isTwoBlock_invP_iff]

theorem isExcFive_antiD_iff (σ : Perm (Fin k)) : IsExcFive (antiD σ) ↔ IsExcFive σ := by
  rw [antiD, isExcFive_compP_iff, isExcFive_revP_iff, isExcFive_invP_iff]

/-- (UD) for `antiD σ` is (LD) for `σ` (both written out; `UD (antiD σ) ↔ LD σ` by unfolding). -/
theorem ud_antiD_iff (σ : Perm (Fin k)) :
    (∀ j : ℕ, rv (antiD σ) ≤ j → j < k → spos (antiD σ) (j + 1) < spos (antiD σ) j) ↔
      (∀ i : ℕ, 1 ≤ i → i < bp σ → sval σ (i + 1) < sval σ i) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := spos_le σ 1
    exact ⟨fun _ i _ hi => absurd hi (by unfold bp; omega), fun _ j _ hj => absurd hj (by omega)⟩
  have hb1 : 1 ≤ bp σ := one_le_spos σ le_rfl hk
  have hbk : bp σ ≤ k := spos_le σ 1
  rw [rv_antiD σ hk]
  constructor
  · intro h i hi1 hi2
    have := h (k - i) (by omega) (by omega)
    rw [spos_antiD σ (by omega) (by omega), spos_antiD σ (by omega) (by omega)] at this
    have e1 : k + 1 - (k - i + 1) = i := by omega
    have e2 : k + 1 - (k - i) = i + 1 := by omega
    rw [e1, e2] at this
    have := sval_le σ i
    have := sval_le σ (i + 1)
    omega
  · intro h j hj1 hj2
    have := h (k - j) (by omega) (by omega)
    rw [spos_antiD σ (by omega) (by omega), spos_antiD σ (by omega) (by omega)]
    have e1 : k + 1 - (j + 1) = k - j := by omega
    have e2 : k + 1 - j = k - j + 1 := by omega
    rw [e1, e2]
    have := one_le_sval σ (i := k - j) (by omega) (by omega)
    have := sval_le σ (k - j)
    have := sval_le σ (k - j + 1)
    omega

/-- (BD) for `antiD σ` is (RD) for `σ` (both written out; `BD (antiD σ) ↔ RD σ` by unfolding). -/
theorem bd_antiD_iff (σ : Perm (Fin k)) :
    (∀ j : ℕ, 1 ≤ j → j < lv (antiD σ) → spos (antiD σ) (j + 1) < spos (antiD σ) j) ↔
      (∀ i : ℕ, up σ ≤ i → i < k → sval σ (i + 1) < sval σ i) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := sval_le (antiD σ) 1
    exact ⟨fun _ i _ hi => absurd hi (by omega), fun _ j _ hj => absurd hj (by unfold lv; omega)⟩
  have hu1 : 1 ≤ up σ := one_le_spos σ hk le_rfl
  have huk : up σ ≤ k := spos_le σ k
  rw [lv_antiD σ hk]
  constructor
  · intro h i hi1 hi2
    have := h (k - i) (by omega) (by omega)
    rw [spos_antiD σ (by omega) (by omega), spos_antiD σ (by omega) (by omega)] at this
    have e1 : k + 1 - (k - i + 1) = i := by omega
    have e2 : k + 1 - (k - i) = i + 1 := by omega
    rw [e1, e2] at this
    have := sval_le σ i
    have := sval_le σ (i + 1)
    omega
  · intro h j hj1 hj2
    have := h (k - j) (by omega) (by omega)
    rw [spos_antiD σ (by omega) (by omega), spos_antiD σ (by omega) (by omega)]
    have e1 : k + 1 - (j + 1) = k - j := by omega
    have e2 : k + 1 - j = k - j + 1 := by omega
    rw [e1, e2]
    have := one_le_sval σ (i := k - j) (by omega) (by omega)
    have := sval_le σ (k - j)
    have := sval_le σ (k - j + 1)
    omega

end DISC

end LinfPermRemoval
