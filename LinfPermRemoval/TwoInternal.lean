/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.UnitGap

/-!
# Subsubsection 4.4.3: the simultaneous exceptional case

Hypotheses of Lemma 4.40 (`Hyp440`): the standing hypotheses of Subsection 4.4, (4.22)
`ℓ = r - 1` and `b = u - 1`, (4.23) `u < σ⁻¹(ℓ-1) < σ⁻¹(k-1)`, (4.24) `σ(2) < σ(u+1) < ℓ`,
(UD) and (LD).

The claims inside the proof of Lemma 4.40 are steps of a proof by contradiction: their context
(`Ctx440`) fixes a `σ`-copy `Θ` in the support of Construction 4.39 with `Θ ≠ Σ`, which
`lemma_4_40` shows cannot exist; the bundle without the field `ne` is satisfiable (take
`Θ = Σ`).
-/

open Equiv Finset

namespace LinfPermRemoval

variable {k : ℕ}

/-- **Construction 4.39**, `P_H = (k-2, ℓ) + t(1,1)`, `0 < t < 1` (in the stripe `H_ℓ`). -/
def PH439 (σ : Perm (Fin k)) : Set (ℝ × ℝ) := openSeg ((k : ℝ) - 2, (lv σ : ℝ)) (1, 1)

/-- **Construction 4.39**, `P_V = (u-1, 2) + t(1,1)`, `0 < t < 1` (in the stripe `V_{u-1}`). -/
def PV439 (σ : Perm (Fin k)) : Set (ℝ × ℝ) := openSeg ((up σ : ℝ) - 1, 2) (1, 1)

/-- The support `Σ ∪ P_L ∪ P_R ∪ P_B ∪ P_U ∪ P_H ∪ P_V` of Construction 4.39. -/
noncomputable def D439 (σ : Perm (Fin k)) : Set (ℝ × ℝ) := D419 σ ∪ PH439 σ ∪ PV439 σ

/-- The hypotheses of Lemma 4.40. -/
structure Hyp440 (σ : Perm (Fin k)) : Prop where
  standing : Standing44 σ
  lr : lv σ + 1 = rv σ
  bu : bp σ + 1 = up σ
  pos : up σ < spos σ (lv σ - 1) ∧ spos σ (lv σ - 1) < spos σ (k - 1)
  val : sval σ 2 < sval σ (up σ + 1) ∧ sval σ (up σ + 1) < lv σ
  ud : UD σ
  ld : LD σ

/-! ## Auxiliary development for the proof of Lemma 4.40

The real arguments are stated with explicit hypotheses (`Hyp440 σ`, a copy `Θ` in the support
`D439 σ`, and, from Claim 4.47 on, `Θ ≠ Σ`), since `lemma_4_40` precedes `Ctx440`. -/

namespace TI

theorem sval_of {σ : Perm (Fin k)} {i : ℕ} (h : 1 ≤ i ∧ i ≤ k) :
    sval σ i = (σ ⟨i - 1, by omega⟩ : ℕ) + 1 := by
  simp [sval, h]

theorem spos_of {σ : Perm (Fin k)} {j : ℕ} (h : 1 ≤ j ∧ j ≤ k) :
    spos σ j = (σ.symm ⟨j - 1, by omega⟩ : ℕ) + 1 := by
  simp [spos, h]

theorem sval_mem {σ : Perm (Fin k)} {i : ℕ} (h : 1 ≤ i ∧ i ≤ k) :
    1 ≤ sval σ i ∧ sval σ i ≤ k := by
  rw [sval_of h]; have := (σ ⟨i - 1, by omega⟩).isLt; omega

theorem spos_mem {σ : Perm (Fin k)} {j : ℕ} (h : 1 ≤ j ∧ j ≤ k) :
    1 ≤ spos σ j ∧ spos σ j ≤ k := by
  rw [spos_of h]; have := (σ.symm ⟨j - 1, by omega⟩).isLt; omega

theorem sval_succ (σ : Perm (Fin k)) (a : Fin k) : sval σ ((a : ℕ) + 1) = (σ a : ℕ) + 1 := by
  rw [sval_of (by omega)]; simp

theorem spos_succ (σ : Perm (Fin k)) (a : Fin k) :
    spos σ ((a : ℕ) + 1) = (σ.symm a : ℕ) + 1 := by
  rw [spos_of (by omega)]; simp

theorem th_succ (Θ : Fin k → ℝ × ℝ) (a : Fin k) : th Θ ((a : ℕ) + 1) = Θ a := by
  simp [th]

theorem sval_spos {σ : Perm (Fin k)} {j : ℕ} (h : 1 ≤ j ∧ j ≤ k) :
    sval σ (spos σ j) = j := by
  rw [spos_of h, sval_succ, Equiv.apply_symm_apply]; simp; omega

theorem spos_sval {σ : Perm (Fin k)} {i : ℕ} (h : 1 ≤ i ∧ i ≤ k) :
    spos σ (sval σ i) = i := by
  rw [sval_of h, spos_succ, Equiv.symm_apply_apply]; simp; omega

theorem sval_inj {σ : Perm (Fin k)} {i i' : ℕ} (h : 1 ≤ i ∧ i ≤ k) (h' : 1 ≤ i' ∧ i' ≤ k)
    (he : sval σ i = sval σ i') : i = i' := by
  rw [← spos_sval (σ := σ) h, ← spos_sval (σ := σ) h', he]

theorem th_of {Θ : Fin k → ℝ × ℝ} {i : ℕ} (h : 1 ≤ i ∧ i ≤ k) :
    th Θ i = Θ ⟨i - 1, by omega⟩ := by
  simp [th, h]

theorem thInv_eq (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (j : ℕ) :
    thInv σ Θ j = th Θ (spos σ j) := by
  by_cases h : 1 ≤ j ∧ j ≤ k
  · rw [spos_of h, th_succ]
    simp [thInv, h]
  · simp [thInv, spos, th, h]

theorem sig_eq {σ : Perm (Fin k)} {i : ℕ} (h : 1 ≤ i ∧ i ≤ k) :
    sig σ i = ((i : ℝ), (sval σ i : ℝ)) := by
  rw [sig, th_of h, sval_of h, canonPt]
  ext
  · simp only; rw [Nat.cast_sub (by omega)]; simp
  · simp

theorem sigInv_eq {σ : Perm (Fin k)} {j : ℕ} (h : 1 ≤ j ∧ j ≤ k) :
    sigInv σ j = ((spos σ j : ℝ), (j : ℝ)) := by
  rw [sigInv, thInv_eq, ← sig, sig_eq (spos_mem h), sval_spos h]

theorem mem_canon {σ : Perm (Fin k)} {p : ℝ × ℝ} :
    p ∈ canon σ ↔ ∃ i, 1 ≤ i ∧ i ≤ k ∧ p = ((i : ℝ), (sval σ i : ℝ)) := by
  constructor
  · intro hp
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨a + 1, by omega, by omega, ?_⟩
    rw [← sig_eq (by omega), sig, th_of (by omega)]
    simp
  · rintro ⟨i, h1, h2, rfl⟩
    rw [← sig_eq ⟨h1, h2⟩, sig, th_of ⟨h1, h2⟩]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

variable {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ}

theorem thx_lt_iff (hr : Represents σ Θ) {i i' : ℕ} (h : 1 ≤ i ∧ i ≤ k) (h' : 1 ≤ i' ∧ i' ≤ k) :
    (th Θ i).1 < (th Θ i').1 ↔ i < i' := by
  rw [th_of h, th_of h', hr.1.lt_iff_lt, Fin.mk_lt_mk]; omega

theorem thy_lt_iff (hr : Represents σ Θ) {i i' : ℕ} (h : 1 ≤ i ∧ i ≤ k) (h' : 1 ≤ i' ∧ i' ≤ k) :
    (th Θ i).2 < (th Θ i').2 ↔ sval σ i < sval σ i' := by
  rw [th_of h, th_of h', hr.2, sval_of h, sval_of h', Fin.lt_def]; omega

theorem thx_lt (hr : Represents σ Θ) {i i' : ℕ} (h : 1 ≤ i) (h' : i' ≤ k) (hlt : i < i') :
    (th Θ i).1 < (th Θ i').1 := (thx_lt_iff hr (by omega) (by omega)).2 hlt

theorem thy_lt (hr : Represents σ Θ) {i i' : ℕ} (h : 1 ≤ i ∧ i ≤ k) (h' : 1 ≤ i' ∧ i' ≤ k)
    (hlt : sval σ i < sval σ i') : (th Θ i).2 < (th Θ i').2 := (thy_lt_iff hr h h').2 hlt

theorem thInvy_lt (hr : Represents σ Θ) {j j' : ℕ} (h : 1 ≤ j) (h' : j' ≤ k) (hlt : j < j') :
    (thInv σ Θ j).2 < (thInv σ Θ j').2 := by
  rw [thInv_eq, thInv_eq]
  apply thy_lt hr (spos_mem (by omega)) (spos_mem (by omega))
  rw [sval_spos (by omega), sval_spos (by omega)]; exact hlt

theorem th_inj (hr : Represents σ Θ) {i i' : ℕ} (h : 1 ≤ i ∧ i ≤ k) (h' : 1 ≤ i' ∧ i' ≤ k)
    (he : th Θ i = th Θ i') : i = i' := by
  rcases lt_trichotomy i i' with hl | hl | hl
  · have := thx_lt hr h.1 h'.2 hl; rw [he] at this; exact absurd this (lt_irrefl _)
  · exact hl
  · have := thx_lt hr h'.1 h.2 hl; rw [he] at this; exact absurd this (lt_irrefl _)


theorem spos_le (σ : Perm (Fin k)) (j : ℕ) : spos σ j ≤ k := by
  by_cases h : 1 ≤ j ∧ j ≤ k
  · exact (spos_mem h).2
  · simp [spos, h]

/-- Numerical consequences of the hypotheses of Lemma 4.40. -/
structure Nums (σ : Perm (Fin k)) : Prop where
  k5 : 5 ≤ k
  l3 : 3 ≤ lv σ
  lk : lv σ + 2 ≤ k
  r : rv σ = lv σ + 1
  b2 : 2 ≤ bp σ
  u : up σ = bp σ + 1
  uk : up σ + 2 ≤ k
  sb : sval σ (bp σ) = 1
  su : sval σ (up σ) = k
  sk : sval σ k = lv σ + 1
  pl : spos σ (lv σ) = 1
  pr : spos σ (lv σ + 1) = k

/-- `lv σ` unfolded (definitional). -/
theorem lv_def {σ : Perm (Fin k)} : sval σ 1 = lv σ := rfl

/-- `bp σ` unfolded (definitional). -/
theorem bp_def {σ : Perm (Fin k)} : spos σ 1 = bp σ := rfl

/-- `up σ` unfolded (definitional). -/
theorem up_def {σ : Perm (Fin k)} : spos σ k = up σ := rfl

theorem nums {σ : Perm (Fin k)} (hσ : Hyp440 σ) : Nums σ := by
  obtain ⟨⟨-, -, hl, hr⟩, hlr, hbu, ⟨hp1, hp2⟩, ⟨hv1, hv2⟩, -, -⟩ := hσ
  have hk : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    subst this
    exact hl.2 (by simp [lv, sval])
  have hlm := sval_mem (σ := σ) (i := 1) ⟨le_rfl, hk⟩
  have hrm := sval_mem (σ := σ) (i := k) ⟨hk, le_rfl⟩
  have hbm := spos_mem (σ := σ) (j := 1) ⟨le_rfl, hk⟩
  have hum := spos_mem (σ := σ) (j := k) ⟨hk, le_rfl⟩
  have hsb : sval σ (bp σ) = 1 := sval_spos ⟨le_rfl, hk⟩
  have hsu : sval σ (up σ) = k := sval_spos ⟨hk, le_rfl⟩
  have hpl : spos σ (lv σ) = 1 := spos_sval ⟨le_rfl, hk⟩
  have hpr : spos σ (rv σ) = k := spos_sval ⟨hk, le_rfl⟩
  have hb1 : bp σ ≠ 1 := fun h => hl.1 (by have := hsb; rw [h] at this; exact this)
  have hbk : bp σ ≠ k := fun h => hr.1 (by have := hsb; rw [h] at this; exact this)
  have hu1 : up σ ≠ 1 := fun h => hl.2 (by have := hsu; rw [h] at this; exact this)
  have huk : up σ ≠ k := fun h => hr.2 (by have := hsu; rw [h] at this; exact this)
  have hq := spos_le σ (k - 1)
  have h2 := sval_mem (σ := σ) (i := 2) ⟨by omega, by omega⟩
  change 1 ≤ lv σ ∧ lv σ ≤ k at hlm
  change 1 ≤ rv σ ∧ rv σ ≤ k at hrm
  change 1 ≤ bp σ ∧ bp σ ≤ k at hbm
  change 1 ≤ up σ ∧ up σ ≤ k at hum
  refine ⟨by omega, by omega, by omega, hlr.symm, by omega, hbu.symm, by omega, hsb, hsu,
    hlr.symm, hpl, by rw [hlr]; exact hpr⟩


/-! ### Geometry of the pieces of the support -/

theorem seg_nonint {a1 a2 v1 v2 t : ℝ} {p : ℝ × ℝ} (ha1 : ∃ z : ℤ, a1 = z)
    (ha2 : ∃ z : ℤ, a2 = z) (hv1 : v1 = 1 ∨ v1 = -1) (hv2 : v2 = 1 ∨ v2 = -1)
    (hp : p = (a1 + t * v1, a2 + t * v2)) (hl : p ∉ lattice) :
    (∀ m : ℤ, p.1 ≠ m) ∧ (∀ m : ℤ, p.2 ≠ m) := by
  obtain ⟨z1, rfl⟩ := ha1
  obtain ⟨z2, rfl⟩ := ha2
  subst hp
  constructor <;> intro m hm <;> apply hl <;> simp only at hm <;>
    rcases hv1 with rfl | rfl <;> rcases hv2 with rfl | rfl
  · exact ⟨m, z2 + m - z1, Prod.ext (by simp; linarith) (by push_cast; simp; linarith)⟩
  · exact ⟨m, z2 - m + z1, Prod.ext (by simp; linarith) (by push_cast; simp; linarith)⟩
  · exact ⟨m, z2 - m + z1, Prod.ext (by simp; linarith) (by push_cast; simp; linarith)⟩
  · exact ⟨m, z2 + m - z1, Prod.ext (by simp; linarith) (by push_cast; simp; linarith)⟩
  · exact ⟨z1 + m - z2, m, Prod.ext (by push_cast; simp; linarith) (by simp; linarith)⟩
  · exact ⟨z1 - m + z2, m, Prod.ext (by push_cast; simp; linarith) (by simp; linarith)⟩
  · exact ⟨z1 - m + z2, m, Prod.ext (by push_cast; simp; linarith) (by simp; linarith)⟩
  · exact ⟨z1 + m - z2, m, Prod.ext (by push_cast; simp; linarith) (by simp; linarith)⟩

theorem nonint_ne {x : ℝ} (h : ∀ m : ℤ, x ≠ m) (n : ℕ) : x ≠ n := by
  have := h n; simpa using this

variable {σ : Perm (Fin k)}

theorem PL_bd (hσ : Hyp440 σ) {p : ℝ × ℝ} (hp : p ∈ PL419 σ) :
    p.1 < 1 ∧ (lv σ : ℝ) + 1 < p.2 ∧ p.2 ≤ k ∧ (∀ m : ℤ, p.1 ≠ m) ∧ (∀ m : ℤ, p.2 ≠ m) := by
  have N := nums hσ
  obtain ⟨⟨hI, hlat⟩, hy⟩ := hp
  simp only [show lv σ < rv σ by rw [N.r]; omega, ↓reduceIte] at hy
  have hk : (5 : ℝ) ≤ k := by exact_mod_cast N.k5
  unfold IL419 at hI
  split_ifs at hI
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hn := seg_nonint ⟨1, by simp⟩ ⟨1, by simp⟩ (Or.inr rfl) (Or.inl rfl) rfl hlat
    have h1 := hn.1 1
    simp only [Int.cast_one] at h1 hy ⊢
    refine ⟨lt_of_le_of_ne (by linarith) h1, hy, by linarith, hn⟩
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hn := seg_nonint ⟨1, by simp⟩ ⟨k, by simp⟩ (Or.inr rfl) (Or.inr rfl) rfl hlat
    have h1 := hn.1 1
    simp only [Int.cast_one] at h1 hy ⊢
    refine ⟨lt_of_le_of_ne (by linarith) h1, hy, by linarith, hn⟩

theorem PR_bd (hσ : Hyp440 σ) {p : ℝ × ℝ} (hp : p ∈ PR419 σ) :
    (k : ℝ) < p.1 ∧ 1 ≤ p.2 ∧ p.2 < lv σ ∧ (∀ m : ℤ, p.1 ≠ m) ∧ (∀ m : ℤ, p.2 ≠ m) := by
  have N := nums hσ
  obtain ⟨⟨hI, hlat⟩, hy⟩ := hp
  simp only [show lv σ < rv σ by rw [N.r]; omega, ↓reduceIte] at hy
  rw [N.r] at hy
  push_cast at hy
  have hk : (5 : ℝ) ≤ k := by exact_mod_cast N.k5
  unfold IR419 at hI
  split_ifs at hI
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hn := seg_nonint ⟨k, by simp⟩ ⟨1, by simp⟩ (Or.inl rfl) (Or.inl rfl) rfl hlat
    have h1 := nonint_ne hn.1 k
    simp only at h1 hy ⊢
    refine ⟨lt_of_le_of_ne (by linarith) (Ne.symm h1), by linarith, by linarith, hn⟩
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hn := seg_nonint ⟨k, by simp⟩ ⟨k, by simp⟩ (Or.inl rfl) (Or.inr rfl) rfl hlat
    have h1 := nonint_ne hn.1 k
    simp only at h1 hy ⊢
    refine ⟨lt_of_le_of_ne (by linarith) (Ne.symm h1), by linarith, by linarith, hn⟩

theorem PB_bd (hσ : Hyp440 σ) {p : ℝ × ℝ} (hp : p ∈ PB419 σ) :
    p.2 < 1 ∧ (up σ : ℝ) < p.1 ∧ p.1 ≤ k ∧ (∀ m : ℤ, p.1 ≠ m) ∧ (∀ m : ℤ, p.2 ≠ m) := by
  have N := nums hσ
  obtain ⟨⟨hI, hlat⟩, hx⟩ := hp
  simp only [show bp σ < up σ by rw [N.u]; omega, ↓reduceIte] at hx
  have hu : (up σ : ℝ) = bp σ + 1 := by rw [N.u]; push_cast; ring
  have hk : (5 : ℝ) ≤ k := by exact_mod_cast N.k5
  unfold IB419 at hI
  split_ifs at hI
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hn := seg_nonint ⟨1, by simp⟩ ⟨1, by simp⟩ (Or.inl rfl) (Or.inr rfl) rfl hlat
    have h1 := hn.2 1
    simp only [Int.cast_one] at h1 hx ⊢
    refine ⟨lt_of_le_of_ne (by linarith) h1, by linarith, by linarith, hn⟩
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hn := seg_nonint ⟨k, by simp⟩ ⟨1, by simp⟩ (Or.inr rfl) (Or.inr rfl) rfl hlat
    have h1 := hn.2 1
    simp only [Int.cast_one] at h1 hx ⊢
    refine ⟨lt_of_le_of_ne (by linarith) h1, by linarith, by linarith, hn⟩

theorem PU_bd (hσ : Hyp440 σ) {p : ℝ × ℝ} (hp : p ∈ PU419 σ) :
    (k : ℝ) < p.2 ∧ 1 ≤ p.1 ∧ p.1 < bp σ ∧ (∀ m : ℤ, p.1 ≠ m) ∧ (∀ m : ℤ, p.2 ≠ m) := by
  have N := nums hσ
  obtain ⟨⟨hI, hlat⟩, hx⟩ := hp
  simp only [show bp σ < up σ by rw [N.u]; omega, ↓reduceIte] at hx
  have hu : (up σ : ℝ) = bp σ + 1 := by rw [N.u]; push_cast; ring
  have hk : (5 : ℝ) ≤ k := by exact_mod_cast N.k5
  unfold IU419 at hI
  split_ifs at hI
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hn := seg_nonint ⟨1, by simp⟩ ⟨k, by simp⟩ (Or.inl rfl) (Or.inl rfl) rfl hlat
    have h1 := nonint_ne hn.2 k
    simp only at h1 hx ⊢
    refine ⟨lt_of_le_of_ne (by linarith) (Ne.symm h1), by linarith, by linarith, hn⟩
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hn := seg_nonint ⟨k, by simp⟩ ⟨k, by simp⟩ (Or.inr rfl) (Or.inl rfl) rfl hlat
    have h1 := nonint_ne hn.2 k
    simp only at h1 hx ⊢
    refine ⟨lt_of_le_of_ne (by linarith) (Ne.symm h1), by linarith, by linarith, hn⟩

theorem PH_bd {p : ℝ × ℝ} (hp : p ∈ PH439 σ) :
    (k : ℝ) - 2 < p.1 ∧ p.1 < k - 1 ∧ (lv σ : ℝ) < p.2 ∧ p.2 < lv σ + 1 ∧
      p.2 = p.1 + ((lv σ : ℝ) - k + 2) := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hp
  simp only [mul_one]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by ring⟩

theorem PV_bd (hσ : Hyp440 σ) {p : ℝ × ℝ} (hp : p ∈ PV439 σ) :
    (bp σ : ℝ) < p.1 ∧ p.1 < bp σ + 1 ∧ 2 < p.2 ∧ p.2 < 3 ∧
      p.2 = p.1 + (2 - (bp σ : ℝ)) := by
  have hu : (up σ : ℝ) = bp σ + 1 := by rw [(nums hσ).u]; push_cast; ring
  obtain ⟨t, ht0, ht1, rfl⟩ := hp
  simp only [mul_one, hu]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by ring⟩

theorem canon_sub_D (σ : Perm (Fin k)) : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ D439 σ :=
  fun _ hp => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hp)))))

/-- Classification of the points of the support of Construction 4.39. -/
theorem cls (hσ : Hyp440 σ) {p : ℝ × ℝ} (hp : p ∈ D439 σ) :
    (∃ i, 1 ≤ i ∧ i ≤ k ∧ p = ((i : ℝ), (sval σ i : ℝ))) ∨
    (p ∈ PL419 σ ∧ p.1 < 1 ∧ (lv σ : ℝ) + 1 < p.2 ∧ p.2 ≤ k) ∨
    (p ∈ PR419 σ ∧ (k : ℝ) < p.1 ∧ 1 ≤ p.2 ∧ p.2 < lv σ) ∨
    (p ∈ PB419 σ ∧ p.2 < 1 ∧ (up σ : ℝ) < p.1 ∧ p.1 ≤ k) ∨
    (p ∈ PU419 σ ∧ (k : ℝ) < p.2 ∧ 1 ≤ p.1 ∧ p.1 < bp σ) ∨
    (p ∈ PH439 σ ∧ (k : ℝ) - 2 < p.1 ∧ p.1 < k - 1 ∧ (lv σ : ℝ) < p.2 ∧ p.2 < lv σ + 1 ∧
      p.2 = p.1 + ((lv σ : ℝ) - k + 2)) ∨
    (p ∈ PV439 σ ∧ (bp σ : ℝ) < p.1 ∧ p.1 < bp σ + 1 ∧ 2 < p.2 ∧ p.2 < 3 ∧
      p.2 = p.1 + (2 - (bp σ : ℝ))) := by
  rcases hp with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inl (mem_canon.mp (Finset.mem_coe.mp h))
  · have := PL_bd hσ h; exact Or.inr (Or.inl ⟨h, this.1, this.2.1, this.2.2.1⟩)
  · have := PR_bd hσ h; exact Or.inr (Or.inr (Or.inl ⟨h, this.1, this.2.1, this.2.2.1⟩))
  · have := PB_bd hσ h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, this.1, this.2.1, this.2.2.1⟩)))
  · have := PU_bd hσ h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, this.1, this.2.1, this.2.2.1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, PH_bd h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, PV_bd hσ h⟩)))))


/-! ### The boundary restrictions (4.4) -/

theorem numsR (hσ : Hyp440 σ) :
    (5 : ℝ) ≤ k ∧ (3 : ℝ) ≤ lv σ ∧ (lv σ : ℝ) + 2 ≤ k ∧ (2 : ℝ) ≤ bp σ ∧
      (up σ : ℝ) = bp σ + 1 ∧ (up σ : ℝ) + 2 ≤ k := by
  have N := nums hσ
  refine ⟨by exact_mod_cast N.k5, by exact_mod_cast N.l3, by exact_mod_cast N.lk,
    by exact_mod_cast N.b2, by rw [N.u]; push_cast; ring, by exact_mod_cast N.uk⟩


theorem posSlope_of {S : Set (ℝ × ℝ)} (a1 a2 : ℝ)
    (hS : ∀ p ∈ S, ∃ t : ℝ, p.1 = a1 + t ∧ p.2 = a2 + t) : PosSlope S := by
  intro p hp q hq _
  obtain ⟨s, hs1, hs2⟩ := hS p hp
  obtain ⟨t, ht1, ht2⟩ := hS q hq
  rw [hs1, hs2, ht1, ht2]; constructor <;> intro h <;> linarith

theorem negSlope_of {S : Set (ℝ × ℝ)} (a1 a2 : ℝ)
    (hS : ∀ p ∈ S, ∃ t : ℝ, p.1 = a1 + t ∧ p.2 = a2 - t) : NegSlope S := by
  intro p hp q hq _
  obtain ⟨s, hs1, hs2⟩ := hS p hp
  obtain ⟨t, ht1, ht2⟩ := hS q hq
  rw [hs1, hs2, ht1, ht2]; constructor <;> intro h <;> linarith

theorem th_mem {Θ : Fin k → ℝ × ℝ} (hΘ : CopyIn σ Θ (D439 σ)) {i : ℕ} (h : 1 ≤ i ∧ i ≤ k) :
    th Θ i ∈ D439 σ := by
  rw [th_of h]; exact hΘ.2 _


theorem memPL_of (hσ : Hyp440 σ) {p : ℝ × ℝ} (hp : p ∈ D439 σ) (hx : p.1 < 1) : p ∈ PL419 σ := by
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  rcases cls hσ hp with ⟨j, h1, h2, rfl⟩ | h | h | h | h | h | h
  · simp only at hx; exact absurd hx (by push Not; exact_mod_cast h1)
  · exact h.1
  all_goals linarith [h.2.1, h.2.2.1, h.2.2.2]

theorem memPR_of (hσ : Hyp440 σ) {p : ℝ × ℝ} (hp : p ∈ D439 σ) (hx : (k : ℝ) < p.1) :
    p ∈ PR419 σ := by
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  rcases cls hσ hp with ⟨j, h1, h2, rfl⟩ | h | h | h | h | h | h
  · simp only at hx; exact absurd hx (by push Not; exact_mod_cast h2)
  · linarith [h.2.1]
  · exact h.1
  all_goals linarith [h.2.1, h.2.2.1, h.2.2.2]

theorem memPB_of (hσ : Hyp440 σ) {p : ℝ × ℝ} (hp : p ∈ D439 σ) (hy : p.2 < 1) :
    p ∈ PB419 σ := by
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  rcases cls hσ hp with ⟨j, h1, h2, rfl⟩ | h | h | h | h | h | h
  · simp only at hy
    exact absurd hy (by push Not; exact_mod_cast (sval_mem ⟨h1, h2⟩).1)
  · linarith [h.2.2.1]
  · linarith [h.2.2.1]
  · exact h.1
  all_goals linarith [h.2.1, h.2.2.1, h.2.2.2]

theorem memPU_of (hσ : Hyp440 σ) {p : ℝ × ℝ} (hp : p ∈ D439 σ) (hy : (k : ℝ) < p.2) :
    p ∈ PU419 σ := by
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  rcases cls hσ hp with ⟨j, h1, h2, rfl⟩ | h | h | h | h | h | h
  · simp only at hy
    exact absurd hy (by push Not; exact_mod_cast (sval_mem ⟨h1, h2⟩).2)
  · linarith [h.2.2.2]
  · linarith [h.2.2.2]
  · linarith [h.2.1]
  · exact h.1
  all_goals linarith [h.2.1, h.2.2.1, h.2.2.2]

/-- The boundary restrictions (4.4), in 1-based form. -/
theorem bd (hσ : Hyp440 σ) {Θ : Fin k → ℝ × ℝ} (hΘ : CopyIn σ Θ (D439 σ)) {i : ℕ}
    (hi : 1 ≤ i ∧ i ≤ k) :
    (th Θ i ∈ PL419 σ → i = 1) ∧ (th Θ i ∈ PR419 σ → i = k) ∧
      (th Θ i ∈ PB419 σ → sval σ i = 1) ∧ (th Θ i ∈ PU419 σ → sval σ i = k) := by
  have N := nums hσ
  have hk : 2 ≤ k := by have := N.k5; omega
  have hk5 : (5 : ℝ) ≤ k := by exact_mod_cast N.k5
  have hu3 : (3 : ℝ) ≤ up σ := by have := N.u; have := N.b2; exact_mod_cast (by omega : 3 ≤ up σ)
  have hb2 : (2 : ℝ) ≤ bp σ := by exact_mod_cast N.b2
  have hl3 : (3 : ℝ) ≤ lv σ := by exact_mod_cast N.l3
  have hlk : (lv σ : ℝ) + 2 ≤ k := by exact_mod_cast N.lk
  have huk : (up σ : ℝ) + 2 ≤ k := by exact_mod_cast N.uk
  have hbk : (bp σ : ℝ) + 3 ≤ k := by
    have := N.u; have := N.uk; exact_mod_cast (by omega : bp σ + 3 ≤ k)
  have hD := canon_sub_D σ
  have hL : ∀ p ∈ {p | p ∈ D439 σ ∧ p.1 < 1}, p ∈ PL419 σ := fun p hp => memPL_of hσ hp.1 hp.2
  have hR : ∀ p ∈ {p | p ∈ D439 σ ∧ (k : ℝ) < p.1}, p ∈ PR419 σ :=
    fun p hp => memPR_of hσ hp.1 hp.2
  have hB : ∀ p ∈ {p | p ∈ D439 σ ∧ p.2 < 1}, p ∈ PB419 σ := fun p hp => memPB_of hσ hp.1 hp.2
  have hU : ∀ p ∈ {p | p ∈ D439 σ ∧ (k : ℝ) < p.2}, p ∈ PU419 σ :=
    fun p hp => memPU_of hσ hp.1 hp.2
  have hrep := hΘ.1
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
  · have := claim_4_3_1 σ hk (D439 σ) hD Θ hΘ ⟨fun h12 => negSlope_of 1 1 (fun p hp => by
        have hI := (hL p hp).1.1
        unfold IL419 at hI; simp only [show lv σ < sval σ 2 from h12, ↓reduceIte] at hI
        obtain ⟨t, -, -, rfl⟩ := hI; exact ⟨-t, by simp, by simp⟩),
      fun h21 => posSlope_of 1 k (fun p hp => by
        have hI := (hL p hp).1.1
        unfold IL419 at hI; simp only [show ¬ lv σ < sval σ 2 by change ¬ sval σ 1 < sval σ 2; omega,
          ↓reduceIte] at hI
        obtain ⟨t, -, -, rfl⟩ := hI; exact ⟨-t, by simp, by simp⟩)⟩
      ⟨i - 1, by omega⟩ ⟨th_of (Θ := Θ) hi ▸ th_mem hΘ hi, by rw [← th_of (Θ := Θ) hi]; exact (PL_bd hσ hp).1⟩
    rw [← th_of (Θ := Θ) hi] at this
    exact th_inj hrep hi ⟨le_rfl, hk.trans' (by norm_num)⟩ this
  · have := claim_4_3_2 σ hk (D439 σ) hD Θ hΘ ⟨fun h12 => negSlope_of k k (fun p hp => by
        have hI := (hR p hp).1.1
        unfold IR419 at hI; simp only [show ¬ rv σ < sval σ (k - 1) by change ¬ sval σ k < sval σ (k - 1); omega,
          ↓reduceIte] at hI
        obtain ⟨t, -, -, rfl⟩ := hI; exact ⟨t, by simp, by simp; ring⟩),
      fun h21 => posSlope_of k 1 (fun p hp => by
        have hI := (hR p hp).1.1
        unfold IR419 at hI; simp only [show rv σ < sval σ (k - 1) from h21, ↓reduceIte] at hI
        obtain ⟨t, -, -, rfl⟩ := hI; exact ⟨t, by simp, by simp⟩)⟩
      ⟨i - 1, by omega⟩ ⟨th_of (Θ := Θ) hi ▸ th_mem hΘ hi, by rw [← th_of (Θ := Θ) hi]; exact (PR_bd hσ hp).1⟩
    rw [← th_of (Θ := Θ) hi] at this
    exact th_inj hrep hi ⟨by omega, le_rfl⟩ this
  · have := claim_4_3_3 σ hk (D439 σ) hD Θ hΘ ⟨fun h12 => negSlope_of 1 1 (fun p hp => by
        have hI := (hB p hp).1.1
        unfold IB419 at hI; simp only [show bp σ < spos σ 2 from h12, ↓reduceIte] at hI
        obtain ⟨t, -, -, rfl⟩ := hI; exact ⟨t, by simp, by simp; ring⟩),
      fun h21 => posSlope_of k 1 (fun p hp => by
        have hI := (hB p hp).1.1
        unfold IB419 at hI; simp only [show ¬ bp σ < spos σ 2 by change ¬ spos σ 1 < spos σ 2; omega,
          ↓reduceIte] at hI
        obtain ⟨t, -, -, rfl⟩ := hI; exact ⟨-t, by simp, by simp⟩)⟩
      ⟨i - 1, by omega⟩ ⟨th_of (Θ := Θ) hi ▸ th_mem hΘ hi, by rw [← th_of (Θ := Θ) hi]; exact (PB_bd hσ hp).1⟩
    rw [← th_of (Θ := Θ) hi, thInv_eq] at this
    have := th_inj hrep hi (spos_mem ⟨le_rfl, by omega⟩) this
    rw [this, sval_spos ⟨le_rfl, by omega⟩]
  · have := claim_4_3_4 σ hk (D439 σ) hD Θ hΘ ⟨fun h12 => negSlope_of k k (fun p hp => by
        have hI := (hU p hp).1.1
        unfold IU419 at hI; simp only [show ¬ up σ < spos σ (k - 1) by change ¬ spos σ k < spos σ (k - 1); omega,
          ↓reduceIte] at hI
        obtain ⟨t, -, -, rfl⟩ := hI; exact ⟨-t, by simp, by simp⟩),
      fun h21 => posSlope_of 1 k (fun p hp => by
        have hI := (hU p hp).1.1
        unfold IU419 at hI; simp only [show up σ < spos σ (k - 1) from h21, ↓reduceIte] at hI
        obtain ⟨t, -, -, rfl⟩ := hI; exact ⟨t, by simp, by simp⟩)⟩
      ⟨i - 1, by omega⟩ ⟨th_of (Θ := Θ) hi ▸ th_mem hΘ hi, by rw [← th_of (Θ := Θ) hi]; exact (PU_bd hσ hp).1⟩
    rw [← th_of (Θ := Θ) hi, thInv_eq] at this
    have := th_inj hrep hi (spos_mem ⟨by omega, le_rfl⟩) this
    rw [this, sval_spos ⟨by omega, le_rfl⟩]


/-! ### Case analysis for the points of a copy -/

variable {Θ : Fin k → ℝ × ℝ}

/-- The classification of `Θ(i)` together with the boundary restrictions. -/
theorem clsTh (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ k) :
    (∃ i', 1 ≤ i' ∧ i' ≤ k ∧ th Θ i = ((i' : ℝ), (sval σ i' : ℝ)) ∧
      (th Θ i).1 = i' ∧ (th Θ i).2 = sval σ i') ∨
    (i = 1 ∧ (th Θ i).1 < 1 ∧ (lv σ : ℝ) + 1 < (th Θ i).2 ∧ (th Θ i).2 ≤ k) ∨
    (i = k ∧ (k : ℝ) < (th Θ i).1 ∧ 1 ≤ (th Θ i).2 ∧ (th Θ i).2 < lv σ) ∨
    (sval σ i = 1 ∧ (th Θ i).2 < 1 ∧ (up σ : ℝ) < (th Θ i).1 ∧ (th Θ i).1 ≤ k) ∨
    (sval σ i = k ∧ (k : ℝ) < (th Θ i).2 ∧ 1 ≤ (th Θ i).1 ∧ (th Θ i).1 < bp σ) ∨
    (th Θ i ∈ PH439 σ ∧ (k : ℝ) - 2 < (th Θ i).1 ∧ (th Θ i).1 < k - 1 ∧
      (lv σ : ℝ) < (th Θ i).2 ∧ (th Θ i).2 < lv σ + 1 ∧
      (th Θ i).2 = (th Θ i).1 + ((lv σ : ℝ) - k + 2)) ∨
    (th Θ i ∈ PV439 σ ∧ (bp σ : ℝ) < (th Θ i).1 ∧ (th Θ i).1 < bp σ + 1 ∧
      2 < (th Θ i).2 ∧ (th Θ i).2 < 3 ∧ (th Θ i).2 = (th Θ i).1 + (2 - (bp σ : ℝ))) := by
  have B := bd hσ hΘ hi
  rcases cls hσ (th_mem hΘ hi) with h | h | h | h | h | h | h
  · obtain ⟨i', h1, h2, he⟩ := h
    exact Or.inl ⟨i', h1, h2, he, by rw [he], by rw [he]⟩
  · exact Or.inr (Or.inl ⟨B.1 h.1, h.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨B.2.1 h.1, h.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨B.2.2.1 h.1, h.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨B.2.2.2 h.1, h.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-- The rounding step behind Claim 4.41: a point of the copy outside `P_H ∪ P_V` that deviates
from its canonical level does so by at least one unit, in each direction in which there is room
for a unit step: upward in `y` when `σ(i) < k`, downward in `y` when `1 < σ(i)`, rightward in `x`
when `i < k`, and leftward in `x` when `1 < i`. -/
theorem round (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ k)
    (hn : th Θ i ∉ PH439 σ ∪ PV439 σ) :
    (sval σ i < k → (sval σ i : ℝ) < (th Θ i).2 → (sval σ i : ℝ) + 1 ≤ (th Θ i).2) ∧
    (1 < sval σ i → (th Θ i).2 < sval σ i → (th Θ i).2 ≤ (sval σ i : ℝ) - 1) ∧
    (i < k → (i : ℝ) < (th Θ i).1 → (i : ℝ) + 1 ≤ (th Θ i).1) ∧
    (1 < i → (th Θ i).1 < i → (th Θ i).1 ≤ (i : ℝ) - 1) := by
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  rcases clsTh hσ hΘ hi with ⟨i', h1, h2, he, -, -⟩ | ⟨rfl, hx, hy, -⟩ | ⟨rfl, hx, -, hy⟩ |
      ⟨hs, hy, hx, -⟩ | ⟨hs, hy, -, hx⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · rw [he]; simp only
    refine ⟨fun _ h => ?_, fun _ h => ?_, fun _ h => ?_, fun _ h => ?_⟩
    · have : sval σ i < sval σ i' := by exact_mod_cast h
      have : sval σ i + 1 ≤ sval σ i' := this
      exact_mod_cast this
    · have : sval σ i' < sval σ i := by exact_mod_cast h
      have : (sval σ i' : ℝ) + 1 ≤ sval σ i := by exact_mod_cast this
      linarith
    · have : i < i' := by exact_mod_cast h
      have : i + 1 ≤ i' := this
      exact_mod_cast this
    · have : i' < i := by exact_mod_cast h
      have : (i' : ℝ) + 1 ≤ i := by exact_mod_cast this
      linarith
  · rw [lv_def]
    refine ⟨fun _ _ => by linarith, fun _ h => by linarith, fun _ h => by simp at h; linarith,
      fun h => absurd h (lt_irrefl _)⟩
  · rw [N.sk]; push_cast
    refine ⟨fun _ h => by linarith, fun _ _ => by linarith, fun h => absurd h (lt_irrefl _),
      fun _ h => by linarith⟩
  · rw [hs]
    have hib : i = bp σ := by
      have := spos_sval (σ := σ) hi; rw [hs] at this; exact this.symm
    subst hib
    refine ⟨fun _ h => by simp at h; linarith, fun h => absurd h (lt_irrefl _),
      fun _ _ => by linarith, fun _ h => by linarith⟩
  · rw [hs]
    have hiu : i = up σ := by
      have := spos_sval (σ := σ) hi; rw [hs] at this; exact this.symm
    subst hiu
    refine ⟨fun h => absurd h (lt_irrefl _), fun _ h => by linarith, fun _ h => by linarith,
      fun _ _ => by linarith⟩
  · exact absurd (Or.inl h) hn
  · exact absurd (Or.inr h) hn


theorem nat_btw {a n : ℕ} (h1 : (a : ℝ) < n) (h2 : (n : ℝ) < a + 1) : False := by
  have : a < n := by exact_mod_cast h1
  have : n < a + 1 := by exact_mod_cast h2
  omega

/-! ### Claim 4.41 and Corollary 4.42 -/

theorem c441 (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ)) :
    (∀ j : ℕ, 1 ≤ j → j < k → thInv σ Θ j ∉ PH439 σ ∪ PV439 σ → (j : ℝ) < (thInv σ Θ j).2 →
      ((j : ℝ) + 1) < (thInv σ Θ (j + 1)).2) ∧
    (∀ j : ℕ, 1 < j → j ≤ k → thInv σ Θ j ∉ PH439 σ ∪ PV439 σ → (thInv σ Θ j).2 < (j : ℝ) →
      (thInv σ Θ (j - 1)).2 < (j : ℝ) - 1) ∧
    (∀ i : ℕ, 1 ≤ i → i < k → th Θ i ∉ PH439 σ ∪ PV439 σ → (i : ℝ) < (th Θ i).1 →
      ((i : ℝ) + 1) < (th Θ (i + 1)).1) ∧
    (∀ i : ℕ, 1 < i → i ≤ k → th Θ i ∉ PH439 σ ∪ PV439 σ → (th Θ i).1 < (i : ℝ) →
      (th Θ (i - 1)).1 < (i : ℝ) - 1) := by
  have hr := hΘ.1
  refine ⟨fun j hj1 hjk hn hy => ?_, fun j hj1 hjk hn hy => ?_, fun i hi1 hik hn hx => ?_,
    fun i hi1 hik hn hx => ?_⟩
  · have h2 := thInvy_lt hr hj1 hjk (Nat.lt_succ_self j)
    simp only [thInv_eq] at hn hy h2 ⊢
    have R := (round hσ hΘ (spos_mem ⟨hj1, hjk.le⟩) hn).1
    rw [sval_spos ⟨hj1, hjk.le⟩] at R
    linarith [R hjk hy]
  · have h2 := thInvy_lt hr (j := j - 1) (by omega) hjk (by omega)
    simp only [thInv_eq] at hn hy h2 ⊢
    have R := (round hσ hΘ (spos_mem ⟨by omega, hjk⟩) hn).2.1
    rw [sval_spos ⟨by omega, hjk⟩] at R
    linarith [R hj1 hy]
  · have h2 := thx_lt hr hi1 hik (Nat.lt_succ_self i)
    linarith [(round hσ hΘ ⟨hi1, hik.le⟩ hn).2.2.1 hik hx]
  · have h2 := thx_lt hr (i := i - 1) (by omega) hik (by omega)
    linarith [(round hσ hΘ ⟨by omega, hik⟩ hn).2.2.2 hi1 hx]

theorem thInvy_le (hr : Represents σ Θ) {j s : ℕ} (hj : 1 ≤ j) (hjs : j ≤ s) (hs : s ≤ k) :
    (thInv σ Θ j).2 ≤ (thInv σ Θ s).2 := by
  rcases eq_or_lt_of_le hjs with rfl | h
  · exact le_rfl
  · exact (thInvy_lt hr hj hs h).le

theorem thx_le (hr : Represents σ Θ) {i s : ℕ} (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ k) :
    (th Θ s).1 ≤ (th Θ i).1 := by
  rcases eq_or_lt_of_le hsi with rfl | h
  · exact le_rfl
  · exact (thx_lt hr hs hi h).le

theorem c442 (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ)) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k → (j : ℝ) < (thInv σ Θ j).2 → (lv σ : ℝ) + 1 ≤ (thInv σ Θ j).2 →
      ∀ s : ℕ, j ≤ s → s ≤ k → (s : ℝ) < (thInv σ Θ s).2) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ k → (th Θ i).1 < (i : ℝ) → (th Θ i).1 ≤ (up σ : ℝ) - 1 →
      ∀ s : ℕ, 1 ≤ s → s ≤ i → (th Θ s).1 < (s : ℝ)) := by
  have hr := hΘ.1
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  refine ⟨fun j hj1 hjk hy hyl s hjs hsk => ?_, fun i hi1 hik hx hxu s hs1 hsi => ?_⟩
  · induction s, hjs using Nat.le_induction with
    | base => exact hy
    | succ s hjs ih =>
      have ih' := ih (by omega)
      have hm := thInvy_le hr hj1 hjs (by omega)
      have hn : thInv σ Θ s ∉ PH439 σ ∪ PV439 σ := by
        rintro (h | h)
        · linarith [(PH_bd h).2.2.2.1]
        · linarith [(PV_bd hσ h).2.2.2.1]
      push_cast
      exact (c441 hσ hΘ).1 s (by omega) (by omega) hn ih'
  · obtain ⟨d, hd⟩ : ∃ d, s + d = i := ⟨i - s, by omega⟩
    induction d generalizing s with
    | zero => simp at hd; subst hd; exact hx
    | succ d ih =>
      have ih' := ih (s + 1) (by omega) (by omega) (by omega)
      have hm := thx_le hr (s := s + 1) (by omega) (by omega) hik
      have hn : th Θ (s + 1) ∉ PH439 σ ∪ PV439 σ := by
        rintro (h | h)
        · linarith [(PH_bd h).1]
        · linarith [(PV_bd hσ h).1]
      have := (c441 hσ hΘ).2.2.2 (s + 1) (by omega) (by omega) hn (by exact_mod_cast ih')
      simpa using this


/-! ### Claim 4.43 -/

theorem c443a (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ)) : thInv σ Θ (lv σ) ∉ PH439 σ := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3
  intro h
  rw [thInv_eq, N.pl] at h
  obtain ⟨h1x, h1x', h1y, h1y', -⟩ := PH_bd h
  have hU : 1 ≤ up σ ∧ up σ ≤ k := ⟨by omega, by omega⟩
  have hK : 1 ≤ k ∧ k ≤ k := ⟨by omega, le_rfl⟩
  have hxU := thx_lt hr (i := 1) le_rfl hU.2 (by omega)
  have hyU := thy_lt hr (i := 1) ⟨le_rfl, by omega⟩ hU (by rw [lv_def, N.su]; omega)
  have hxK := thx_lt hr (i := up σ) hU.1 le_rfl (by omega)
  have hyK := thy_lt hr (i := 1) ⟨le_rfl, by omega⟩ hK (by rw [lv_def, N.sk]; omega)
  have hyK' := thy_lt hr (i := k) hK hU (by rw [N.sk, N.su]; omega)
  rcases clsTh hσ hΘ hU with ⟨i', h1, h2, -, hx, hy⟩ | ⟨h1, -⟩ | ⟨-, -, -, hy⟩ | ⟨-, hy, -⟩ |
      ⟨-, -, -, hx⟩ | ⟨hP, -, -, -, hy, hl⟩ | ⟨-, -, hx, -⟩
  · have hi' : k < i' + 2 := by
      have : (k : ℝ) < i' + 2 := by linarith
      exact_mod_cast this
    rcases clsTh hσ hΘ hK with ⟨i'', h1', h2', -, hx', hy'⟩ | ⟨h1, -⟩ | ⟨-, -, -, hy⟩ |
        ⟨-, hy, -⟩ | ⟨-, -, -, hx⟩ | ⟨-, -, hx, -⟩ | ⟨-, -, -, -, hy, -⟩
    · have : i' < i'' := by
        have : (i' : ℝ) < i'' := by linarith
        exact_mod_cast this
      have hi'k : i' = k - 1 := by omega
      have hxU' : (th Θ (up σ)).1 = (k : ℝ) - 1 := by
        rw [hx, hi'k]; rw [Nat.cast_sub (by omega)]; simp
      have hxK' : (th Θ k).1 ≤ k := by rw [hx']; exact_mod_cast h2'
      have hM : 1 ≤ k - 1 ∧ k - 1 ≤ k := ⟨by omega, by omega⟩
      have hxM := thx_lt hr (i := up σ) hU.1 hM.2 (by omega)
      have hxM' := thx_lt hr (i := k - 1) hM.1 le_rfl (by omega)
      rcases clsTh hσ hΘ hM with ⟨j', -, -, -, hx'', -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨hs, -⟩ |
          ⟨-, -, -, hx⟩ | ⟨-, -, hx, -⟩ | ⟨-, -, hx, -⟩
      · rw [hx'', hxU'] at hxM
        rw [hx''] at hxM'
        exact nat_btw (a := k - 1) (n := j') (by rw [Nat.cast_sub (by omega)]; simpa using hxM)
          (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
      · omega
      · omega
      · have : k - 1 = bp σ := by
          have := spos_sval (σ := σ) hM; rw [hs] at this; rw [← this]; exact bp_def
        omega
      · linarith
      · linarith
      · linarith
    · omega
    · linarith
    · linarith
    · linarith
    · have : (k : ℝ) - 1 ≤ i' := by
        have : k ≤ i' + 1 := by omega
        have : (k : ℝ) ≤ i' + 1 := by exact_mod_cast this
        linarith
      linarith
    · linarith
  · omega
  · linarith
  · linarith
  · linarith
  · rcases clsTh hσ hΘ hK with ⟨i'', -, -, -, -, hy'⟩ | ⟨-, -, hy, -⟩ | ⟨-, -, -, hy⟩ |
        ⟨-, hy, -⟩ | ⟨-, hy, -⟩ | ⟨-, -, -, -, -, hl'⟩ | ⟨-, -, -, -, hy, -⟩
    · rw [hy'] at hyK hyK'
      exact nat_btw (a := lv σ) (n := sval σ i'') (by linarith) (by linarith)
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
  · linarith

theorem c443b (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ)) : th Θ (up σ) ∉ PV439 σ := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3
  intro h
  obtain ⟨hUx, hUx', hUy, hUy', -⟩ := PV_bd hσ h
  have hU : 1 ≤ up σ ∧ up σ ≤ k := ⟨by omega, by omega⟩
  have hA : 1 ≤ 1 ∧ 1 ≤ k := ⟨le_rfl, by omega⟩
  have hB : 1 ≤ bp σ ∧ bp σ ≤ k := ⟨by omega, by omega⟩
  have hxA := thx_lt hr (i := 1) le_rfl hU.2 (by omega)
  have hyA := thy_lt hr hA hU (by rw [lv_def, N.su]; omega)
  have hxB := thx_lt hr (i := bp σ) hB.1 hU.2 (by omega)
  have hxAB := thx_lt hr (i := 1) le_rfl hB.2 (by omega)
  have hyB := thy_lt hr hB hA (by rw [lv_def, N.sb]; omega)
  rcases clsTh hσ hΘ hA with ⟨i', h1, h2, -, hx, hy⟩ | ⟨-, -, hy, -⟩ | ⟨h1, -⟩ | ⟨hs, -⟩ |
      ⟨hs, -⟩ | ⟨-, hx, -⟩ | ⟨hP, -, -, -, -, hl⟩
  · have hi' : sval σ i' ≤ 2 := by
      have : (sval σ i' : ℝ) < 3 := by linarith
      have : sval σ i' < 3 := by exact_mod_cast this
      omega
    rcases clsTh hσ hΘ hB with ⟨i'', hi1'', hi2'', -, -, hy'⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
        ⟨-, -, hx, -⟩ | ⟨hs, -⟩ | ⟨-, hx, -⟩ | ⟨-, -, -, hy', -⟩
    · have hlt : sval σ i'' < sval σ i' := by
        have : (sval σ i'' : ℝ) < sval σ i' := by linarith
        exact_mod_cast this
      have h1'' := (sval_mem (σ := σ) (i := i'') ⟨hi1'', hi2''⟩).1
      have hs2 : sval σ i' = 2 := by omega
      have hs1 : sval σ i'' = 1 := by omega
      have hT : 1 ≤ 2 ∧ 2 ≤ k := ⟨by omega, by omega⟩
      have hTm := spos_mem (σ := σ) hT
      have hyT := thy_lt hr hB hTm (by rw [N.sb, sval_spos hT]; omega)
      have hyT' := thy_lt hr hTm hA (by rw [lv_def, sval_spos hT]; omega)
      rw [hy', hs1] at hyT
      rw [hy, hs2] at hyT'
      rcases clsTh hσ hΘ hTm with ⟨j', -, -, -, -, hy''⟩ | ⟨-, -, hy, -⟩ | ⟨hk, -⟩ |
          ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨-, -, -, hy, -⟩ | ⟨-, -, -, hy, -⟩
      · rw [hy''] at hyT hyT'
        exact nat_btw (a := 1) (n := sval σ j') (by exact_mod_cast hyT)
          (by push_cast at hyT' ⊢; linarith)
      · push_cast at hyT'; linarith
      · have := sval_spos (σ := σ) hT; rw [hk, N.sk] at this; omega
      · rw [sval_spos hT] at hs; omega
      · rw [sval_spos hT] at hs; omega
      · push_cast at hyT'; linarith
      · push_cast at hyT'; linarith
    · omega
    · omega
    · linarith
    · rw [N.sb] at hs; omega
    · linarith
    · have : (sval σ i' : ℝ) ≤ 2 := by exact_mod_cast hi'
      linarith
  · linarith
  · omega
  · rw [lv_def] at hs; omega
  · rw [lv_def] at hs; omega
  · linarith
  · rcases clsTh hσ hΘ hB with ⟨i'', -, -, -, hx', -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, hx, -⟩ |
        ⟨-, hy', -⟩ | ⟨-, hx, -⟩ | ⟨-, -, -, -, -, hl'⟩
    · rw [hx'] at hxB hxAB
      have hP' := PV_bd hσ hP
      exact nat_btw (a := bp σ) (n := i'') (by linarith) (by linarith)
    · omega
    · omega
    · linarith
    · linarith
    · linarith
    · linarith


/-! ### Claim 4.44 -/

/-- Claim 4.44 (1). A step inside the proof by contradiction of Lemma 4.40 (tex l.1519, Claim 4.44
at l.1591): its hypotheses can never all hold, since a copy meeting `P_H` differs from `Σ` and
`TI.no_copy` refutes it. Used inside `claim_4_44`, `TI.c445a`, `TI.c445b` and `TI.c446`. -/
theorem c444a (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hs : ∃ s : ℕ, 1 ≤ s ∧ s < lv σ ∧ thInv σ Θ s ∈ PH439 σ) :
    (lv σ : ℝ) + 1 ≤ (thInv σ Θ (lv σ)).2 ∧ thInv σ Θ k ∈ PU419 σ ∧
      ∀ j : ℕ, rv σ ≤ j → j ≤ k - 1 → thInv σ Θ j = sigInv σ (j + 1) := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3; have hr' := N.r
  obtain ⟨s, hs1, hsl, hP⟩ := hs
  have hys := (PH_bd hP).2.2.1
  have hyl := thInvy_lt hr hs1 (by omega : lv σ ≤ k) hsl
  have hA : 1 ≤ 1 ∧ 1 ≤ k := ⟨le_rfl, by omega⟩
  -- `Θ⁻¹(ℓ)_y ≥ ℓ + 1`
  have h1 : (lv σ : ℝ) + 1 ≤ (thInv σ Θ (lv σ)).2 := by
    have hn := c443a hσ hΘ
    have hyl' := lt_trans hys hyl
    simp only [thInv_eq, N.pl] at hn hyl' ⊢
    by_contra hc
    push Not at hc
    rcases clsTh hσ hΘ hA with ⟨i', -, -, -, -, hy⟩ | ⟨-, -, hy, -⟩ | ⟨h1, -⟩ | ⟨hs, -⟩ |
        ⟨hs, -⟩ | ⟨hP', -⟩ | ⟨-, -, -, -, hy, -⟩
    · rw [hy] at hyl' hc
      exact nat_btw (a := lv σ) (n := sval σ i') hyl' hc
    · linarith
    · omega
    · rw [lv_def] at hs; omega
    · rw [lv_def] at hs; omega
    · exact hn hP'
    · linarith
  have hprop := (c442 hσ hΘ).1 (lv σ) (by omega) (by omega) (by linarith) h1
  have hK := hprop k (by omega) le_rfl
  refine ⟨h1, memPU_of hσ (by rw [thInv_eq]; exact th_mem hΘ (spos_mem ⟨by omega, le_rfl⟩)) hK,
    ?_⟩
  -- the points of ranks `r, …, k-1` are canonical
  have hcan : ∀ j : ℕ, rv σ ≤ j → j ≤ k - 1 →
      ∃ i', 1 ≤ i' ∧ i' ≤ k ∧ thInv σ Θ j = ((i' : ℝ), (sval σ i' : ℝ)) ∧
        (thInv σ Θ j).2 = sval σ i' ∧ j < sval σ i' := by
    intro j hj1 hj2
    have hjm : 1 ≤ j ∧ j ≤ k := ⟨by omega, by omega⟩
    have hy := hprop j (by omega) (by omega)
    rw [thInv_eq] at hy ⊢
    rcases clsTh hσ hΘ (spos_mem hjm) with ⟨i', h1, h2, he, -, hy'⟩ | ⟨h1, -⟩ |
        ⟨-, -, -, hy'⟩ | ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨-, -, -, -, hy', -⟩ | ⟨-, -, -, -, hy', -⟩
    · refine ⟨i', h1, h2, he, hy', ?_⟩
      rw [hy'] at hy; exact_mod_cast hy
    · have := sval_spos (σ := σ) hjm; rw [h1, lv_def] at this; omega
    · have : (rv σ : ℝ) ≤ j := by exact_mod_cast hj1
      rw [hr'] at this; push_cast at this; linarith
    · rw [sval_spos hjm] at hs; omega
    · rw [sval_spos hjm] at hs; omega
    · have : (rv σ : ℝ) ≤ j := by exact_mod_cast hj1
      rw [hr'] at this; push_cast at this; linarith
    · have : (rv σ : ℝ) ≤ j := by exact_mod_cast hj1
      rw [hr'] at this; push_cast at this; linarith
  -- upper bound by downward induction
  have hup : ∀ d j : ℕ, j + d = k - 1 → rv σ ≤ j → (thInv σ Θ j).2 ≤ (j : ℝ) + 1 := by
    intro d
    induction d with
    | zero =>
      intro j hj hj1
      obtain ⟨i', h1, h2, -, hy, -⟩ := hcan j hj1 (by omega)
      rw [hy]
      have := (sval_mem (σ := σ) (i := i') ⟨h1, h2⟩).2
      have : sval σ i' ≤ j + 1 := by omega
      exact_mod_cast this
    | succ d ih =>
      intro j hj hj1
      have h' := ih (j + 1) (by omega) (by omega)
      have hlt := thInvy_lt hr (j := j) (by omega) (by omega : j + 1 ≤ k) (Nat.lt_succ_self j)
      obtain ⟨i', -, -, -, hy, -⟩ := hcan j hj1 (by omega)
      obtain ⟨i'', -, -, -, hy', -⟩ := hcan (j + 1) (by omega) (by omega)
      rw [hy] at hlt ⊢
      rw [hy'] at hlt h'
      have : sval σ i' < sval σ i'' := by exact_mod_cast hlt
      have : sval σ i'' ≤ j + 2 := by
        have : (sval σ i'' : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by push_cast at h' ⊢; linarith
        exact_mod_cast this
      have : sval σ i' ≤ j + 1 := by omega
      exact_mod_cast this
  intro j hj1 hj2
  obtain ⟨i', h1', h2', he, hy, hlt⟩ := hcan j hj1 hj2
  have hle := hup (k - 1 - j) j (by omega) hj1
  rw [hy] at hle
  have hle' : sval σ i' ≤ j + 1 := by
    have : (sval σ i' : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have heq : sval σ i' = j + 1 := by omega
  have hi' : i' = spos σ (j + 1) := by rw [← heq, spos_sval ⟨h1', h2'⟩]
  rw [he, sigInv_eq ⟨by omega, by omega⟩, heq, ← hi']

/-- Claim 4.44 (2). A step inside the proof by contradiction of Lemma 4.40 (tex l.1519, Claim 4.44
at l.1591): its hypotheses can never all hold, since a copy meeting `P_V` differs from `Σ` and
`TI.no_copy` refutes it. Used inside `claim_4_44`, `TI.c445a`, `TI.c445b` and `TI.c446`. -/
theorem c444b (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hs : ∃ s : ℕ, up σ < s ∧ s ≤ k ∧ th Θ s ∈ PV439 σ) :
    (th Θ (up σ)).1 ≤ (up σ : ℝ) - 1 ∧ th Θ 1 ∈ PL419 σ ∧
      ∀ i : ℕ, 2 ≤ i → i ≤ bp σ → th Θ i = sig σ (i - 1) := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3; have hr' := N.r
  obtain ⟨s, hs1, hsk, hP⟩ := hs
  have hxs := (PV_bd hσ hP).2.1
  have hU : 1 ≤ up σ ∧ up σ ≤ k := ⟨by omega, by omega⟩
  have hxu := thx_lt hr hU.1 hsk hs1
  have h1 : (th Θ (up σ)).1 ≤ (up σ : ℝ) - 1 := by
    have hn := c443b hσ hΘ
    by_contra hc
    push Not at hc
    rcases clsTh hσ hΘ hU with ⟨i', -, -, -, hx, -⟩ | ⟨-, hx, -⟩ | ⟨h1, -⟩ | ⟨hs, -⟩ |
        ⟨-, -, -, hx⟩ | ⟨-, hx, -⟩ | ⟨hP', -⟩
    · rw [hx] at hxu hc
      exact nat_btw (a := bp σ) (n := i') (by linarith) (by linarith)
    · linarith
    · omega
    · rw [N.su] at hs; omega
    · linarith
    · linarith
    · exact hn hP'
  have hprop := (c442 hσ hΘ).2 (up σ) hU.1 hU.2 (by linarith) h1
  have hA := hprop 1 le_rfl (by omega)
  refine ⟨h1, memPL_of hσ (th_mem hΘ ⟨le_rfl, by omega⟩) (by simpa using hA), ?_⟩
  have hcan : ∀ i : ℕ, 2 ≤ i → i ≤ bp σ →
      ∃ i', 1 ≤ i' ∧ i' ≤ k ∧ th Θ i = ((i' : ℝ), (sval σ i' : ℝ)) ∧
        (th Θ i).1 = i' ∧ i' < i := by
    intro i hi1 hi2
    have him : 1 ≤ i ∧ i ≤ k := ⟨by omega, by omega⟩
    have hx := hprop i (by omega) (by omega)
    have hib : (i : ℝ) ≤ bp σ := by exact_mod_cast hi2
    rcases clsTh hσ hΘ him with ⟨i', h1, h2, he, hx', -⟩ | ⟨h1, -⟩ |
        ⟨h1, -⟩ | ⟨hs, -, hx', -⟩ | ⟨hs, -⟩ | ⟨-, hx', -⟩ | ⟨-, hx', -⟩
    · refine ⟨i', h1, h2, he, hx', ?_⟩
      rw [hx'] at hx; exact_mod_cast hx
    · omega
    · omega
    · linarith
    · have := spos_sval (σ := σ) him; rw [hs, up_def] at this; omega
    · linarith
    · linarith
  have hlow : ∀ i : ℕ, 2 ≤ i → i ≤ bp σ → (i : ℝ) - 1 ≤ (th Θ i).1 := by
    intro i hi1 hi2
    induction i, hi1 using Nat.le_induction with
    | base =>
      obtain ⟨i', h1, -, -, hx, -⟩ := hcan 2 le_rfl hi2
      rw [hx]; have : (1 : ℝ) ≤ i' := by exact_mod_cast h1
      norm_num; linarith
    | succ i hi1 ih =>
      have h' := ih (by omega)
      have hlt := thx_lt hr (i := i) (by omega) (by omega : i + 1 ≤ k) (Nat.lt_succ_self i)
      obtain ⟨i', -, -, -, hx, -⟩ := hcan i hi1 (by omega)
      obtain ⟨i'', -, -, -, hx', -⟩ := hcan (i + 1) (by omega) hi2
      rw [hx] at hlt h'
      rw [hx'] at hlt ⊢
      have : i' < i'' := by exact_mod_cast hlt
      have : i ≤ i' + 1 := by
        have : (i : ℝ) ≤ ((i' + 1 : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      have : i ≤ i'' := by omega
      have : (i : ℝ) ≤ i'' := by exact_mod_cast this
      push_cast; linarith
  intro i hi1 hi2
  obtain ⟨i', h1', h2', he, hx, hlt⟩ := hcan i hi1 hi2
  have hle := hlow i hi1 hi2
  rw [hx] at hle
  have : i ≤ i' + 1 := by
    have : (i : ℝ) ≤ ((i' + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have heq : i' = i - 1 := by omega
  rw [he, sig_eq ⟨by omega, by omega⟩, heq]


/-! ### Claims 4.45 and 4.46 -/

theorem c445a (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ)) :
    ∀ s : ℕ, 1 ≤ s → s < lv σ → thInv σ Θ s ∈ PH439 σ →
      ∀ t : ℕ, s ≤ t → t < lv σ → thInv σ Θ t ∈ PH439 σ := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3; have hr' := N.r
  intro s hs1 hsl hP t hst htl
  have h44 := (c444a hσ hΘ ⟨s, hs1, hsl, hP⟩).2.2 (rv σ) le_rfl (by omega)
  have hrm : 1 ≤ rv σ + 1 ∧ rv σ + 1 ≤ k := ⟨by omega, by omega⟩
  rw [sigInv_eq hrm] at h44
  have hyr := thInvy_lt hr (j := t) (by omega) (by omega : rv σ ≤ k) (by omega)
  have hyt := thInvy_le hr hs1 hst (by omega)
  have hys := (PH_bd hP).2.2.1
  have htm : 1 ≤ t ∧ t ≤ k := ⟨by omega, by omega⟩
  have hspt := spos_mem (σ := σ) htm
  have hpt : spos σ t < k := by
    rcases lt_or_eq_of_le hspt.2 with h | h
    · exact h
    · exfalso
      have := sval_spos (σ := σ) htm
      rw [h, N.sk] at this; omega
  -- `Θ⁻¹(t)` lies to the left of `Θ(k) = Θ⁻¹(r)`, whose `x`-coordinate is at most `k`
  have hxt : (thInv σ Θ t).1 < k := by
    have h1 := thx_lt hr hspt.1 le_rfl hpt
    have h2 : thInv σ Θ (rv σ) = th Θ k := by rw [thInv_eq, hr', N.pr]
    rw [← h2, h44] at h1
    have : (spos σ (rv σ + 1) : ℝ) ≤ k := by exact_mod_cast spos_le σ _
    rw [thInv_eq]; simp only at h1; linarith
  rw [h44] at hyr
  simp only at hyr
  simp only [thInv_eq] at hyr hyt hxt hys ⊢
  rcases clsTh hσ hΘ hspt with ⟨i', h1, h2, -, hx, hy⟩ | ⟨h1, -⟩ | ⟨-, -, -, hy⟩ | ⟨-, hy, -⟩ |
      ⟨-, hy, -⟩ | ⟨hP', -⟩ | ⟨-, -, -, -, hy, -⟩
  · rw [hy] at hyr hyt
    have a1 : lv σ < sval σ i' := by exact_mod_cast (lt_of_lt_of_le hys hyt)
    have a2 : sval σ i' < rv σ + 1 := by exact_mod_cast hyr
    have : sval σ i' = rv σ := by omega
    have : i' = k := by
      have := spos_sval (σ := σ) ⟨h1, h2⟩; rw [‹sval σ i' = rv σ›, hr', N.pr] at this
      exact this.symm
    rw [hx, this] at hxt; exact absurd hxt (lt_irrefl _)
  · have := sval_spos (σ := σ) htm; rw [h1, lv_def] at this; omega
  · linarith
  · linarith
  · have : (rv σ : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : rv σ + 1 ≤ k)
    push_cast at hyr; linarith
  · exact hP'
  · linarith

theorem c445b (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ)) :
    ∀ s : ℕ, up σ < s → s ≤ k → th Θ s ∈ PV439 σ →
      ∀ t : ℕ, up σ < t → t ≤ s → th Θ t ∈ PV439 σ := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3; have hr' := N.r
  intro s hs1 hsk hP t hts hst
  have h44 := (c444b hσ hΘ ⟨s, hs1, hsk, hP⟩).2.2 (bp σ) hb' le_rfl
  have hbm : 1 ≤ bp σ - 1 ∧ bp σ - 1 ≤ k := ⟨by omega, by omega⟩
  rw [sig_eq hbm] at h44
  have htm : 1 ≤ t ∧ t ≤ k := ⟨by omega, by omega⟩
  have hbm' : 1 ≤ bp σ ∧ bp σ ≤ k := ⟨by omega, by omega⟩
  have hxb := thx_lt hr (i := bp σ) (by omega) htm.2 (by omega)
  have hxs := thx_le hr (s := t) (by omega) hst hsk
  have hxs' := (PV_bd hσ hP).2.1
  have hst1 : sval σ t ≠ 1 := by
    intro h; have := spos_sval (σ := σ) htm; rw [h, bp_def] at this; omega
  have hyb := thy_lt hr hbm' htm (by rw [N.sb]; have := (sval_mem (σ := σ) htm).1; omega)
  rw [h44] at hxb hyb
  simp only at hxb hyb
  have hsb1 : (1 : ℝ) ≤ sval σ (bp σ - 1) := by exact_mod_cast (sval_mem hbm).1
  rw [Nat.cast_sub (by omega)] at hxb
  push_cast at hxb
  rcases clsTh hσ hΘ htm with ⟨i', h1, h2, -, hx, hy⟩ | ⟨h1, -⟩ | ⟨-, hx, -⟩ | ⟨hs, -⟩ |
      ⟨hs, -⟩ | ⟨-, hx, -⟩ | ⟨hP', -⟩
  · rw [hx] at hxb hxs
    have a1 : bp σ < i' + 1 := by
      have : (bp σ : ℝ) < i' + 1 := by linarith
      exact_mod_cast this
    have a2 : i' < bp σ + 1 := by
      have : (i' : ℝ) < bp σ + 1 := by linarith
      exact_mod_cast this
    have : i' = bp σ := by omega
    rw [hy, this, N.sb] at hyb
    push_cast at hyb; linarith
  · omega
  · linarith
  · exact absurd hs hst1
  · have := spos_sval (σ := σ) htm; rw [hs, up_def] at this; omega
  · linarith
  · exact hP'

theorem c446 (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ)) :
    (∀ s : ℕ, 1 ≤ s → s ≤ lv σ → thInv σ Θ s ∉ PH439 σ) ∧
    (∀ s : ℕ, up σ ≤ s → s ≤ k → th Θ s ∉ PV439 σ) := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3; have hr' := N.r
  obtain ⟨hp1, hp2⟩ := hσ.pos
  obtain ⟨hv1, hv2⟩ := hσ.val
  constructor
  · intro s hs1 hsl hP
    rcases eq_or_lt_of_le hsl with rfl | hlt
    · exact c443a hσ hΘ hP
    have hP' := c445a hσ hΘ s hs1 hlt hP (lv σ - 1) (by omega) (by omega)
    have h44 := (c444a hσ hΘ ⟨s, hs1, hlt, hP⟩).2.2 (k - 1) (by omega) le_rfl
    rw [show k - 1 + 1 = k by omega, sigInv_eq ⟨by omega, le_rfl⟩, up_def] at h44
    have hx1 := (PH_bd hP').1
    have hx2 : (thInv σ Θ (k - 1)).1 < (thInv σ Θ (lv σ - 1)).1 := by
      rw [h44]; simp only; linarith
    rw [thInv_eq, thInv_eq] at hx2
    have := (thx_lt_iff hr (spos_mem ⟨by omega, by omega⟩) (spos_mem ⟨by omega, by omega⟩)).1 hx2
    omega
  · intro s hs1 hsk hP
    rcases eq_or_lt_of_le hs1 with rfl | hlt
    · exact c443b hσ hΘ hP
    have hP' := c445b hσ hΘ s hlt hsk hP (up σ + 1) (by omega) (by omega)
    have h44 := (c444b hσ hΘ ⟨s, hlt, hsk, hP⟩).2.2 2 le_rfl (by omega)
    rw [sig_eq ⟨le_rfl, by omega⟩, lv_def] at h44
    have hy1 := (PV_bd hσ hP').2.2.2.1
    have hy2 : (th Θ (up σ + 1)).2 < (th Θ 2).2 := by
      rw [h44]; simp only; linarith
    have := (thy_lt_iff hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).1 hy2
    omega


/-! ### (4.25): `Θ` meets `P_H ∪ P_V` (via Lemma 4.20) -/

/-- A finite point set with pairwise distinct `x`-coordinates and pairwise distinct
`y`-coordinates is associated with a permutation. -/
theorem permPointSet_of_inj (P : Finset (ℝ × ℝ))
    (hx : ∀ p ∈ P, ∀ q ∈ P, p.1 = q.1 → p = q) (hy : ∀ p ∈ P, ∀ q ∈ P, p.2 = q.2 → p = q) :
    IsPermPointSet P := by
  classical
  have hX : (P.image Prod.fst).card = P.card :=
    Finset.card_image_of_injOn (fun p hp q hq h => hx p hp q hq h)
  have hY : (P.image Prod.snd).card = P.card :=
    Finset.card_image_of_injOn (fun p hp q hq h => hy p hp q hq h)
  set fx := (P.image Prod.fst).orderEmbOfFin hX
  set fy := (P.image Prod.snd).orderEmbOfFin hY
  have hex : ∀ i, ∃ p ∈ P, p.1 = fx i := fun i =>
    Finset.mem_image.mp ((P.image Prod.fst).orderEmbOfFin_mem hX i)
  choose Θ hΘP hΘx using hex
  have hey : ∀ i, ∃ j, fy j = (Θ i).2 := by
    intro i
    have hm : (Θ i).2 ∈ (↑(P.image Prod.snd) : Set ℝ) :=
      Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (hΘP i))
    rw [← Finset.range_orderEmbOfFin _ hY] at hm
    exact hm
  choose π0 hπ0 using hey
  have hΘinj : Function.Injective Θ := by
    intro a b h
    have : fx a = fx b := by rw [← hΘx a, ← hΘx b, h]
    exact fx.injective this
  have hinj : Function.Injective π0 := by
    intro a b h
    have : (Θ a).2 = (Θ b).2 := by rw [← hπ0 a, ← hπ0 b, h]
    exact hΘinj (hy _ (hΘP a) _ (hΘP b) this)
  refine ⟨Equiv.ofBijective π0 (Finite.injective_iff_bijective.mp hinj), Θ, ⟨?_, ?_⟩, ?_⟩
  · intro a b hab
    simp only [hΘx]
    exact fx.strictMono hab
  · intro a b
    rw [← hπ0 a, ← hπ0 b]
    exact fy.lt_iff_lt
  · symm
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
      exact hΘP a
    · rw [Finset.card_image_of_injective _ hΘinj]; simp

theorem canon_int {σ : Perm (Fin k)} {p : ℝ × ℝ} (hp : p ∈ canon σ) :
    (∃ m : ℕ, p.1 = m) ∧ (∃ m : ℕ, p.2 = m) := by
  obtain ⟨i, -, -, rfl⟩ := mem_canon.mp hp
  exact ⟨⟨i, rfl⟩, ⟨sval σ i, rfl⟩⟩

theorem canon_inj {σ : Perm (Fin k)} {p q : ℝ × ℝ} (hp : p ∈ canon σ) (hq : q ∈ canon σ) :
    (p.1 = q.1 → p = q) ∧ (p.2 = q.2 → p = q) := by
  obtain ⟨i, hi1, hi2, rfl⟩ := mem_canon.mp hp
  obtain ⟨j, hj1, hj2, rfl⟩ := mem_canon.mp hq
  constructor
  · intro h
    have : i = j := by simp only at h; exact_mod_cast h
    rw [this]
  · intro h
    have : sval σ i = sval σ j := by simp only at h; exact_mod_cast h
    rw [sval_inj ⟨hi1, hi2⟩ ⟨hj1, hj2⟩ this]

/-- (4.25) in its weak form: an additional copy uses `P_H` or `P_V` (otherwise it lies in the
support of Construction 4.19, and Lemma 4.20 applies to `Σ ∪ Θ`). -/
theorem meets (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hne : Finset.univ.image Θ ≠ canon σ) :
    (∃ i, 1 ≤ i ∧ i ≤ k ∧ th Θ i ∈ PH439 σ) ∨ (∃ i, 1 ≤ i ∧ i ≤ k ∧ th Θ i ∈ PV439 σ) := by
  classical
  by_contra hc
  push Not at hc
  obtain ⟨hcH, hcV⟩ := hc
  have hD : ∀ a, Θ a ∈ D419 σ := by
    intro a
    have h1 := hΘ.2 a
    rw [← th_succ Θ a] at h1 ⊢
    rcases h1 with (h | h) | h
    · exact h
    · exact absurd h (hcH _ (by omega) (by omega))
    · exact absurd h (hcV _ (by omega) (by omega))
  -- the points of `Θ` outside `Σ` have non-integral coordinates
  have hni : ∀ a, Θ a ∉ canon σ → (∀ m : ℤ, (Θ a).1 ≠ m) ∧ (∀ m : ℤ, (Θ a).2 ≠ m) := by
    intro a hna
    rcases hD a with (((h | h) | h) | h) | h
    · exact absurd (Finset.mem_coe.mp h) hna
    · exact (PL_bd hσ h).2.2.2
    · exact (PR_bd hσ h).2.2.2
    · exact (PB_bd hσ h).2.2.2
    · exact (PU_bd hσ h).2.2.2
  set P := canon σ ∪ Finset.univ.image Θ with hPdef
  have hmem : ∀ p ∈ P, p ∈ canon σ ∨ ∃ a, p = Θ a ∧ Θ a ∉ canon σ := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Or.inl h
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      by_cases hc : Θ a ∈ canon σ
      · exact Or.inl hc
      · exact Or.inr ⟨a, rfl, hc⟩
  have hinjΘ : ∀ a b, ((Θ a).1 = (Θ b).1 → a = b) ∧ ((Θ a).2 = (Θ b).2 → a = b) := by
    intro a b
    refine ⟨fun h => hΘ.1.1.injective h, fun h => ?_⟩
    have h1 := (hΘ.1.2 a b).not.mp (by rw [h]; exact lt_irrefl _)
    have h2 := (hΘ.1.2 b a).not.mp (by rw [h]; exact lt_irrefl _)
    exact σ.injective (le_antisymm (not_lt.mp h2) (not_lt.mp h1))
  have hPP : IsPermPointSet P := by
    apply permPointSet_of_inj
    · intro p hp q hq h
      rcases hmem p hp with hp' | ⟨a, rfl, ha⟩ <;> rcases hmem q hq with hq' | ⟨b, rfl, hb⟩
      · exact (canon_inj hp' hq').1 h
      · obtain ⟨⟨m, hm⟩, -⟩ := canon_int hp'
        exact absurd (h.symm.trans hm) (nonint_ne (hni b hb).1 m)
      · obtain ⟨⟨m, hm⟩, -⟩ := canon_int hq'
        exact absurd (h.trans hm) (nonint_ne (hni a ha).1 m)
      · rw [(hinjΘ a b).1 h]
    · intro p hp q hq h
      rcases hmem p hp with hp' | ⟨a, rfl, ha⟩ <;> rcases hmem q hq with hq' | ⟨b, rfl, hb⟩
      · exact (canon_inj hp' hq').2 h
      · obtain ⟨-, ⟨m, hm⟩⟩ := canon_int hp'
        exact absurd (h.symm.trans hm) (nonint_ne (hni b hb).2 m)
      · obtain ⟨-, ⟨m, hm⟩⟩ := canon_int hq'
        exact absurd (h.trans hm) (nonint_ne (hni a ha).2 m)
      · rw [(hinjΘ a b).2 h]
  have h1 : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P := by
    intro p hp; exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_coe.mp hp))
  have h2 : (↑P : Set (ℝ × ℝ)) ⊆ D419 σ := by
    intro p hp
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hp) with h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_coe.mpr h))))
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact hD a
  have hU := lemma_4_20 σ hσ.standing P hPP h1 h2
  exact hne (hU.2 Θ ⟨hΘ.1, fun a => Finset.mem_coe.mpr
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))⟩)


/-! ### The two bounds used by Claims 4.47–4.49 -/

theorem ky_of_kx (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hx : (bp σ : ℝ) < (th Θ (up σ)).1) : (thInv σ Θ (lv σ)).2 < (lv σ : ℝ) + 1 := by
  have N := nums hσ
  have hk' := N.k5; have hlk' := N.lk; have hl3' := N.l3; have huk' := N.uk
  by_contra hc
  push Not at hc
  have hK := (c442 hσ hΘ).1 (lv σ) (by omega) (by omega) (by linarith) hc k (by omega) le_rfl
  have hPU := PU_bd hσ (memPU_of hσ (by rw [thInv_eq]; exact th_mem hΘ (spos_mem
    ⟨by omega, le_rfl⟩)) hK)
  rw [thInv_eq, up_def] at hPU
  linarith [hPU.2.2.1]

theorem kx_of_ky (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hy : (thInv σ Θ (lv σ)).2 < (lv σ : ℝ) + 1) : (bp σ : ℝ) < (th Θ (up σ)).1 := by
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk
  by_contra hc
  push Not at hc
  have hA := (c442 hσ hΘ).2 (up σ) (by omega) (by omega) (by linarith) (by linarith) 1 le_rfl
    (by omega)
  have hPL := PL_bd hσ (memPL_of hσ (th_mem hΘ ⟨le_rfl, by omega⟩) (by simpa using hA))
  rw [thInv_eq, N.pl] at hy
  linarith [hPL.2.1]

theorem kykx (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hne : Finset.univ.image Θ ≠ canon σ) :
    (thInv σ Θ (lv σ)).2 < (lv σ : ℝ) + 1 ∧ (bp σ : ℝ) < (th Θ (up σ)).1 := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hl3' := N.l3
  rcases meets hσ hΘ hne with ⟨i, hi1, hi2, hP⟩ | ⟨i, hi1, hi2, hP⟩
  · have hy : (thInv σ Θ (lv σ)).2 < (lv σ : ℝ) + 1 := by
      have hsm := sval_mem (σ := σ) ⟨hi1, hi2⟩
      have hth : thInv σ Θ (sval σ i) = th Θ i := by rw [thInv_eq, spos_sval ⟨hi1, hi2⟩]
      have hgt : lv σ < sval σ i := by
        by_contra hc
        exact (c446 hσ hΘ).1 (sval σ i) hsm.1 (by omega) (hth ▸ hP)
      have := thInvy_lt hr (j := lv σ) (by omega) hsm.2 hgt
      rw [hth] at this
      linarith [(PH_bd hP).2.2.2.1]
    exact ⟨hy, kx_of_ky hσ hΘ hy⟩
  · have hx : (bp σ : ℝ) < (th Θ (up σ)).1 := by
      have hlt : i < up σ := by
        by_contra hc
        exact (c446 hσ hΘ).2 i (by omega) hi2 hP
      have := thx_lt hr hi1 (by omega) hlt
      linarith [(PV_bd hσ hP).1]
    exact ⟨ky_of_kx hσ hΘ hx, hx⟩

/-! ### Claims 4.47 and 4.48 -/

/-- The index set of `Σ_BR`: `u + 1 ≤ i ≤ k - 1` and `2 ≤ σ(i) ≤ ℓ - 1`. -/
def BR (σ : Perm (Fin k)) (i : ℕ) : Prop :=
  up σ + 1 ≤ i ∧ i ≤ k - 1 ∧ 2 ≤ sval σ i ∧ sval σ i ≤ lv σ - 1

theorem c447 (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hne : Finset.univ.image Θ ≠ canon σ) {i : ℕ} (hi : BR σ i) :
    ∃ i', BR σ i' ∧ th Θ i = sig σ i' := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3; have hr' := N.r
  obtain ⟨hKy, hKx⟩ := kykx hσ hΘ hne
  obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
  have him : 1 ≤ i ∧ i ≤ k := ⟨by omega, by omega⟩
  have hnV := (c446 hσ hΘ).2 i (by omega) him.2
  have hnH : th Θ i ∉ PH439 σ := by
    have := (c446 hσ hΘ).1 (sval σ i) (by omega) (by omega)
    rwa [thInv_eq, spos_sval him] at this
  have hxi := thx_lt hr (i := up σ) (by omega) him.2 (by omega)
  have hyi := thy_lt hr him ⟨le_rfl, by omega⟩ (by rw [lv_def]; omega)
  have h1l : th Θ 1 = thInv σ Θ (lv σ) := by rw [thInv_eq, N.pl]
  rw [h1l] at hyi
  rcases clsTh hσ hΘ him with ⟨i', h1, h2, he, hx, hy⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨hs, -⟩ |
      ⟨hs, -⟩ | ⟨hP, -⟩ | ⟨hP, -⟩
  · rw [hx] at hxi
    rw [hy] at hyi
    have a1 : bp σ < i' := by
      have : (bp σ : ℝ) < i' := by linarith
      exact_mod_cast this
    have a2 : sval σ i' < lv σ + 1 := by
      have : (sval σ i' : ℝ) < lv σ + 1 := by linarith
      exact_mod_cast this
    have hu1 : i' ≠ up σ := by intro h; rw [h, N.su] at a2; omega
    have hk1 : i' ≠ k := by intro h; rw [h, N.sk] at a2; omega
    have hs1 : sval σ i' ≠ 1 := by
      intro h; have := spos_sval (σ := σ) ⟨h1, h2⟩; rw [h, bp_def] at this; omega
    have hsl : sval σ i' ≠ lv σ := by
      intro h; have := spos_sval (σ := σ) ⟨h1, h2⟩; rw [h, N.pl] at this; omega
    have := (sval_mem (σ := σ) ⟨h1, h2⟩).1
    refine ⟨i', ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
    rw [he, sig_eq ⟨h1, h2⟩]
  · omega
  · omega
  · omega
  · omega
  · exact absurd hP hnH
  · exact absurd hP hnV

/-- A strictly increasing self-map of a finite set of naturals is the identity on it. -/
theorem smono_fix (I : Finset ℕ) (φ : ℕ → ℕ) (hmap : ∀ i ∈ I, φ i ∈ I)
    (hmono : ∀ i ∈ I, ∀ j ∈ I, i < j → φ i < φ j) : ∀ i ∈ I, φ i = i := by
  have hge : ∀ i ∈ I, i ≤ φ i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_contra hc
      push Not at hc
      have h1 := ih (φ i) hc (hmap i hi)
      have h2 := hmono (φ i) (hmap i hi) i hi hc
      omega
  have hinj : Set.InjOn φ I := by
    intro i hi j hj h
    by_contra hc
    rcases lt_or_gt_of_ne hc with h' | h'
    · exact absurd h (hmono i hi j hj h').ne
    · exact absurd h (hmono j hj i hi h').ne'
  have himg : I.image φ = I := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hmap i hi
    · rw [Finset.card_image_of_injOn hinj]
  have hsum : ∑ i ∈ I, i = ∑ i ∈ I, φ i := by
    have := Finset.sum_image (f := fun x => x) hinj
    rw [himg] at this
    exact this
  intro i hi
  exact ((Finset.sum_eq_sum_iff_of_le hge).mp hsum i hi).symm

theorem c448 (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hne : Finset.univ.image Θ ≠ canon σ) {i : ℕ} (hi : BR σ i) : th Θ i = sig σ i := by
  classical
  have hr := hΘ.1
  have N := nums hσ
  have hk' := N.k5; have hu' := N.u
  have hBRk : ∀ {j}, BR σ j → 1 ≤ j ∧ j ≤ k := fun h => ⟨by have := h.1; omega, by
    have := h.2.1; omega⟩
  set I := (Finset.Icc 1 k).filter (BR σ)
  have hfl : ∀ j, BR σ j → BR σ ⌊(th Θ j).1⌋₊ ∧ th Θ j = sig σ ⌊(th Θ j).1⌋₊ := by
    intro j hj
    obtain ⟨i', hB, he⟩ := c447 hσ hΘ hne hj
    have : ⌊(th Θ j).1⌋₊ = i' := by rw [he, sig_eq (hBRk hB)]; simp
    rw [this]; exact ⟨hB, he⟩
  have hmapI : ∀ j ∈ I, ⌊(th Θ j).1⌋₊ ∈ I := by
    intro j hj
    have h := (hfl j (Finset.mem_filter.mp hj).2).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (hBRk h), h⟩
  have hmonoI : ∀ j ∈ I, ∀ j' ∈ I, j < j' → ⌊(th Θ j).1⌋₊ < ⌊(th Θ j').1⌋₊ := by
    intro j hj j' hj' hlt
    have hjB := hfl j (Finset.mem_filter.mp hj).2
    have hjB' := hfl j' (Finset.mem_filter.mp hj').2
    have hx := thx_lt hr (hBRk (Finset.mem_filter.mp hj).2).1
      (hBRk (Finset.mem_filter.mp hj').2).2 hlt
    rw [hjB.2, hjB'.2, sig_eq (hBRk hjB.1), sig_eq (hBRk hjB'.1)] at hx
    simp only at hx
    exact_mod_cast hx
  have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (hBRk hi), hi⟩
  have hfix := smono_fix I _ hmapI hmonoI i hiI
  have h := (hfl i hi).2
  rw [hfix] at h
  exact h


/-! ### Claim 4.49 -/

theorem ud_anti (hσ : Hyp440 σ) {j j' : ℕ} (hj : rv σ ≤ j) (hjj : j ≤ j') (hj' : j' ≤ k) :
    spos σ j' ≤ spos σ j := by
  induction j', hjj using Nat.le_induction with
  | base => exact le_rfl
  | succ j' hjj ih => exact (hσ.ud j' (by omega) (by omega)).le.trans (ih (by omega))

theorem ld_anti (hσ : Hyp440 σ) {i i' : ℕ} (hi : 1 ≤ i) (hii : i ≤ i') (hi' : i' ≤ bp σ) :
    sval σ i' ≤ sval σ i := by
  induction i', hii using Nat.le_induction with
  | base => exact le_rfl
  | succ i' hii ih => exact (hσ.ld i' (by omega) (by omega)).le.trans (ih (by omega))

theorem c449a (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hne : Finset.univ.image Θ ≠ canon σ) : thInv σ Θ (rv σ) ∉ PH439 σ := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3; have hr' := N.r
  obtain ⟨hKy, hKx⟩ := kykx hσ hΘ hne
  intro hP
  rw [thInv_eq, hr', N.pr] at hP
  obtain ⟨hxK, hxK', hyK, hyK', hlK⟩ := PH_bd hP
  have hM : 1 ≤ k - 1 ∧ k - 1 ≤ k := ⟨by omega, by omega⟩
  have hK : 1 ≤ k ∧ k ≤ k := ⟨by omega, le_rfl⟩
  have hxM := thx_lt hr hM.1 le_rfl (by omega : k - 1 < k)
  set m := sval σ (k - 1) with hm
  have hmm := sval_mem (σ := σ) hM
  have hm1 : m ≠ lv σ := by
    intro h; have := spos_sval (σ := σ) hM; rw [← hm, h, N.pl] at this; omega
  have hm2 : m ≠ lv σ + 1 := by
    intro h; have := spos_sval (σ := σ) hM; rw [← hm, h, N.pr] at this; omega
  rcases lt_or_gt_of_ne hm1 with hlt | hgt
  · -- `σ(k-1) ≤ ℓ - 1`: Corollary 4.48 pins `Θ(k-1)`
    have hm0 : m ≠ 1 := by
      intro h; have := spos_sval (σ := σ) hM; rw [← hm, h, bp_def] at this; omega
    have h48 := c448 hσ hΘ hne (i := k - 1) ⟨by omega, le_rfl, by omega, by omega⟩
    rw [h48, sig_eq hM] at hxM
    simp only at hxM
    rw [Nat.cast_sub (by omega)] at hxM
    push_cast at hxM
    linarith
  · -- `σ(k-1) ≥ r + 1`: (UD) forces `σ(k-1) = r + 1`
    have hmr : m = lv σ + 2 := by
      have h1 := ud_anti hσ (j := rv σ + 1) (j' := m) (by omega) (by omega) hmm.2
      have h2 := hσ.ud (rv σ) le_rfl (by omega)
      rw [hr', N.pr, show lv σ + 1 + 1 = lv σ + 2 by ring] at h2
      rw [hm, spos_sval hM, hr', show lv σ + 1 + 1 = lv σ + 2 by ring] at h1
      have h3 : spos σ (lv σ + 2) = k - 1 := by omega
      have := sval_spos (σ := σ) (j := lv σ + 2) ⟨by omega, by omega⟩
      rw [h3] at this; omega
    have hyM := thy_lt hr hK hM (by rw [N.sk, ← hm, hmr]; omega)
    have hPU : (lv σ : ℝ) + 2 < (th Θ (k - 1)).2 := by
      rcases clsTh hσ hΘ hM with ⟨i', h1, h2, -, hx, hy⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨hs, -⟩ |
          ⟨hs, -⟩ | ⟨hP', -, -, -, -, hl'⟩ | ⟨-, -, -, -, hy, -⟩
      · rw [hx] at hxM
        rw [hy] at hyM ⊢
        have a1 : i' < k - 1 := by
          have : (i' : ℝ) < k - 1 := by linarith
          have : (i' : ℝ) + 1 < k := by linarith
          have : i' + 1 < k := by exact_mod_cast this
          omega
        have a2 : lv σ < sval σ i' := by
          have : (lv σ : ℝ) < sval σ i' := by linarith
          exact_mod_cast this
        have a3 : sval σ i' ≠ lv σ + 1 := by
          intro h; have := spos_sval (σ := σ) ⟨h1, h2⟩; rw [h, N.pr] at this; omega
        have a4 : sval σ i' ≠ lv σ + 2 := by
          intro h; have := spos_sval (σ := σ) ⟨h1, h2⟩; rw [h, ← hmr, hm, spos_sval hM] at this
          omega
        have : lv σ + 2 < sval σ i' := by omega
        exact_mod_cast this
      · omega
      · omega
      · rw [← hm] at hs; omega
      · rw [← hm] at hs
        have := spos_sval (σ := σ) hM; rw [← hm, hs, up_def] at this; omega
      · linarith
      · linarith
    -- propagation from rank `r + 1` up to rank `k`
    have hth : thInv σ Θ (lv σ + 2) = th Θ (k - 1) := by
      rw [thInv_eq, ← hmr, hm, spos_sval hM]
    have hprop := (c442 hσ hΘ).1 (lv σ + 2) (by omega) (by omega) (by rw [hth]; push_cast; linarith)
      (by rw [hth]; linarith) k (by omega) le_rfl
    have hPU' := PU_bd hσ (memPU_of hσ (by rw [thInv_eq]; exact th_mem hΘ (spos_mem
      ⟨by omega, le_rfl⟩)) hprop)
    rw [thInv_eq, up_def] at hPU'
    linarith [hPU'.2.2.1]

theorem c449b (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hne : Finset.univ.image Θ ≠ canon σ) : th Θ (bp σ) ∉ PV439 σ := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3; have hr' := N.r
  obtain ⟨hKy, hKx⟩ := kykx hσ hΘ hne
  intro hP
  obtain ⟨hxB, hxB', hyB, hyB', hlB⟩ := PV_bd hσ hP
  have h2m : 1 ≤ 2 ∧ 2 ≤ k := ⟨by omega, by omega⟩
  have hBm : 1 ≤ bp σ ∧ bp σ ≤ k := ⟨by omega, by omega⟩
  set p := spos σ 2 with hp
  have hpm := spos_mem (σ := σ) h2m
  have hsp : sval σ p = 2 := sval_spos h2m
  have hyP := thy_lt hr hBm hpm (by rw [N.sb, hsp]; omega)
  have hpb : p ≠ bp σ := by intro h; rw [h, N.sb] at hsp; omega
  have hpu : p ≠ up σ := by intro h; rw [h, N.su] at hsp; omega
  have hp1 : p ≠ 1 := by intro h; rw [h, lv_def] at hsp; omega
  have hpk : p ≠ k := by intro h; rw [h, N.sk] at hsp; omega
  rcases lt_or_gt_of_ne hpb with hlt | hgt
  · -- `σ⁻¹(2) < b`: (LD) forces `σ⁻¹(2) = b - 1`
    have hpb1 : p = bp σ - 1 := by
      have h1 := ld_anti hσ (i := p) (i' := bp σ - 1) hpm.1 (by omega) (by omega)
      have h2 := hσ.ld (bp σ - 1) (by omega) (by omega)
      rw [show bp σ - 1 + 1 = bp σ by omega, N.sb] at h2
      rw [hsp] at h1
      have h3 : sval σ (bp σ - 1) = 2 := by omega
      have := spos_sval (σ := σ) (i := bp σ - 1) ⟨by omega, by omega⟩
      rw [h3] at this; omega
    have hxP := thx_lt hr hpm.1 hBm.2 hlt
    have hxPi : (th Θ p).1 < p := by
      rcases clsTh hσ hΘ hpm with ⟨i', h1, h2, -, hx, hy⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨hs, -⟩ |
          ⟨hs, -⟩ | ⟨-, hx, -⟩ | ⟨hP', -, -, -, -, hl'⟩
      · rw [hx] at hxP ⊢
        rw [hy] at hyP
        have a1 : i' ≤ bp σ := by
          have : (i' : ℝ) < bp σ + 1 := by linarith
          have : i' < bp σ + 1 := by exact_mod_cast this
          omega
        have a2 : 2 < sval σ i' := by
          have : (2 : ℝ) < sval σ i' := by linarith
          exact_mod_cast this
        have a3 : i' ≠ bp σ := by intro h; rw [h, N.sb] at a2; omega
        have a4 : i' ≠ bp σ - 1 := by intro h; rw [h, ← hpb1, hsp] at a2; omega
        have : i' < p := by omega
        exact_mod_cast this
      · exact absurd h1 hp1
      · exact absurd h1 hpk
      · rw [hsp] at hs; omega
      · rw [hsp] at hs; omega
      · linarith
      · linarith
    have hA := (c442 hσ hΘ).2 p hpm.1 hpm.2 hxPi (by
      have : (p : ℝ) + 2 ≤ up σ := by exact_mod_cast (by omega : p + 2 ≤ up σ)
      linarith) 1 le_rfl hpm.1
    have hPL := PL_bd hσ (memPL_of hσ (th_mem hΘ ⟨le_rfl, by omega⟩) (by simpa using hA))
    rw [thInv_eq, N.pl] at hKy
    linarith [hPL.2.1]
  · -- `σ⁻¹(2) > u`: Corollary 4.48 pins `Θ⁻¹(2)`
    have hgt' : up σ < p := by omega
    have h48 := c448 hσ hΘ hne (i := p) ⟨by omega, by omega, by omega, by omega⟩
    rw [h48, sig_eq hpm, hsp] at hyP
    simp only at hyP
    push_cast at hyP
    linarith


/-! ### Claim 4.50 and the final contradiction -/

/-- First half of Claim 4.50 (tex l.1705), from a point of `Θ` on `P_H`. A step of the proof by
contradiction of Lemma 4.40 (tex l.1519): its hypotheses can never all hold, since `lemma_4_40`
shows `Σ` is the only copy and `Σ` has no point on `P_H` (`hH` fails even with `hne` set aside), so
it holds only vacuously. Used only inside `TI.meets_both` and `TI.no_copy`. -/
theorem c450y (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hne : Finset.univ.image Θ ≠ canon σ) (hH : ∃ i, 1 ≤ i ∧ i ≤ k ∧ th Θ i ∈ PH439 σ) :
    (lv σ : ℝ) - 1 < (thInv σ Θ (lv σ)).2 ∧ (thInv σ Θ (lv σ)).2 < (lv σ : ℝ) := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3; have hr' := N.r
  obtain ⟨i, hi1, hi2, hP⟩ := hH
  have hsm := sval_mem (σ := σ) ⟨hi1, hi2⟩
  have hth : thInv σ Θ (sval σ i) = th Θ i := by rw [thInv_eq, spos_sval ⟨hi1, hi2⟩]
  have hgt : lv σ < sval σ i := by
    by_contra hc
    exact (c446 hσ hΘ).1 (sval σ i) hsm.1 (by omega) (hth ▸ hP)
  have hyr := thInvy_le hr (j := rv σ) (s := sval σ i) (by omega) (by omega) hsm.2
  rw [hth] at hyr
  have hyr' := (PH_bd hP).2.2.2.1
  have hthr : thInv σ Θ (rv σ) = th Θ k := by rw [thInv_eq, hr', N.pr]
  have hn := c449a hσ hΘ hne
  rw [hthr] at hyr hn
  have hK : 1 ≤ k ∧ k ≤ k := ⟨by omega, le_rfl⟩
  -- `Θ⁻¹(r)_y ≤ ℓ`, since only `P_H` meets the strip `ℓ < y < ℓ + 1`
  have hle : (th Θ k).2 ≤ lv σ := by
    by_contra hc
    push Not at hc
    rcases clsTh hσ hΘ hK with ⟨i', -, -, -, -, hy⟩ | ⟨h1, -⟩ | ⟨-, -, -, hy⟩ | ⟨-, hy, -⟩ |
        ⟨-, hy, -⟩ | ⟨hP', -⟩ | ⟨-, -, -, -, hy, -⟩
    · rw [hy] at hc hyr
      exact nat_btw (a := lv σ) (n := sval σ i') hc (by linarith)
    · omega
    · linarith
    · linarith
    · linarith
    · exact hn hP'
    · linarith
  have hlt := thInvy_lt hr (j := lv σ) (by omega) (by omega : rv σ ≤ k) (by omega)
  rw [hthr] at hlt
  refine ⟨?_, by linarith⟩
  -- `Θ⁻¹(ℓ-1) = Σ⁻¹(ℓ-1)` by Corollary 4.48
  obtain ⟨hp1, hp2⟩ := hσ.pos
  have hlm : 1 ≤ lv σ - 1 ∧ lv σ - 1 ≤ k := ⟨by omega, by omega⟩
  have hpm := spos_mem (σ := σ) hlm
  have hq := spos_le σ (k - 1)
  have h48 := c448 hσ hΘ hne (i := spos σ (lv σ - 1))
    ⟨by omega, by omega, by rw [sval_spos hlm]; omega, by rw [sval_spos hlm]⟩
  have hlt' := thInvy_lt hr (j := lv σ - 1) (by omega) (by omega : lv σ ≤ k) (by omega)
  rw [thInv_eq (j := lv σ - 1), h48, sig_eq hpm, sval_spos hlm] at hlt'
  simp only at hlt'
  rw [Nat.cast_sub (by omega)] at hlt'
  push_cast at hlt'
  exact hlt'

/-- Second half of Claim 4.50 (tex l.1705), from a point of `Θ` on `P_V`. A step of the proof by
contradiction of Lemma 4.40 (tex l.1519): its hypotheses can never all hold, since `lemma_4_40`
shows `Σ` is the only copy and `Σ` has no point on `P_V` (`hV` fails even with `hne` set aside), so
it holds only vacuously. Used only inside `TI.meets_both` and `TI.no_copy`. -/
theorem c450x (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hne : Finset.univ.image Θ ≠ canon σ) (hV : ∃ i, 1 ≤ i ∧ i ≤ k ∧ th Θ i ∈ PV439 σ) :
    (up σ : ℝ) < (th Θ (up σ)).1 ∧ (th Θ (up σ)).1 < (up σ : ℝ) + 1 := by
  have hr := hΘ.1
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3; have hr' := N.r
  obtain ⟨i, hi1, hi2, hP⟩ := hV
  have hlt : i < up σ := by
    by_contra hc
    exact (c446 hσ hΘ).2 i (by omega) hi2 hP
  have hBm : 1 ≤ bp σ ∧ bp σ ≤ k := ⟨by omega, by omega⟩
  have hxb := thx_le hr (s := i) (i := bp σ) hi1 (by omega) hBm.2
  have hxi := (PV_bd hσ hP).1
  have hn := c449b hσ hΘ hne
  -- `Θ(b)_x ≥ u`, since only `P_V` meets the strip `u - 1 < x < u`
  have hge : (up σ : ℝ) ≤ (th Θ (bp σ)).1 := by
    by_contra hc
    push Not at hc
    rw [hu] at hc
    rcases clsTh hσ hΘ hBm with ⟨i', -, -, -, hx, -⟩ | ⟨-, hx, -⟩ | ⟨h1, -⟩ | ⟨-, -, hx, -⟩ |
        ⟨-, -, -, hx⟩ | ⟨-, hx, -⟩ | ⟨hP', -⟩
    · rw [hx] at hc hxb
      exact nat_btw (a := bp σ) (n := i') (by linarith) hc
    · linarith
    · omega
    · linarith
    · linarith
    · linarith
    · exact hn hP'
  have hxu := thx_lt hr (i := bp σ) hBm.1 (by omega : up σ ≤ k) (by omega)
  refine ⟨by linarith, ?_⟩
  obtain ⟨hv1, hv2⟩ := hσ.val
  have h2 := (sval_mem (σ := σ) (i := 2) ⟨by omega, by omega⟩).1
  have hUm : 1 ≤ up σ + 1 ∧ up σ + 1 ≤ k := ⟨by omega, by omega⟩
  have h48 := c448 hσ hΘ hne (i := up σ + 1) ⟨le_rfl, by omega, by omega, by omega⟩
  have hx := thx_lt hr (i := up σ) (by omega) hUm.2 (Nat.lt_succ_self _)
  rw [h48, sig_eq hUm] at hx
  simp only at hx
  push_cast at hx
  exact hx

/-- Final step of the proof of Lemma 4.40 (tex l.1728–1731): if `Θ⁻¹(ℓ)` lies in the strip
`ℓ - 1 < y < ℓ`, then `Θ(1) ∈ P_V`. A step of the proof by contradiction: its hypotheses can never
all hold, since `lemma_4_40` shows the only copy is `Σ`, whose point `Σ⁻¹(ℓ)` has `y = ℓ`; so it
holds only vacuously. Used only inside `TI.meets_both` and `TI.no_copy`. -/
theorem strip_y (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hy : (lv σ : ℝ) - 1 < (thInv σ Θ (lv σ)).2 ∧ (thInv σ Θ (lv σ)).2 < (lv σ : ℝ)) :
    th Θ 1 ∈ PV439 σ := by
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5
  rw [thInv_eq, N.pl] at hy
  obtain ⟨hy1, hy2⟩ := hy
  rcases clsTh hσ hΘ (i := 1) ⟨le_rfl, by omega⟩ with ⟨i', -, -, -, -, hy'⟩ | ⟨-, -, hy', -⟩ |
      ⟨h1, -⟩ | ⟨-, hy', -⟩ | ⟨-, hy', -⟩ | ⟨-, -, -, hy', -⟩ | ⟨hP, -⟩
  · rw [hy'] at hy1 hy2
    exfalso
    have a1 : sval σ i' < lv σ := by exact_mod_cast hy2
    have a2 : lv σ < sval σ i' + 1 := by
      have : (lv σ : ℝ) < sval σ i' + 1 := by linarith
      exact_mod_cast this
    omega
  · linarith
  · omega
  · linarith
  · linarith
  · linarith
  · exact hP

/-- Final step of the proof of Lemma 4.40 (tex l.1733–1735): if `Θ(u)` lies in the strip
`u < x < u + 1`, then `Θ(u) ∈ P_H`. A step of the proof by contradiction: its hypotheses can never
all hold, since `lemma_4_40` shows the only copy is `Σ`, whose point `Σ(u)` has `x = u`; so it holds
only vacuously. Used only inside `TI.meets_both` and `TI.no_copy`. -/
theorem strip_x (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hx : (up σ : ℝ) < (th Θ (up σ)).1 ∧ (th Θ (up σ)).1 < (up σ : ℝ) + 1) :
    th Θ (up σ) ∈ PH439 σ := by
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  obtain ⟨hx1, hx2⟩ := hx
  rcases clsTh hσ hΘ (i := up σ) ⟨by omega, by omega⟩ with ⟨i', -, -, -, hx', -⟩ |
      ⟨-, hx', -⟩ | ⟨-, hx', -⟩ | ⟨hs, -⟩ | ⟨-, -, -, hx'⟩ | ⟨hP, -⟩ | ⟨-, -, hx', -⟩
  · rw [hx'] at hx1 hx2
    exact absurd hx2 (by
      have : up σ < i' := by exact_mod_cast hx1
      have : (up σ : ℝ) + 1 ≤ i' := by exact_mod_cast this
      linarith)
  · linarith
  · linarith
  · rw [N.su] at hs; omega
  · linarith
  · exact hP
  · linarith

/-- (4.25): an additional copy meets both `P_H` and `P_V`. -/
theorem meets_both (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hne : Finset.univ.image Θ ≠ canon σ) :
    (∃ i, 1 ≤ i ∧ i ≤ k ∧ th Θ i ∈ PH439 σ) ∧ (∃ i, 1 ≤ i ∧ i ≤ k ∧ th Θ i ∈ PV439 σ) := by
  have N := nums hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk
  rcases meets hσ hΘ hne with hH | hV
  · exact ⟨hH, ⟨1, le_rfl, by omega, strip_y hσ hΘ (c450y hσ hΘ hne hH)⟩⟩
  · exact ⟨⟨up σ, by omega, by omega, strip_x hσ hΘ (c450x hσ hΘ hne hV)⟩, hV⟩

/-- The final step of the proof of Lemma 4.40: no additional copy exists. -/
theorem no_copy (hσ : Hyp440 σ) (hΘ : CopyIn σ Θ (D439 σ))
    (hne : Finset.univ.image Θ ≠ canon σ) : False := by
  have N := nums hσ
  obtain ⟨hk5, hl3, hlk, hb2, hu, huk⟩ := numsR hσ
  have hk' := N.k5; have hu' := N.u; have huk' := N.uk; have hb' := N.b2
  have hlk' := N.lk; have hl3' := N.l3
  obtain ⟨hH, hV⟩ := meets_both hσ hΘ hne
  have hy := c450y hσ hΘ hne hH
  have hx := c450x hσ hΘ hne hV
  have hPV := PV_bd hσ (strip_y hσ hΘ hy)
  have hPH := PH_bd (strip_x hσ hΘ hx)
  rw [thInv_eq, N.pl] at hy
  -- `ℓ = 3` and `u = k - 2`
  have hl : lv σ = 3 := by
    have : (lv σ : ℝ) < 4 := by linarith [hPV.2.2.2.1]
    have : lv σ < 4 := by exact_mod_cast this
    omega
  have hu2 : k < up σ + 3 := by
    have : (k : ℝ) < up σ + 3 := by linarith [hPH.1]
    exact_mod_cast this
  -- `σ(2) = 1`, so `b = 2`, `u = 3`, `k = 5`
  obtain ⟨hv1, hv2⟩ := hσ.val
  have h2m : 1 ≤ 2 ∧ 2 ≤ k := ⟨by omega, by omega⟩
  have h2 := (sval_mem (σ := σ) h2m).1
  have hs2 : sval σ 2 = 1 := by omega
  have hb : bp σ = 2 := by rw [← bp_def, ← hs2, spos_sval h2m]
  have hk5' : k = 5 := by omega
  have hsu1 : sval σ (up σ + 1) = 2 := by omega
  have hnot := hσ.standing.not42
  subst hk5'
  have e1 : sval σ 1 = 3 := by rw [lv_def, hl]
  have e3 : sval σ 3 = 5 := by
    have := N.su; rw [show up σ = 3 by omega] at this; exact this
  have e4 : sval σ 4 = 2 := by rw [show up σ + 1 = 4 by omega] at hsu1; exact hsu1
  have e5 : sval σ 5 = 4 := by
    have := N.sk; rw [hl] at this; exact this
  apply hnot
  have : oneLine σ = [sval σ 1, sval σ 2, sval σ 3, sval σ 4, sval σ 5] := by
    simp only [oneLine, List.ofFn_succ, List.ofFn_zero]
    simp [← sval_succ]
  rw [IsExcFive, this, e1, hs2, e3, e4, e5]
  simp

end TI


/-- **Lemma 4.40.** Under its hypotheses (`Hyp440`), if `Π` is associated with a permutation and
`Σ ⊆ Π ⊆ Σ ∪ P_L ∪ P_R ∪ P_B ∪ P_U ∪ P_H ∪ P_V` (Construction 4.39), then `Σ` is the unique
`σ`-copy in `Π`. The proof does not use `hP : IsPermPointSet P`; the paper states it (tex l.1509),
and it is kept to match the paper. -/
theorem lemma_4_40 (σ : Perm (Fin k)) (hσ : Hyp440 σ)
    (P : Finset (ℝ × ℝ)) (hP : IsPermPointSet P)
    (h₁ : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P) (h₂ : (↑P : Set (ℝ × ℝ)) ⊆ D439 σ) :
    IsUniqueCopy σ ↑P := by
  refine ⟨h₁, fun Θ hΘ => ?_⟩
  by_contra hne
  exact TI.no_copy hσ ⟨hΘ.1, fun i => h₂ (hΘ.2 i)⟩ hne

/-- The context of the proof of Lemma 4.40 (tex l.1519): its hypotheses and a `σ`-copy `Θ` in
the support of Construction 4.39 with `Θ ≠ Σ`. -/
structure Ctx440 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) : Prop where
  hyp : Hyp440 σ
  copy : CopyIn σ Θ (D439 σ)
  ne : Finset.univ.image Θ ≠ canon σ

/-- **Claim 4.41** (propagation away from `P_H ∪ P_V`), statements 1–4:
1. if `j < k`, `Θ⁻¹(j) ∉ P_H ∪ P_V` and `Θ⁻¹(j)_y > j`, then `Θ⁻¹(j+1)_y > j+1`;
2. if `j > 1`, `Θ⁻¹(j) ∉ P_H ∪ P_V` and `Θ⁻¹(j)_y < j`, then `Θ⁻¹(j-1)_y < j-1`;
3. if `i < k`, `Θ(i) ∉ P_H ∪ P_V` and `Θ(i)_x > i`, then `Θ(i+1)_x > i+1`;
4. if `i > 1`, `Θ(i) ∉ P_H ∪ P_V` and `Θ(i)_x < i`, then `Θ(i-1)_x < i-1`.

A step of the proof by contradiction of Lemma 4.40 (tex l.1519): its context `Ctx440` cannot be
satisfied, because `lemma_4_40` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `Hyp440.ud`/`ld` ((UD), (LD), tex l.1509)
or `Standing44.not41`/`not42` (tex l.1018); these paper hypotheses are kept to match the paper. -/
theorem claim_4_41 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx440 σ Θ) :
    (∀ j : ℕ, 1 ≤ j → j < k → thInv σ Θ j ∉ PH439 σ ∪ PV439 σ → (j : ℝ) < (thInv σ Θ j).2 →
      ((j : ℝ) + 1) < (thInv σ Θ (j + 1)).2) ∧
    (∀ j : ℕ, 1 < j → j ≤ k → thInv σ Θ j ∉ PH439 σ ∪ PV439 σ → (thInv σ Θ j).2 < (j : ℝ) →
      (thInv σ Θ (j - 1)).2 < (j : ℝ) - 1) ∧
    (∀ i : ℕ, 1 ≤ i → i < k → th Θ i ∉ PH439 σ ∪ PV439 σ → (i : ℝ) < (th Θ i).1 →
      ((i : ℝ) + 1) < (th Θ (i + 1)).1) ∧
    (∀ i : ℕ, 1 < i → i ≤ k → th Θ i ∉ PH439 σ ∪ PV439 σ → (th Θ i).1 < (i : ℝ) →
      (th Θ (i - 1)).1 < (i : ℝ) - 1) := by
  exact TI.c441 hc.hyp hc.copy

/-- **Corollary 4.42**, statements 1–2:
1. if `Θ⁻¹(j)_y > j` and `Θ⁻¹(j)_y ≥ ℓ + 1`, then `Θ⁻¹(s)_y > s` for `j ≤ s ≤ k`;
2. if `Θ(i)_x < i` and `Θ(i)_x ≤ u - 1`, then `Θ(s)_x < s` for `1 ≤ s ≤ i`.

A step of the proof by contradiction of Lemma 4.40 (tex l.1519): its context `Ctx440` cannot be
satisfied, because `lemma_4_40` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `Hyp440.ud`/`ld` ((UD), (LD), tex l.1509)
or `Standing44.not41`/`not42` (tex l.1018); these paper hypotheses are kept to match the paper. -/
theorem cor_4_42 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx440 σ Θ) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k → (j : ℝ) < (thInv σ Θ j).2 → (lv σ : ℝ) + 1 ≤ (thInv σ Θ j).2 →
      ∀ s : ℕ, j ≤ s → s ≤ k → (s : ℝ) < (thInv σ Θ s).2) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ k → (th Θ i).1 < (i : ℝ) → (th Θ i).1 ≤ (up σ : ℝ) - 1 →
      ∀ s : ℕ, 1 ≤ s → s ≤ i → (th Θ s).1 < (s : ℝ)) := by
  exact TI.c442 hc.hyp hc.copy

/-- **Claim 4.43.** `Θ⁻¹(ℓ) ∉ P_H` and `Θ(u) ∉ P_V`.

A step of the proof by contradiction of Lemma 4.40 (tex l.1519): its context `Ctx440` cannot be
satisfied, because `lemma_4_40` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `Hyp440.ud`/`ld` ((UD), (LD), tex l.1509)
or `Standing44.not41`/`not42` (tex l.1018); these paper hypotheses are kept to match the paper. -/
theorem claim_4_43 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx440 σ Θ) :
    thInv σ Θ (lv σ) ∉ PH439 σ ∧ th Θ (up σ) ∉ PV439 σ := by
  exact ⟨TI.c443a hc.hyp hc.copy, TI.c443b hc.hyp hc.copy⟩

/-- **Claim 4.44.**
1. If `Θ⁻¹(s) ∈ P_H` for some `s < ℓ`, then `Θ⁻¹(ℓ)_y ≥ ℓ + 1`, `Θ⁻¹(k) ∈ P_U`, and
   `Θ⁻¹(j) = Σ⁻¹(j+1)` for `r ≤ j ≤ k - 1` (4.27);
2. if `Θ(s) ∈ P_V` for some `s > u`, then `Θ(u)_x ≤ u - 1`, `Θ(1) ∈ P_L`, and
   `Θ(i) = Σ(i-1)` for `2 ≤ i ≤ b` (4.28).

A step of the proof by contradiction of Lemma 4.40 (tex l.1519): its context `Ctx440` cannot be
satisfied, because `lemma_4_40` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `Hyp440.ud`/`ld` ((UD), (LD), tex l.1509)
or `Standing44.not41`/`not42` (tex l.1018); these paper hypotheses are kept to match the paper. -/
theorem claim_4_44 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx440 σ Θ) :
    ((∃ s : ℕ, 1 ≤ s ∧ s < lv σ ∧ thInv σ Θ s ∈ PH439 σ) →
      (lv σ : ℝ) + 1 ≤ (thInv σ Θ (lv σ)).2 ∧ thInv σ Θ k ∈ PU419 σ ∧
      ∀ j : ℕ, rv σ ≤ j → j ≤ k - 1 → thInv σ Θ j = sigInv σ (j + 1)) ∧
    ((∃ s : ℕ, up σ < s ∧ s ≤ k ∧ th Θ s ∈ PV439 σ) →
      (th Θ (up σ)).1 ≤ (up σ : ℝ) - 1 ∧ th Θ 1 ∈ PL419 σ ∧
      ∀ i : ℕ, 2 ≤ i → i ≤ bp σ → th Θ i = sig σ (i - 1)) := by
  exact ⟨TI.c444a hc.hyp hc.copy, TI.c444b hc.hyp hc.copy⟩

/-- **Claim 4.45.**
1. If `Θ⁻¹(s) ∈ P_H` for some `s < ℓ`, then `Θ⁻¹(t) ∈ P_H` for `s ≤ t < ℓ`;
2. if `Θ(s) ∈ P_V` for some `s > u`, then `Θ(t) ∈ P_V` for `u < t ≤ s`.

A step of the proof by contradiction of Lemma 4.40 (tex l.1519): its context `Ctx440` cannot be
satisfied, because `lemma_4_40` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `Hyp440.ud`/`ld` ((UD), (LD), tex l.1509)
or `Standing44.not41`/`not42` (tex l.1018); these paper hypotheses are kept to match the paper. -/
theorem claim_4_45 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx440 σ Θ) :
    (∀ s : ℕ, 1 ≤ s → s < lv σ → thInv σ Θ s ∈ PH439 σ →
      ∀ t : ℕ, s ≤ t → t < lv σ → thInv σ Θ t ∈ PH439 σ) ∧
    (∀ s : ℕ, up σ < s → s ≤ k → th Θ s ∈ PV439 σ →
      ∀ t : ℕ, up σ < t → t ≤ s → th Θ t ∈ PV439 σ) := by
  exact ⟨TI.c445a hc.hyp hc.copy, TI.c445b hc.hyp hc.copy⟩

/-- **Claim 4.46.** `Θ⁻¹(s) ∉ P_H` for `1 ≤ s ≤ ℓ`, and `Θ(s) ∉ P_V` for `u ≤ s ≤ k`.

A step of the proof by contradiction of Lemma 4.40 (tex l.1519): its context `Ctx440` cannot be
satisfied, because `lemma_4_40` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof does not use `ne` (`Θ ≠ Σ`), `Hyp440.ud`/`ld` ((UD), (LD), tex l.1509)
or `Standing44.not41`/`not42` (tex l.1018); these paper hypotheses are kept to match the paper. -/
theorem claim_4_46 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx440 σ Θ) :
    (∀ s : ℕ, 1 ≤ s → s ≤ lv σ → thInv σ Θ s ∉ PH439 σ) ∧
    (∀ s : ℕ, up σ ≤ s → s ≤ k → th Θ s ∉ PV439 σ) := by
  exact TI.c446 hc.hyp hc.copy

/-- `Σ_BR = Σ ∩ ([u+1, k-1] × [2, ℓ-1])` (tex l.1649). -/
def SigBR (σ : Perm (Fin k)) : Set (ℝ × ℝ) :=
  {p | p ∈ canon σ ∧ (up σ : ℝ) + 1 ≤ p.1 ∧ p.1 ≤ (k : ℝ) - 1 ∧
    2 ≤ p.2 ∧ p.2 ≤ (lv σ : ℝ) - 1}

namespace TI

theorem BR_mem {σ : Perm (Fin k)} {i : ℕ} (hi : BR σ i) : 1 ≤ i ∧ i ≤ k := by
  have := hi.1; have := hi.2.1; omega

theorem mem_SigBR_iff {σ : Perm (Fin k)} {i : ℕ} (hi : 1 ≤ i ∧ i ≤ k) :
    sig σ i ∈ SigBR σ ↔ BR σ i := by
  rw [SigBR, Set.mem_ofPred_eq, sig_eq hi]
  simp only
  constructor
  · rintro ⟨-, h1, h2, h3, h4⟩
    refine ⟨by exact_mod_cast h1, ?_, by exact_mod_cast h3, ?_⟩
    · have : (i : ℝ) + 1 ≤ k := by linarith
      have : i + 1 ≤ k := by exact_mod_cast this
      omega
    · have : (sval σ i : ℝ) + 1 ≤ lv σ := by linarith
      have : sval σ i + 1 ≤ lv σ := by exact_mod_cast this
      omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨mem_canon.mpr ⟨i, hi.1, hi.2, rfl⟩, by exact_mod_cast h1, ?_, by exact_mod_cast h3, ?_⟩
    · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : i + 1 ≤ k)
      linarith
    · have : (sval σ i : ℝ) + 1 ≤ lv σ := by exact_mod_cast (by omega : sval σ i + 1 ≤ lv σ)
      linarith

end TI

/-- **Claim 4.47.** `Θ_BR ⊆ Σ_BR`, where `Θ_BR = {Θ(i) : Σ(i) ∈ Σ_BR}`.

A step of the proof by contradiction of Lemma 4.40 (tex l.1519): its context `Ctx440` cannot be
satisfied, because `lemma_4_40` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof uses `ne`, but not `Hyp440.ud`/`ld` ((UD), (LD), tex l.1509) or
`Standing44.not42` (tex l.1018); these paper hypotheses are kept to match the paper. -/
theorem claim_4_47 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx440 σ Θ) :
    ∀ i : ℕ, 1 ≤ i → i ≤ k → sig σ i ∈ SigBR σ → th Θ i ∈ SigBR σ := by
  intro i hi1 hik hS
  have hB := (TI.mem_SigBR_iff ⟨hi1, hik⟩).1 hS
  obtain ⟨i', hB', he⟩ := TI.c447 hc.hyp hc.copy hc.ne hB
  rw [he]
  exact (TI.mem_SigBR_iff (TI.BR_mem hB')).2 hB'

/-- **Corollary 4.48.** If `u + 1 ≤ i ≤ k - 1` and `2 ≤ σ(i) ≤ ℓ - 1`, then `Θ(i) = Σ(i)`.

A step of the proof by contradiction of Lemma 4.40 (tex l.1519): its context `Ctx440` cannot be
satisfied, because `lemma_4_40` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof uses `ne`, but not `Hyp440.ud`/`ld` ((UD), (LD), tex l.1509) or
`Standing44.not42` (tex l.1018); these paper hypotheses are kept to match the paper. -/
theorem cor_4_48 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx440 σ Θ) :
    ∀ i : ℕ, up σ + 1 ≤ i → i ≤ k - 1 → 2 ≤ sval σ i → sval σ i ≤ lv σ - 1 →
      th Θ i = sig σ i := by
  intro i h1 h2 h3 h4
  exact TI.c448 hc.hyp hc.copy hc.ne ⟨h1, h2, h3, h4⟩

/-- **Claim 4.49.** `Θ⁻¹(r) ∉ P_H` and `Θ(b) ∉ P_V`.

A step of the proof by contradiction of Lemma 4.40 (tex l.1519): its context `Ctx440` cannot be
satisfied, because `lemma_4_40` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof uses `ne`, `Hyp440.ud`/`ld` and `Standing44.not41`, but not
`Standing44.not42` (tex l.1018); that paper hypothesis is kept to match the paper. -/
theorem claim_4_49 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx440 σ Θ) :
    thInv σ Θ (rv σ) ∉ PH439 σ ∧ th Θ (bp σ) ∉ PV439 σ := by
  exact ⟨TI.c449a hc.hyp hc.copy hc.ne, TI.c449b hc.hyp hc.copy hc.ne⟩

/-- **Claim 4.50.** `ℓ - 1 < Θ⁻¹(ℓ)_y < ℓ` and `u < Θ(u)_x < u + 1`.

A step of the proof by contradiction of Lemma 4.40 (tex l.1519): its context `Ctx440` cannot be
satisfied, because `lemma_4_40` proves `Σ` is the only copy, so the claim holds only vacuously, as
in the paper. Its proof uses `ne`, `Hyp440.ud`/`ld` and `Standing44.not41`, but not
`Standing44.not42` (tex l.1018); that paper hypothesis is kept to match the paper. -/
theorem claim_4_50 (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (hc : Ctx440 σ Θ) :
    ((lv σ : ℝ) - 1 < (thInv σ Θ (lv σ)).2 ∧ (thInv σ Θ (lv σ)).2 < (lv σ : ℝ)) ∧
    ((up σ : ℝ) < (th Θ (up σ)).1 ∧ (th Θ (up σ)).1 < (up σ : ℝ) + 1) := by
  obtain ⟨hH, hV⟩ := TI.meets_both hc.hyp hc.copy hc.ne
  exact ⟨TI.c450y hc.hyp hc.copy hc.ne hH, TI.c450x hc.hyp hc.copy hc.ne hV⟩

end LinfPermRemoval
