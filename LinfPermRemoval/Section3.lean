/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.Basic

/-!
# Section 3: the `O(n)` cases

Patterns: `(12)` is `1 : Perm (Fin 2)` and `(132)` is `p132`. The six patterns of Theorem 1.1 are
listed in one-line notation in `linearPatterns`.

Positions are 0-based in Lean (see `LinfPermRemoval.Basic`); in particular "adjacent positions
`i, i+1`" of the paper are Lean indices `i, j` with `j = i + 1`.
-/

open Equiv Finset

namespace LinfPermRemoval

variable {n k : ℕ}

/-- The six patterns `(12), (21), (132), (231), (312), (213)` of Theorem 1.1 and Lemma 3.1, in
one-line notation. -/
def linearPatterns : List (List ℕ) := [[1, 2], [2, 1], [1, 3, 2], [2, 3, 1], [3, 1, 2], [2, 1, 3]]

namespace Sec3

theorem isCopy_image_of_strictMono (σ : Perm (Fin k)) (π : Perm (Fin n)) (f : Fin k → Fin n)
    (hf : StrictMono f) (hv : ∀ a b, π (f a) < π (f b) ↔ σ a < σ b) :
    IsCopy σ π (univ.image f) := by
  have hc : (univ.image f).card = k := by
    rw [card_image_of_injective _ hf.injective]; simp
  refine ⟨hc, ?_⟩
  have : ⇑((univ.image f).orderEmbOfFin hc) = f :=
    (Finset.orderEmbOfFin_unique hc (fun x => mem_image_of_mem f (mem_univ x)) hf).symm
  simpa [this] using hv

theorem isCopy_orderEmb {σ : Perm (Fin k)} {π : Perm (Fin n)} {S : Finset (Fin n)}
    (h : IsCopy σ π S) : ∃ f : Fin k → Fin n, StrictMono f ∧ S = univ.image f ∧
      ∀ a b, π (f a) < π (f b) ↔ σ a < σ b := by
  obtain ⟨hc, hv⟩ := h
  refine ⟨S.orderEmbOfFin hc, (S.orderEmbOfFin hc).strictMono, ?_, hv⟩
  ext x
  simp only [mem_image, mem_univ, true_and]
  rw [← Set.mem_range, Finset.range_orderEmbOfFin]
  simp

theorem isCopy12_iff (π : Perm (Fin n)) (S : Finset (Fin n)) :
    IsCopy (1 : Perm (Fin 2)) π S ↔ ∃ a b, a < b ∧ S = {a, b} ∧ π a < π b := by
  constructor
  · intro h
    obtain ⟨f, hf, rfl, hv⟩ := isCopy_orderEmb h
    refine ⟨f 0, f 1, hf (by decide), ?_, (hv 0 1).2 (by decide)⟩
    ext x; simp [Fin.exists_fin_two, eq_comm]
  · rintro ⟨a, b, hab, rfl, hv⟩
    have him : ({a, b} : Finset (Fin n)) = univ.image ![a, b] := by
      ext x; simp [Fin.exists_fin_two, eq_comm]
    rw [him]
    apply isCopy_image_of_strictMono
    · rw [Fin.strictMono_iff_lt_succ]; intro i; fin_cases i; simpa using hab
    · intro x y
      fin_cases x <;> fin_cases y <;> simp [hv, lt_asymm hv]

theorem isCopy132_iff (π : Perm (Fin n)) (S : Finset (Fin n)) :
    IsCopy p132 π S ↔ ∃ a b c, a < b ∧ b < c ∧ S = {a, b, c} ∧ π a < π c ∧ π c < π b := by
  constructor
  · intro h
    obtain ⟨f, hf, rfl, hv⟩ := isCopy_orderEmb h
    refine ⟨f 0, f 1, f 2, hf (by decide), hf (by decide), ?_, (hv 0 2).2 (by decide),
      (hv 2 1).2 (by decide)⟩
    ext x; simp [Fin.exists_fin_succ, eq_comm]
  · rintro ⟨a, b, c, hab, hbc, rfl, h1, h2⟩
    have him : ({a, b, c} : Finset (Fin n)) = univ.image ![a, b, c] := by
      ext x; simp [Fin.exists_fin_succ, eq_comm]
    rw [him]
    apply isCopy_image_of_strictMono
    · rw [Fin.strictMono_iff_lt_succ]; intro i; fin_cases i
      · simpa using hab
      · simpa using hbc
    · intro x y
      fin_cases x <;> fin_cases y <;>
        simp [p132, Equiv.swap_apply_of_ne_of_ne, h1, h2, h1.trans h2, lt_asymm h1,
          lt_asymm h2, lt_asymm (h1.trans h2)]

theorem exists_matching (π π' : Perm (Fin n)) :
    ∃ θ : Perm (Fin n), univ.inf' univ_nonempty (maxDisp π π') = maxDisp π π' θ := by
  obtain ⟨θ, -, h⟩ := Finset.exists_mem_eq_inf' univ_nonempty (maxDisp π π')
  exact ⟨θ, h⟩

theorem disp_le (π π' θ : Perm (Fin n)) (i : Fin n) :
    max ((i : ℤ) - (θ i : ℤ)).natAbs ((π i : ℤ) - (π' (θ i) : ℤ)).natAbs ≤ maxDisp π π' θ :=
  Finset.le_sup (f := fun i : Fin n =>
    max ((i : ℤ) - (θ i : ℤ)).natAbs ((π i : ℤ) - (π' (θ i) : ℤ)).natAbs) (mem_univ i)

/-- Bound on `ρ_∞(π, π * s)` through the matching `s⁻¹`. -/
theorem rhoInf_mul_le (hn : 2 ≤ n) (π s : Perm (Fin n)) (d : ℕ)
    (hd : ∀ i : Fin n, ((i : ℤ) - (s⁻¹ i : ℤ)).natAbs ≤ d) :
    ((n : ℝ) - 1) * rhoInf π (π * s) ≤ d := by
  have hm : maxDisp π (π * s) s⁻¹ ≤ d := by
    unfold maxDisp
    refine Finset.sup_le fun i _ => ?_
    simpa using hd i
  have hle : univ.inf' univ_nonempty (maxDisp π (π * s)) ≤ d :=
    (Finset.inf'_le _ (mem_univ _)).trans hm
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold rhoInf
  rw [mul_div_cancel₀ _ hpos.ne']
  exact_mod_cast hle

open Classical in
/-- The counting injection. -/
theorem numCopies_add_le (σ : Perm (Fin k)) (π π' : Perm (Fin n))
    (g : Finset (Fin n) → Finset (Fin n)) (hg : Function.Injective g)
    (hcopy : ∀ S', IsCopy σ π' S' → IsCopy σ π (g S'))
    (D : Finset (Finset (Fin n))) (hD : ∀ T ∈ D, IsCopy σ π T)
    (hDg : ∀ S', IsCopy σ π' S' → g S' ∉ D) :
    numCopies σ π' + D.card ≤ numCopies σ π := by
  unfold numCopies
  rw [← card_image_of_injective _ hg, ← card_union_of_disjoint]
  · apply card_le_card
    intro T hT
    rcases mem_union.1 hT with h | h
    · obtain ⟨S', hS', rfl⟩ := mem_image.1 h
      simp only [mem_filter, mem_univ, true_and] at hS' ⊢
      exact hcopy S' hS'
    · simpa using hD T h
  · rw [disjoint_left]
    intro T h hT
    obtain ⟨S', hS', rfl⟩ := mem_image.1 h
    simp only [mem_filter, mem_univ, true_and] at hS'
    exact hDg S' hS' hT

theorem exists_copy_of_pos {σ : Perm (Fin k)} {π : Perm (Fin n)} (h : 0 < numCopies σ π) :
    ∃ S, IsCopy σ π S := by
  classical
  unfold numCopies at h
  obtain ⟨S, hS⟩ := card_pos.1 (by convert h)
  exact ⟨S, by simpa using hS⟩

theorem le_of_isCopy {σ : Perm (Fin k)} {π : Perm (Fin n)} {S : Finset (Fin n)}
    (h : IsCopy σ π S) : k ≤ n := by
  obtain ⟨hc, -⟩ := h
  simpa [hc] using card_le_univ S

/-! ### Claim 3.2 -/

theorem exists_adj12 (π : Perm (Fin n)) : ∀ (d : ℕ) (i j : Fin n), (j : ℕ) = i + d →
    π i < π j → ∃ a b : Fin n, (b : ℕ) = a + 1 ∧ π a < π b := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro i j hd hv
  have hd0 : d ≠ 0 := by rintro rfl; simp [Fin.ext_iff.2 hd] at hv
  by_cases h1 : d = 1
  · exact ⟨i, j, by omega, hv⟩
  · have hm : (i : ℕ) + 1 < n := by omega
    have hne : i ≠ ⟨i + 1, hm⟩ := by simp [Fin.ext_iff]
    rcases lt_or_gt_of_ne (π.injective.ne hne) with h | h
    · exact ⟨i, _, rfl, h⟩
    · exact ih (d - 1) (by omega) ⟨i + 1, hm⟩ j (by simp; omega) (h.trans hv)

theorem claim_3_2_aux (π : Perm (Fin n)) (h : 0 < numCopies (1 : Perm (Fin 2)) π) :
    ∃ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 ∧ IsCopy (1 : Perm (Fin 2)) π {i, j} := by
  obtain ⟨S, hS⟩ := exists_copy_of_pos h
  obtain ⟨a, b, hab, -, hv⟩ := (isCopy12_iff π S).1 hS
  obtain ⟨i, j, hij, hv'⟩ := exists_adj12 π (b - a) a b (by rw [Fin.lt_def] at hab; omega) hv
  exact ⟨i, j, hij, (isCopy12_iff π _).2 ⟨i, j, by rw [Fin.lt_def]; omega, rfl, hv'⟩⟩

/-! ### Claim 3.4 -/

theorem swap_lt_swap {i j a b : Fin n} (hij : (j : ℕ) = (i : ℕ) + 1) (hab : a < b)
    (hne : ¬ (a = i ∧ b = j)) : Equiv.swap i j a < Equiv.swap i j b := by
  rw [Fin.lt_def] at hab ⊢
  rw [swap_apply_def, swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem claim_3_4_aux (π : Perm (Fin n)) (i j : Fin n) (hij : (j : ℕ) = (i : ℕ) + 1)
    (hπ : π i < π j) (S' : Finset (Fin n))
    (hS' : IsCopy (1 : Perm (Fin 2)) (π * Equiv.swap i j) S') :
    IsCopy (1 : Perm (Fin 2)) π (S'.image (Equiv.swap i j)) := by
  obtain ⟨a, b, hab, rfl, hv⟩ := (isCopy12_iff _ S').1 hS'
  rw [isCopy12_iff]
  refine ⟨Equiv.swap i j a, Equiv.swap i j b, swap_lt_swap hij hab ?_, by simp, hv⟩
  rintro ⟨rfl, rfl⟩
  simp [swap_apply_left, swap_apply_right] at hv
  exact lt_asymm hv hπ

/-! ### Claim 3.5 -/

theorem exists_adj132 (π : Perm (Fin n)) : ∀ (d : ℕ) (a b c : Fin n), (b : ℕ) = a + d →
    b < c → π a < π c → π c < π b →
    ∃ a' b' c' : Fin n, (b' : ℕ) = a' + 1 ∧ b' < c' ∧ π a' < π c' ∧ π c' < π b' := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro a b c hd hbc h1 h2
  have hd0 : d ≠ 0 := by
    rintro rfl; obtain rfl : b = a := Fin.ext (by omega); exact lt_asymm h1 h2
  by_cases hd1 : d = 1
  · exact ⟨a, b, c, by omega, hbc, h1, h2⟩
  · have hm : (a : ℕ) + 1 < n := by omega
    have hne : (⟨a + 1, hm⟩ : Fin n) ≠ c := by
      rw [Fin.lt_def] at hbc; simp [Fin.ext_iff]; omega
    rcases lt_or_gt_of_ne (π.injective.ne hne) with h | h
    · exact ih (d - 1) (by omega) ⟨a + 1, hm⟩ b c (by simp; omega) hbc h h2
    · refine ⟨a, ⟨a + 1, hm⟩, c, rfl, ?_, h1, h⟩
      rw [Fin.lt_def] at hbc ⊢; simp; omega

theorem claim_3_5_aux (π : Perm (Fin n)) (h : 0 < numCopies p132 π) :
    ∃ a b c : Fin n, (b : ℕ) = (a : ℕ) + 1 ∧ b < c ∧ IsCopy p132 π {a, b, c} := by
  obtain ⟨S, hS⟩ := exists_copy_of_pos h
  obtain ⟨a, b, c, hab, hbc, -, h1, h2⟩ := (isCopy132_iff π S).1 hS
  obtain ⟨a', b', c', hd, hbc', h1', h2'⟩ :=
    exists_adj132 π (b - a) a b c (by rw [Fin.lt_def] at hab; omega) hbc h1 h2
  exact ⟨a', b', c', hd, hbc', (isCopy132_iff π _).2
    ⟨a', b', c', by rw [Fin.lt_def]; omega, hbc', rfl, h1', h2'⟩⟩

/-! ### Dihedral symmetries (tex l.281–285): reversal `π ↦ π * rev`, complement `π ↦ rev * π` -/

theorem revPerm_mul_revPerm : (Fin.revPerm : Perm (Fin n)) * Fin.revPerm = 1 := by
  ext i; simp

theorem isCopy_compl_iff (σ : Perm (Fin k)) (π : Perm (Fin n)) (S : Finset (Fin n)) :
    IsCopy (Fin.revPerm * σ) (Fin.revPerm * π) S ↔ IsCopy σ π S := by
  unfold IsCopy
  simp only [Perm.mul_apply, Fin.revPerm_apply, Fin.rev_lt_rev]
  exact exists_congr fun _ => ⟨fun H a b => H b a, fun H a b => H b a⟩

theorem numCopies_compl (σ : Perm (Fin k)) (π : Perm (Fin n)) :
    numCopies (Fin.revPerm * σ) (Fin.revPerm * π) = numCopies σ π := by
  unfold numCopies
  congr 1
  ext S
  simp [isCopy_compl_iff]

theorem isCopy_rev {σ : Perm (Fin k)} {π : Perm (Fin n)} {S : Finset (Fin n)}
    (h : IsCopy σ π S) : IsCopy (σ * Fin.revPerm) (π * Fin.revPerm) (S.image Fin.rev) := by
  obtain ⟨f, hf, rfl, hv⟩ := isCopy_orderEmb h
  have him : (univ.image f).image Fin.rev = univ.image (fun a => Fin.rev (f (Fin.rev a))) := by
    ext x
    simp only [mem_image, mem_univ, true_and, exists_exists_eq_and]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨Fin.rev a, by simp⟩
    · rintro ⟨a, rfl⟩; exact ⟨Fin.rev a, rfl⟩
  rw [him]
  apply isCopy_image_of_strictMono
  · intro a b hab
    simp only [Fin.rev_lt_rev]
    exact hf (Fin.rev_lt_rev.2 hab)
  · intro a b
    simpa using hv (Fin.rev a) (Fin.rev b)

theorem numCopies_rev_le (σ : Perm (Fin k)) (π : Perm (Fin n)) :
    numCopies σ π ≤ numCopies (σ * Fin.revPerm) (π * Fin.revPerm) := by
  classical
  unfold numCopies
  refine card_le_card_of_injOn (fun S => S.image Fin.rev) ?_ ?_
  · intro S hS
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
    exact isCopy_rev hS
  · intro S _ T _ hST
    exact image_injective Fin.rev_injective hST

theorem numCopies_rev (σ : Perm (Fin k)) (π : Perm (Fin n)) :
    numCopies (σ * Fin.revPerm) (π * Fin.revPerm) = numCopies σ π := by
  refine le_antisymm ?_ (numCopies_rev_le σ π)
  have := numCopies_rev_le (σ * Fin.revPerm) (π * Fin.revPerm)
  simpa [mul_assoc, revPerm_mul_revPerm] using this

theorem maxDisp_rev_le (π π' θ : Perm (Fin n)) :
    maxDisp (π * Fin.revPerm) (π' * Fin.revPerm) (Fin.revPerm * θ * Fin.revPerm) ≤
      maxDisp π π' θ := by
  refine Finset.sup_le fun i _ => ?_
  have h := disp_le π π' θ (Fin.rev i)
  have e1 : ((i : ℤ) - ((Fin.revPerm * θ * Fin.revPerm : Perm (Fin n)) i : ℕ)) =
      -(((Fin.rev i : ℕ) : ℤ) - (θ (Fin.rev i) : ℕ)) := by
    simp only [Perm.mul_apply, Fin.revPerm_apply, Fin.val_rev]
    have := (θ (Fin.rev i)).isLt
    have := i.isLt
    omega
  simp only [Perm.mul_apply, Fin.revPerm_apply, Fin.rev_rev] at e1 h ⊢
  rw [e1, Int.natAbs_neg]
  exact h

theorem maxDisp_compl_le (π π' θ : Perm (Fin n)) :
    maxDisp (Fin.revPerm * π) (Fin.revPerm * π') θ ≤ maxDisp π π' θ := by
  refine Finset.sup_le fun i _ => ?_
  have h := disp_le π π' θ i
  have e1 : (((Fin.revPerm * π : Perm (Fin n)) i : ℕ) : ℤ) - ((Fin.revPerm * π' : Perm (Fin n)) (θ i) : ℕ) =
      -(((π i : ℕ) : ℤ) - (π' (θ i) : ℕ)) := by
    simp only [Perm.mul_apply, Fin.revPerm_apply, Fin.val_rev]
    have := (π i).isLt
    have := (π' (θ i)).isLt
    omega
  rw [e1, Int.natAbs_neg]
  exact h

theorem mul_rhoInf_eq (h : n ≠ 1) (π π' : Perm (Fin n)) :
    ((n : ℝ) - 1) * rhoInf π π' = (univ.inf' univ_nonempty (maxDisp π π') : ℕ) := by
  have : (n : ℝ) - 1 ≠ 0 := by
    intro h'; apply h; exact_mod_cast (by linarith : (n : ℝ) = 1)
  unfold rhoInf
  field_simp

theorem mul_rhoInf_le_of (π₁ π₁' π π' : Perm (Fin n))
    (hle : ∀ θ, ∃ θ', maxDisp π₁ π₁' θ' ≤ maxDisp π π' θ) :
    ((n : ℝ) - 1) * rhoInf π₁ π₁' ≤ ((n : ℝ) - 1) * rhoInf π π' := by
  rcases eq_or_ne n 1 with rfl | h
  · simp
  rw [mul_rhoInf_eq h, mul_rhoInf_eq h]
  obtain ⟨θ, hθ⟩ := exists_matching π π'
  obtain ⟨θ', hθ'⟩ := hle θ
  rw [hθ]
  exact_mod_cast (Finset.inf'_le _ (mem_univ θ')).trans hθ'

/-- The reduction property of Lemma 3.1 for a pattern `σ` and length `n`. -/
def Red (n : ℕ) (σ : Perm (Fin k)) : Prop :=
  ∀ π : Perm (Fin n), 0 < numCopies σ π → ∃ π' : Perm (Fin n), π' ≠ π ∧
    ((n : ℝ) - 1) * rhoInf π π' ≤ (numCopies σ π : ℝ) - (numCopies σ π' : ℝ)

theorem red_rev {σ : Perm (Fin k)} (h : Red n σ) : Red n (σ * Fin.revPerm) := by
  intro π hπ
  obtain ⟨π₀, rfl⟩ : ∃ π₀ : Perm (Fin n), π = π₀ * Fin.revPerm :=
    ⟨π * Fin.revPerm, by rw [mul_assoc, revPerm_mul_revPerm, mul_one]⟩
  rw [numCopies_rev] at hπ
  obtain ⟨π₀', hne, hb⟩ := h π₀ hπ
  refine ⟨π₀' * Fin.revPerm, fun e => hne (mul_right_cancel e), ?_⟩
  rw [numCopies_rev, numCopies_rev]
  refine le_trans (mul_rhoInf_le_of _ _ _ _ fun θ => ⟨_, maxDisp_rev_le π₀ π₀' θ⟩) hb

theorem red_compl {σ : Perm (Fin k)} (h : Red n σ) : Red n (Fin.revPerm * σ) := by
  intro π hπ
  obtain ⟨π₀, rfl⟩ : ∃ π₀ : Perm (Fin n), π = Fin.revPerm * π₀ :=
    ⟨Fin.revPerm * π, by rw [← mul_assoc, revPerm_mul_revPerm, one_mul]⟩
  rw [numCopies_compl] at hπ
  obtain ⟨π₀', hne, hb⟩ := h π₀ hπ
  refine ⟨Fin.revPerm * π₀', fun e => hne (mul_left_cancel e), ?_⟩
  rw [numCopies_compl, numCopies_compl]
  exact le_trans (mul_rhoInf_le_of _ _ _ _ fun θ => ⟨θ, maxDisp_compl_le π₀ π₀' θ⟩) hb

theorem oneLine_injective {σ τ : Perm (Fin k)} (h : oneLine σ = oneLine τ) : σ = τ := by
  unfold oneLine at h
  have := List.ofFn_injective h
  ext i
  have := congrFun this i
  simp only [Nat.add_right_cancel_iff] at this
  exact this

/-! ### Lemma 3.1 for `(12)` -/

theorem lt_of_isCopy12_pair {π : Perm (Fin n)} {i j : Fin n} (hij : i < j)
    (h : IsCopy (1 : Perm (Fin 2)) π {i, j}) : π i < π j := by
  obtain ⟨a, b, hab, he, hv⟩ := (isCopy12_iff π _).1 h
  have ha : a ∈ ({i, j} : Finset (Fin n)) := by rw [he]; simp
  have hb : b ∈ ({i, j} : Finset (Fin n)) := by rw [he]; simp
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd hab (lt_irrefl _)
  · exact hv
  · exact absurd (hab.trans hij) (lt_irrefl _)
  · exact absurd hab (lt_irrefl _)

theorem red_12 : Red n (1 : Perm (Fin 2)) := by
  intro π hπ
  obtain ⟨S, hS⟩ := exists_copy_of_pos hπ
  have hn := le_of_isCopy hS
  obtain ⟨a, b, hab, -, hv⟩ := (isCopy12_iff π S).1 hS
  obtain ⟨i, j, hij, hv'⟩ := exists_adj12 π (b - a) a b (by rw [Fin.lt_def] at hab; omega) hv
  have hlt : i < j := by rw [Fin.lt_def]; omega
  have hcount : numCopies (1 : Perm (Fin 2)) (π * Equiv.swap i j) + ({{i, j}} : Finset (Finset (Fin n))).card ≤
      numCopies (1 : Perm (Fin 2)) π := by
    refine numCopies_add_le _ _ _ _ (image_injective (Equiv.injective _))
      (claim_3_4_aux π i j hij hv') _ ?_ ?_
    · intro T hT
      rw [mem_singleton.1 hT, isCopy12_iff]
      exact ⟨i, j, hlt, rfl, hv'⟩
    · intro S' hS' hmem
      have hS'e : S' = {j, i} := by
        have := congrArg (fun T => T.image (Equiv.swap i j)) (mem_singleton.1 hmem)
        have hc : ⇑(Equiv.swap i j) ∘ ⇑(Equiv.swap i j) = id :=
          funext fun x => swap_apply_self i j x
        simpa [image_image, hc, swap_apply_left, swap_apply_right] using this
      rw [hS'e, pair_comm] at hS'
      have := lt_of_isCopy12_pair hlt hS'
      simp [swap_apply_left, swap_apply_right] at this
      exact lt_asymm this hv'
  rw [card_singleton] at hcount
  refine ⟨π * Equiv.swap i j, fun e => by rw [e] at hcount; omega, ?_⟩
  have hρ := rhoInf_mul_le (by omega) π (Equiv.swap i j) 1 (fun x => by
    rw [swap_inv, swap_apply_def]
    split_ifs with h1 h2 <;> subst_vars <;> omega)
  have : (1 : ℝ) ≤ (numCopies (1 : Perm (Fin 2)) π : ℝ) -
      numCopies (1 : Perm (Fin 2)) (π * Equiv.swap i j) := by
    have : ((numCopies (1 : Perm (Fin 2)) (π * Equiv.swap i j) + 1 : ℕ) : ℝ) ≤
      numCopies (1 : Perm (Fin 2)) π := by exact_mod_cast hcount
    push_cast at this; linarith
  push_cast at hρ
  linarith

/-! ### The stable partition of Construction 3.6, for a general sorting key -/

section Key

variable {π s : Perm (Fin n)} {K : Fin n → ℕ} {x₂ x₃ : Fin n}

/-- The hypotheses of the `(132)` construction: `K` is the key of Construction 3.6 and `s` sorts
it. (Stated for a general `K` because `key36` is defined after Lemma 3.1.) -/
structure KeyHyp (π s : Perm (Fin n)) (K : Fin n → ℕ) (x₂ x₃ : Fin n) : Prop where
  hK : ∀ i, K i = if i ≤ x₂ then (if π x₃ < π i then (i : ℕ) else n + i) else 2 * n + i
  hs : Monotone (K ∘ s)
  h23 : x₂ < x₃

theorem perm_val_eq_card (θ : Perm (Fin n)) (i : Fin n) :
    (θ i : ℕ) = (univ.filter fun j => θ j < θ i).card := by
  have : (univ.filter fun j => θ j < θ i) = (Iio (θ i)).map θ.symm.toEmbedding := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_map, mem_Iio, Equiv.toEmbedding_apply]
    constructor
    · intro h; exact ⟨θ j, h, by simp⟩
    · rintro ⟨p, hp, rfl⟩; simpa using hp
  rw [this, card_map, Fin.card_Iio]

theorem KeyHyp.val_ne (H : KeyHyp π s K x₂ x₃) {i : Fin n} (hi : i ≤ x₂) : π i ≠ π x₃ := by
  intro h
  have := π.injective h
  subst this
  exact absurd H.h23 (not_lt.2 hi)

theorem KeyHyp.injective (H : KeyHyp π s K x₂ x₃) : Function.Injective K := by
  intro i j h
  rw [H.hK, H.hK] at h
  have := i.isLt; have := j.isLt
  apply Fin.ext
  split_ifs at h <;> omega

theorem KeyHyp.inv_lt_iff (H : KeyHyp π s K x₂ x₃) (i j : Fin n) :
    s⁻¹ i < s⁻¹ j ↔ K i < K j := by
  have hsm : StrictMono (K ∘ s) := H.hs.strictMono_of_injective (H.injective.comp s.injective)
  rw [← hsm.lt_iff_lt]
  simp

theorem KeyHyp.inv_eq_self (H : KeyHyp π s K x₂ x₃) (i : Fin n)
    (h : ∀ j, K j < K i ↔ j < i) : s⁻¹ i = i := by
  apply Fin.ext
  rw [perm_val_eq_card]
  simp_rw [H.inv_lt_iff, h]
  have : (univ.filter fun j => j < i) = Iio i := by ext; simp
  rw [this, Fin.card_Iio]

theorem KeyHyp.inv_eq_of_gt (H : KeyHyp π s K x₂ x₃) {i : Fin n} (hi : x₂ < i) : s⁻¹ i = i := by
  refine H.inv_eq_self i fun j => ?_
  rw [H.hK, H.hK]
  have := i.isLt; have := j.isLt
  rw [Fin.lt_def] at hi
  split_ifs with h1 h2 h3 <;> simp only [Fin.le_def, Fin.lt_def, not_le] at * <;> omega

theorem KeyHyp.apply_eq_of_gt (H : KeyHyp π s K x₂ x₃) {p : Fin n} (hp : x₂ < p) : s p = p := by
  have := H.inv_eq_of_gt hp
  conv_lhs => rw [← this]
  simp

theorem KeyHyp.apply_le_iff (H : KeyHyp π s K x₂ x₃) (p : Fin n) : s p ≤ x₂ ↔ p ≤ x₂ := by
  constructor
  · intro h; by_contra h'; rw [H.apply_eq_of_gt (not_le.1 h')] at h; exact h' h
  · intro h; by_contra h'
    have := H.inv_eq_of_gt (not_le.1 h')
    simp at this
    rw [← this] at h'; exact h' h

theorem KeyHyp.inv_le_iff (H : KeyHyp π s K x₂ x₃) (i : Fin n) : s⁻¹ i ≤ x₂ ↔ i ≤ x₂ := by
  rw [← H.apply_le_iff]; simp

/-- Within `U ∪ R` or within `L ∪ R` (old coordinates), the key order is the position order. -/
theorem KeyHyp.key_lt_iff (H : KeyHyp π s K x₂ x₃) {i j : Fin n}
    (h : (¬ (i ≤ x₂ ∧ π i < π x₃) ∧ ¬ (j ≤ x₂ ∧ π j < π x₃)) ∨
      (¬ (i ≤ x₂ ∧ π x₃ < π i) ∧ ¬ (j ≤ x₂ ∧ π x₃ < π j))) :
    K i < K j ↔ i < j := by
  have hi : i ≤ x₂ → π i ≠ π x₃ := H.val_ne
  have hj : j ≤ x₂ → π j ≠ π x₃ := H.val_ne
  rw [H.hK, H.hK]
  have := i.isLt; have := j.isLt
  simp only [Fin.lt_def, Fin.le_def, ne_eq, Fin.ext_iff, not_and, not_lt] at h hi hj ⊢
  split_ifs with h1 h2 h3 h4 h5 h6 <;> simp only [not_le, not_lt] at * <;> omega

/-- In the new permutation `π * s`, every point of `U` is left of every point of `L`. -/
theorem KeyHyp.U_lt_L (H : KeyHyp π s K x₂ x₃) {p q : Fin n} (hp : p ≤ x₂) (hq : q ≤ x₂)
    (hpU : π x₃ < π (s p)) (hqL : π (s q) < π x₃) : p < q := by
  have h1 := (H.apply_le_iff p).2 hp
  have h2 := (H.apply_le_iff q).2 hq
  have := (H.inv_lt_iff (s p) (s q)).2 (by
    simp only [H.hK, h1, h2, hpU, not_lt.2 hqL.le, ite_true, ite_false]
    have := (s p).isLt; omega)
  simpa using this

/-- Fact 3.8 in the coordinates of `π * s`. -/
theorem KeyHyp.no_mixed (H : KeyHyp π s K x₂ x₃) {S' : Finset (Fin n)}
    (hS' : IsCopy p132 (π * s) S') :
    ¬ ((∃ p ∈ S', p ≤ x₂ ∧ π x₃ < (π * s) p) ∧ (∃ q ∈ S', q ≤ x₂ ∧ (π * s) q < π x₃)) := by
  rintro ⟨⟨p, hpS, hp, hpU⟩, ⟨q, hqS, hq, hqL⟩⟩
  obtain ⟨a, b, c, hab, hbc, rfl, h1, h2⟩ := (isCopy132_iff _ _).1 hS'
  simp only [Perm.mul_apply] at hpU hqL h1 h2
  have hpq := H.U_lt_L hp hq hpU hqL
  simp only [mem_insert, mem_singleton] at hpS hqS
  rcases hpS with rfl | rfl | rfl <;> rcases hqS with rfl | rfl | rfl
  case inr.inl.inr.inr =>
    have := H.U_lt_L hp (le_of_lt (hab.trans_le hp)) hpU (h1.trans hqL)
    order
  all_goals order

/-- Order preservation of `s` on positions avoiding `L` or avoiding `U` (new coordinates). -/
theorem KeyHyp.lt_iff_of_block (H : KeyHyp π s K x₂ x₃) {p q : Fin n}
    (h : (¬ (p ≤ x₂ ∧ (π * s) p < π x₃) ∧ ¬ (q ≤ x₂ ∧ (π * s) q < π x₃)) ∨
      (¬ (p ≤ x₂ ∧ π x₃ < (π * s) p) ∧ ¬ (q ≤ x₂ ∧ π x₃ < (π * s) q))) :
    s p < s q ↔ p < q := by
  have e := H.inv_lt_iff (s p) (s q)
  rw [show s⁻¹ (s p) = p by simp, show s⁻¹ (s q) = q by simp] at e
  rw [e, H.key_lt_iff]
  simpa only [Perm.mul_apply, H.apply_le_iff] using h

/-- Claim 3.9 in the coordinates of `π * s`. -/
theorem KeyHyp.preimage_copy (H : KeyHyp π s K x₂ x₃) {S' : Finset (Fin n)}
    (hS' : IsCopy p132 (π * s) S') : IsCopy p132 π (S'.image s) := by
  have hnm := H.no_mixed hS'
  obtain ⟨a, b, c, hab, hbc, rfl, h1, h2⟩ := (isCopy132_iff _ _).1 hS'
  have hblk : ∀ p ∈ ({a, b, c} : Finset (Fin n)), ∀ q ∈ ({a, b, c} : Finset (Fin n)),
      s p < s q ↔ p < q := by
    intro p hp q hq
    apply H.lt_iff_of_block
    by_cases hU : ∃ p ∈ ({a, b, c} : Finset (Fin n)), p ≤ x₂ ∧ π x₃ < (π * s) p
    · have hL : ¬ ∃ q ∈ ({a, b, c} : Finset (Fin n)), q ≤ x₂ ∧ (π * s) q < π x₃ :=
        fun hL => hnm ⟨hU, hL⟩
      push Not at hL
      left
      exact ⟨fun h => absurd h.2 (not_lt.2 (hL p hp h.1)),
        fun h => absurd h.2 (not_lt.2 (hL q hq h.1))⟩
    · push Not at hU
      right
      exact ⟨fun h => absurd h.2 (not_lt.2 (hU p hp h.1)),
        fun h => absurd h.2 (not_lt.2 (hU q hq h.1))⟩
  rw [isCopy132_iff]
  refine ⟨s a, s b, s c, (hblk a (by simp) b (by simp)).2 hab,
    (hblk b (by simp) c (by simp)).2 hbc, by simp [image_insert], h1, h2⟩

/-- Property 3 of Fact 3.7: positions left of every point of `L` are fixed. -/
theorem KeyHyp.inv_eq_of_lt_L (H : KeyHyp π s K x₂ x₃) {i : Fin n}
    (h : ∀ j, j ≤ x₂ ∧ π j < π x₃ → i < j) : s⁻¹ i = i := by
  by_cases hi : x₂ < i
  · exact H.inv_eq_of_gt hi
  have hi' : i ≤ x₂ := not_lt.1 hi
  have hU : π x₃ < π i := by
    rcases lt_or_gt_of_ne (H.val_ne hi') with h' | h'
    · exact absurd (h i ⟨hi', h'⟩) (lt_irrefl _)
    · exact h'
  refine H.inv_eq_self i fun j => ?_
  have hj := fun hj => h j hj
  have hjne : j ≤ x₂ → π j ≠ π x₃ := H.val_ne
  rw [H.hK, H.hK]
  have := i.isLt; have := j.isLt
  simp only [hi', hU, ite_true]
  simp only [Fin.lt_def, Fin.le_def, ne_eq, Fin.ext_iff] at hj hjne hi' hU ⊢
  split_ifs with h1 h2 <;> simp only [not_le, not_lt] at * <;> omega

/-- The displacement bound of the `(132)` case. -/
theorem KeyHyp.disp_le (H : KeyHyp π s K x₂ x₃) {j₁ : Fin n}
    (hmin : ∀ j, j ≤ x₂ ∧ π j < π x₃ → j₁ ≤ j) (i : Fin n) :
    ((i : ℤ) - (s⁻¹ i : ℤ)).natAbs ≤ (x₂ : ℕ) - j₁ := by
  by_cases hi : x₂ < i
  · rw [H.inv_eq_of_gt hi]; simp
  by_cases hi1 : i < j₁
  · rw [H.inv_eq_of_lt_L fun j hj => hi1.trans_le (hmin j hj)]; simp
  have h1 : s⁻¹ i ≤ x₂ := (H.inv_le_iff i).2 (not_lt.1 hi)
  have h2 : j₁ ≤ s⁻¹ i := by
    by_contra h2
    have hp := H.inv_eq_of_lt_L (i := s⁻¹ i) fun j hj => (not_le.1 h2).trans_le (hmin j hj)
    have := s⁻¹.injective hp
    rw [this] at h2
    exact h2 (not_lt.1 hi1)
  rw [Fin.le_def] at h1 h2
  rw [Fin.lt_def] at hi hi1
  omega


/-! ### Lemma 3.1 for `(132)` -/

theorem KeyHyp.red_step (H : KeyHyp π s K x₂ x₃) {x₁ : Fin n} (h12 : x₁ < x₂)
    (v13 : π x₁ < π x₃) (v32 : π x₃ < π x₂) :
    π * s ≠ π ∧ ((n : ℝ) - 1) * rhoInf π (π * s) ≤
      (numCopies p132 π : ℝ) - (numCopies p132 (π * s) : ℝ) := by
  classical
  set L := univ.filter fun j => j ≤ x₂ ∧ π j < π x₃ with hL
  have hx₁L : x₁ ∈ L := by simp [hL, h12.le, v13]
  set j₁ := L.min' ⟨x₁, hx₁L⟩ with hj₁
  have hj₁L : j₁ ≤ x₂ ∧ π j₁ < π x₃ := by
    have := L.min'_mem ⟨x₁, hx₁L⟩
    simpa [hL] using this
  have hmin : ∀ j, j ≤ x₂ ∧ π j < π x₃ → j₁ ≤ j := fun j hj =>
    L.min'_le j (by simp [hL, hj])
  have hj₁x₁ : j₁ ≤ x₁ := hmin x₁ ⟨h12.le, v13⟩
  -- the destroyed copies `C_x`
  let C : Fin n → Finset (Fin n) := fun x =>
    if π x₃ < π x then {j₁, x, x₃} else {x, x₂, x₃}
  have hCmem : ∀ x, x ∈ C x := fun x => by
    simp only [C]; split_ifs <;> simp
  have hCinj : Set.InjOn C (Ioc j₁ x₂ : Finset (Fin n)) := by
    intro x hx y hy hxy
    simp only [coe_Ioc, Set.mem_Ioc] at hx hy
    have h1 := hCmem x; have h2 := hCmem y
    rw [hxy] at h1; rw [← hxy] at h2
    have hx3 : x ≠ x₃ := ne_of_lt (hx.2.trans_lt H.h23)
    have hy3 : y ≠ x₃ := ne_of_lt (hy.2.trans_lt H.h23)
    have hxj : x ≠ j₁ := ne_of_gt hx.1
    have hyj : y ≠ j₁ := ne_of_gt hy.1
    simp only [C] at h1 h2
    split_ifs at h1 h2 with ha hb <;> simp only [mem_insert, mem_singleton] at h1 h2 <;>
      rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
      first | exact h1 | exact h2.symm | exact absurd h1 ‹_› | exact absurd h2 ‹_› |
        (subst h1; subst h2; rfl)
  have hD : ∀ T ∈ (Ioc j₁ x₂).image C, IsCopy p132 π T := by
    intro T hT
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hT
    rw [mem_Ioc] at hx
    rw [isCopy132_iff]
    simp only [C]
    split_ifs with hU
    · exact ⟨j₁, x, x₃, hx.1, hx.2.trans_lt H.h23, rfl, hj₁L.2, hU⟩
    · have hxL : π x < π x₃ := lt_of_le_of_ne (not_lt.1 hU) (H.val_ne hx.2)
      have hx2 : x ≠ x₂ := by rintro rfl; exact hU v32
      exact ⟨x, x₂, x₃, lt_of_le_of_ne hx.2 hx2, H.h23, rfl, hxL, v32⟩
  have hDg : ∀ S', IsCopy p132 (π * s) S' → S'.image s ∉ (Ioc j₁ x₂).image C := by
    intro S' hS' hmem
    obtain ⟨x, hx, hCx⟩ := mem_image.1 hmem
    rw [mem_Ioc] at hx
    -- an old `U`-point and an old `L`-point of `C x`
    have key : ∀ u ∈ C x, u ≤ x₂ → ∃ p ∈ S', p ≤ x₂ ∧ π u = (π * s) p := by
      intro u hu hu2
      rw [hCx] at hu
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hu
      exact ⟨p, hp, (H.apply_le_iff p).1 hu2, rfl⟩
    obtain ⟨u, hu, hu2, huU, l, hl, hl2, hlL⟩ : ∃ u ∈ C x, u ≤ x₂ ∧ π x₃ < π u ∧
        ∃ l ∈ C x, l ≤ x₂ ∧ π l < π x₃ := by
      simp only [C]
      split_ifs with hU
      · exact ⟨x, by simp, hx.2, hU, j₁, by simp, hj₁L.1, hj₁L.2⟩
      · exact ⟨x₂, by simp, le_rfl, v32, x, by simp, hx.2,
          lt_of_le_of_ne (not_lt.1 hU) (H.val_ne hx.2)⟩
    obtain ⟨p, hp, hp2, hpe⟩ := key u hu hu2
    obtain ⟨q, hq, hq2, hqe⟩ := key l hl hl2
    exact H.no_mixed hS' ⟨⟨p, hp, hp2, hpe ▸ huU⟩, ⟨q, hq, hq2, hqe ▸ hlL⟩⟩
  have hcount := numCopies_add_le p132 π (π * s) (fun S' => S'.image s)
    (image_injective s.injective) (fun S' hS' => H.preimage_copy hS') _ hD hDg
  rw [card_image_of_injOn hCinj, Fin.card_Ioc] at hcount
  have hgap : 1 ≤ (x₂ : ℕ) - j₁ := by rw [Fin.le_def] at hj₁x₁; omega
  refine ⟨fun e => by rw [e] at hcount; omega, ?_⟩
  have hn : 2 ≤ n := by have := x₃.isLt; rw [Fin.lt_def] at h12; have := H.h23; rw [Fin.lt_def] at this; omega
  have hρ := rhoInf_mul_le hn π s ((x₂ : ℕ) - j₁) (H.disp_le hmin)
  have : (((x₂ : ℕ) - j₁ : ℕ) : ℝ) ≤ (numCopies p132 π : ℝ) - numCopies p132 (π * s) := by
    have : ((numCopies p132 (π * s) + ((x₂ : ℕ) - j₁) : ℕ) : ℝ) ≤ numCopies p132 π := by
      exact_mod_cast hcount
    push_cast at this ⊢; linarith
  linarith

end Key

theorem red_132 : Red n p132 := by
  intro π hπ
  obtain ⟨S, hS⟩ := exists_copy_of_pos hπ
  obtain ⟨x₁, x₂, x₃, h12, h23, -, v13, v32⟩ := (isCopy132_iff π S).1 hS
  let K : Fin n → ℕ := fun i =>
    if i ≤ x₂ then (if π x₃ < π i then (i : ℕ) else n + i) else 2 * n + i
  have H : KeyHyp π (Tuple.sort K) K x₂ x₃ := ⟨fun _ => rfl, Tuple.monotone_sort K, h23⟩
  obtain ⟨hne, hb⟩ := H.red_step h12 v13 v32
  exact ⟨_, hne, hb⟩

theorem red_of_mem (σ : Perm (Fin k)) (hσ : oneLine σ ∈ linearPatterns) : Red n σ := by
  have hlen : (oneLine σ).length = k := by simp [oneLine]
  simp only [linearPatterns, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with h | h | h | h | h | h <;> rw [h] at hlen <;> simp at hlen <;> subst hlen
  · rw [oneLine_injective (τ := 1) (h.trans (by decide))]; exact red_12
  · rw [oneLine_injective (τ := 1 * Fin.revPerm) (h.trans (by decide))]; exact red_rev red_12
  · rw [oneLine_injective (τ := p132) (h.trans (by decide))]; exact red_132
  · rw [oneLine_injective (τ := p132 * Fin.revPerm) (h.trans (by decide))]
    exact red_rev red_132
  · rw [oneLine_injective (τ := Fin.revPerm * p132) (h.trans (by decide))]
    exact red_compl red_132
  · rw [oneLine_injective (τ := Fin.revPerm * p132 * Fin.revPerm) (h.trans (by decide))]
    exact red_rev (red_compl red_132)

end Sec3

/-- **Lemma 3.1.** If `σ` is one of `(12), (21), (132), (231), (312), (213)` and `N_σ(π) > 0`,
there is `π' ≠ π` with `N_σ(π) - N_σ(π') ≥ (n-1) ρ_∞(π, π')`. -/
theorem lemma_3_1 (σ : Perm (Fin k)) (hσ : oneLine σ ∈ linearPatterns) (π : Perm (Fin n))
    (hπ : 0 < numCopies σ π) :
    ∃ π' : Perm (Fin n), π' ≠ π ∧
      ((n : ℝ) - 1) * rhoInf π π' ≤ (numCopies σ π : ℝ) - (numCopies σ π' : ℝ) := by
  exact Sec3.red_of_mem σ hσ π hπ

/-! ## Subsection 3.1: `σ = (12)` -/

/-- **Claim 3.2.** If `N_{(12)}(π) > 0`, some `(12)`-copy occupies two adjacent positions
`i, i+1` (horizontal gap `Σ(2)_x - Σ(1)_x = 1`). -/
theorem claim_3_2 (π : Perm (Fin n)) (h : 0 < numCopies (1 : Perm (Fin 2)) π) :
    ∃ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 ∧ IsCopy (1 : Perm (Fin 2)) π {i, j} := by
  exact Sec3.claim_3_2_aux π h

/-- **Construction 3.3.** For adjacent positions `i* = i`, `i* + 1 = j`, the permutation `π'`
with `π'(i*) = π(i*+1)`, `π'(i*+1) = π(i*)` and `π'(i) = π(i)` otherwise. The matching
`Φ : Π → Π'` of the paper sends the canonical point of position `a` to the canonical point of
position `swap i j a` of `π'` (it keeps every `y`-coordinate and swaps the two `x`-coordinates). -/
def con_3_3 (π : Perm (Fin n)) (i j : Fin n) : Perm (Fin n) := π * Equiv.swap i j

/-- **Claim 3.4.** In the setting of Construction 3.3 (with `π(i*) < π(i*+1)`), the preimage
under `Φ` of a `(12)`-copy of `π'` is a `(12)`-copy of `π`. In indices: if `S'` is a
`(12)`-copy of `π'`, then `swap i j '' S'` is a `(12)`-copy of `π`. -/
theorem claim_3_4 (π : Perm (Fin n)) (i j : Fin n) (hij : (j : ℕ) = (i : ℕ) + 1)
    (hπ : π i < π j) (S' : Finset (Fin n)) (hS' : IsCopy (1 : Perm (Fin 2)) (con_3_3 π i j) S') :
    IsCopy (1 : Perm (Fin 2)) π (S'.image (Equiv.swap i j)) := by
  exact Sec3.claim_3_4_aux π i j hij hπ S' hS'

/-! ## Subsection 3.2: `σ = (132)` -/

/-- **Claim 3.5.** If `N_{(132)}(π) > 0`, some `(132)`-copy has its first two positions adjacent:
positions `a < b < c` with `b = a + 1`. -/
theorem claim_3_5 (π : Perm (Fin n)) (h : 0 < numCopies p132 π) :
    ∃ a b c : Fin n, (b : ℕ) = (a : ℕ) + 1 ∧ b < c ∧ IsCopy p132 π {a, b, c} := by
  exact Sec3.claim_3_5_aux π h

/-- The standing data of the `(132)` proof of Lemma 3.1 (tex l.374–381): a `(132)`-copy at
positions `x₁ < x₂ < x₃` with `x₂ = x₁ + 1` and `π(x₁) < π(x₃) < π(x₂)`. Facts 3.7, 3.8 and Claim
3.9 use only `lt₂₃`; the fields `adj`, `v₁₃`, `v₃₂` are stated by the paper (tex l.381) and kept to
match it. -/
structure Ctx132 (π : Perm (Fin n)) (x₁ x₂ x₃ : Fin n) : Prop where
  adj : (x₂ : ℕ) = (x₁ : ℕ) + 1
  lt₂₃ : x₂ < x₃
  v₁₃ : π x₁ < π x₃
  v₃₂ : π x₃ < π x₂

/-- The regions of Construction 3.6, as subsets of the plane in the paper's 1-based
coordinates: `U = {x ≤ x₂, y > π(x₃)}`. -/
def regionU (π : Perm (Fin n)) (x₂ x₃ : Fin n) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ (x₂ : ℝ) + 1 ∧ ((π x₃ : ℕ) : ℝ) + 1 < p.2}

/-- `L = {x ≤ x₂, y < π(x₃)}` (Construction 3.6). -/
def regionL (π : Perm (Fin n)) (x₂ x₃ : Fin n) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ (x₂ : ℝ) + 1 ∧ p.2 < ((π x₃ : ℕ) : ℝ) + 1}

/-- `R = {x > x₂}` (Construction 3.6). -/
def regionR (x₂ : Fin n) : Set (ℝ × ℝ) := {p | (x₂ : ℝ) + 1 < p.1}

/-- The sorting key of Construction 3.6: positions of `U` first, then those of `L`, then those of
`R`, each block in its original order. -/
def key36 (π : Perm (Fin n)) (x₂ x₃ : Fin n) (i : Fin n) : ℕ :=
  if i ≤ x₂ then (if π x₃ < π i then i else n + i) else 2 * n + i

/-- The rearrangement of Construction 3.6: `sort36 s` is the original position of the point that
the construction moves to position `s` (the stable sort of the positions by `key36`). -/
def sort36 (π : Perm (Fin n)) (x₂ x₃ : Fin n) : Perm (Fin n) := Tuple.sort (key36 π x₂ x₃)

/-- **Construction 3.6.** Among the first `x₂` positions, move all points of `U` (in their order)
to the left of all points of `L` (in their order), fix `R`, keep every `y`-coordinate. The new
permutation is `π'(s) = π(sort36 s)`; the paper's `Φ` sends the canonical point of position `i`
of `π` to the canonical point of position `(sort36)⁻¹ i` of `π'`. -/
def con_3_6 (π : Perm (Fin n)) (x₂ x₃ : Fin n) : Perm (Fin n) := π * sort36 π x₂ x₃

namespace Sec3

theorem mem_regionU (π ρ : Perm (Fin n)) (x₂ x₃ i : Fin n) :
    canonPt ρ i ∈ regionU π x₂ x₃ ↔ i ≤ x₂ ∧ π x₃ < ρ i := by
  simp [regionU, canonPt]

theorem mem_regionL (π ρ : Perm (Fin n)) (x₂ x₃ i : Fin n) :
    canonPt ρ i ∈ regionL π x₂ x₃ ↔ i ≤ x₂ ∧ ρ i < π x₃ := by
  simp [regionL, canonPt]

theorem mem_regionR (ρ : Perm (Fin n)) (x₂ i : Fin n) :
    canonPt ρ i ∈ regionR x₂ ↔ x₂ < i := by
  simp [regionR, canonPt]

theorem canonPt_fst_lt (ρ ρ' : Perm (Fin n)) (i j : Fin n) :
    (canonPt ρ i).1 < (canonPt ρ' j).1 ↔ i < j := by
  simp [canonPt]

theorem keyHyp36 (π : Perm (Fin n)) {x₂ x₃ : Fin n} (h23 : x₂ < x₃) :
    KeyHyp π (sort36 π x₂ x₃) (key36 π x₂ x₃) x₂ x₃ :=
  ⟨fun _ => rfl, Tuple.monotone_sort _, h23⟩

end Sec3

/-- **Fact 3.7.** Properties of the bijection `Φ` of Construction 3.6 (`θ = (sort36)⁻¹` is the
new position of each old position, and `Φ(Π(i)) = Π'(θ(i))`):
1. `Φ(Π ∩ U) ⊆ U`, `Φ(Π ∩ L) ⊆ L`, `Φ(Π ∩ R) ⊆ R`;
2. if both points lie in `U ∪ R` or both in `L ∪ R`, `Φ` preserves their `x`-order;
3. points left of `j₁` (the leftmost position of `L`) are fixed. The proof uses only `x₂ < x₃`
(`hc.lt₂₃`), not the fields `adj`, `v₁₃`, `v₃₂` of `Ctx132`; the paper states them (tex l.381), and
they are kept to match the paper. -/
theorem fact_3_7 (π : Perm (Fin n)) (x₁ x₂ x₃ : Fin n) (hc : Ctx132 π x₁ x₂ x₃) :
    let π' := con_3_6 π x₂ x₃
    let θ := (sort36 π x₂ x₃)⁻¹
    (∀ i, (canonPt π i ∈ regionU π x₂ x₃ → canonPt π' (θ i) ∈ regionU π x₂ x₃) ∧
      (canonPt π i ∈ regionL π x₂ x₃ → canonPt π' (θ i) ∈ regionL π x₂ x₃) ∧
      (canonPt π i ∈ regionR x₂ → canonPt π' (θ i) ∈ regionR x₂)) ∧
    (∀ i j,
      ((canonPt π i ∈ regionU π x₂ x₃ ∪ regionR x₂ ∧ canonPt π j ∈ regionU π x₂ x₃ ∪ regionR x₂) ∨
        (canonPt π i ∈ regionL π x₂ x₃ ∪ regionR x₂ ∧ canonPt π j ∈ regionL π x₂ x₃ ∪ regionR x₂)) →
      ((canonPt π i).1 < (canonPt π j).1 ↔ (canonPt π' (θ i)).1 < (canonPt π' (θ j)).1)) ∧
    (∀ i, (∀ j, canonPt π j ∈ regionL π x₂ x₃ → i < j) → canonPt π' (θ i) = canonPt π i) := by
  intro π' θ
  have H := Sec3.keyHyp36 π hc.lt₂₃
  have hθ : ∀ i, π' (θ i) = π i := fun i => by simp [π', θ, con_3_6]
  simp only [Sec3.mem_regionU, Sec3.mem_regionL, Sec3.mem_regionR, Sec3.canonPt_fst_lt, hθ,
    Set.mem_union]
  refine ⟨fun i => ⟨fun h => ⟨(H.inv_le_iff i).2 h.1, h.2⟩, fun h => ⟨(H.inv_le_iff i).2 h.1, h.2⟩,
    fun h => by rw [H.inv_eq_of_gt h]; exact h⟩, fun i j h => ?_, fun i h => ?_⟩
  · rw [H.inv_lt_iff, H.key_lt_iff]
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · left
      exact ⟨fun h' => hi.elim (fun h => lt_asymm h.2 h'.2) (fun h => not_lt.2 h'.1 h),
        fun h' => hj.elim (fun h => lt_asymm h.2 h'.2) (fun h => not_lt.2 h'.1 h)⟩
    · right
      exact ⟨fun h' => hi.elim (fun h => lt_asymm h.2 h'.2) (fun h => not_lt.2 h'.1 h),
        fun h' => hj.elim (fun h => lt_asymm h.2 h'.2) (fun h => not_lt.2 h'.1 h)⟩
  · have hi : θ i = i := H.inv_eq_of_lt_L (i := i) h
    have e := hθ i
    rw [hi] at e
    simp only [canonPt, hi, e]

/-- **Fact 3.8.** No `(132)`-copy of `π'` (Construction 3.6) has points in both `U` and `L`. The
proof uses only `x₂ < x₃` (`hc.lt₂₃`), not the fields `adj`, `v₁₃`, `v₃₂` of `Ctx132`; the paper
states them (tex l.381), and they are kept to match the paper. -/
theorem fact_3_8 (π : Perm (Fin n)) (x₁ x₂ x₃ : Fin n) (hc : Ctx132 π x₁ x₂ x₃)
    (S' : Finset (Fin n)) (hS' : IsCopy p132 (con_3_6 π x₂ x₃) S') :
    ¬ ((∃ s ∈ S', canonPt (con_3_6 π x₂ x₃) s ∈ regionU π x₂ x₃) ∧
      (∃ s ∈ S', canonPt (con_3_6 π x₂ x₃) s ∈ regionL π x₂ x₃)) := by
  simp only [Sec3.mem_regionU, Sec3.mem_regionL]
  exact (Sec3.keyHyp36 π hc.lt₂₃).no_mixed hS'

/-- **Claim 3.9.** The preimage under `Φ` (Construction 3.6) of a `(132)`-copy of `π'` is a
`(132)`-copy of `π`: the copy at positions `S'` of `π'` comes from positions `sort36 '' S'`. The
proof uses only `x₂ < x₃` (`hc.lt₂₃`), not the fields `adj`, `v₁₃`, `v₃₂` of `Ctx132`; the paper
states them (tex l.381), and they are kept to match the paper. -/
theorem claim_3_9 (π : Perm (Fin n)) (x₁ x₂ x₃ : Fin n) (hc : Ctx132 π x₁ x₂ x₃)
    (S' : Finset (Fin n)) (hS' : IsCopy p132 (con_3_6 π x₂ x₃) S') :
    IsCopy p132 π (S'.image (sort36 π x₂ x₃)) := by
  exact (Sec3.keyHyp36 π hc.lt₂₃).preimage_copy hS'

/-! ## Subsection 3.4: upper-bound constructions -/

/-- **Construction 3.10.** For `d < n`, the permutation with `π(1) = n - d`, `π(d+1) = n` and
`π(i) = n - i + 1` otherwise (1-based), i.e. the decreasing permutation with the values at
positions `1` and `d + 1` swapped. (In the paper `d = ⌈2ε(n-1)⌉`.) -/
def con_3_10 (n d : ℕ) (hd : d < n) : Perm (Fin n) :=
  Fin.revPerm * Equiv.swap ⟨0, by omega⟩ ⟨d, hd⟩

/-- The 1-based values of Construction 3.11:
`π(i) = n` for `i = 3d-1`; `n - d` for `i = 4d-1`; `n - i` for `1 ≤ i ≤ d-1` or
`3d ≤ i ≤ 4d-2`; `n - i - 1` for `d ≤ i ≤ 3d-2`; `n - i + 1` for `i ≥ 4d`. -/
def val311 (n d i : ℕ) : ℕ :=
  if i + 1 = 3 * d then n
  else if i + 1 = 4 * d then n - d
  else if (1 ≤ i ∧ i + 1 ≤ d) ∨ (3 * d ≤ i ∧ i + 2 ≤ 4 * d) then n - i
  else if d ≤ i ∧ i + 2 ≤ 3 * d then n - i - 1
  else n - i + 1

/-- The values `val311 n d (i + 1)` lie in `[1, n]`. The proof does not use `hd : 2 ≤ d`; the paper
derives `d ≥ 2` (tex l.486), and it is kept because `con_3_11` is built from this lemma. -/
lemma val311_pos_lt (n d : ℕ) (hd : 2 ≤ d) (hn : 4 * d ≤ n) (i : Fin n) :
    1 ≤ val311 n d (i + 1) ∧ val311 n d (i + 1) ≤ n := by
  have hi := i.isLt
  unfold val311
  split_ifs <;> omega

/-- The 0-based values `val311 n d (i + 1) - 1` are injective in `i`. The proof does not use
`hd : 2 ≤ d`; the paper derives `d ≥ 2` (tex l.486), and it is kept because `con_3_11` is built from
this lemma. -/
lemma val311_injective (n d : ℕ) (hd : 2 ≤ d) (hn : 4 * d ≤ n) :
    Function.Injective fun i : Fin n => (⟨val311 n d (i + 1) - 1, by
      have := val311_pos_lt n d hd hn i; omega⟩ : Fin n) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  simp only [Fin.mk.injEq] at h
  have h1 := val311_pos_lt n d hd hn a
  have h2 := val311_pos_lt n d hd hn b
  apply Fin.ext
  unfold val311 at h h1 h2
  split_ifs at h h1 h2 <;> omega

/-- **Construction 3.11.** The permutation of length `n` with the 1-based values `val311`
(defined for `d ≥ 2` and `4d - 1 < n`; in the paper `d = ⌈2ε(n-1)⌉`). -/
noncomputable def con_3_11 (n d : ℕ) (hd : 2 ≤ d) (hn : 4 * d ≤ n) : Perm (Fin n) :=
  Equiv.ofBijective _ ((val311_injective n d hd hn).bijective_of_finite)

/-! ## Tests -/

/-- Construction 3.10 for `n = 5`, `d = 2`: `π(1) = n - d = 3`, `π(3) = 5`, otherwise
`π(i) = n - i + 1`. -/
example : oneLine (con_3_10 5 2 (by norm_num)) = [3, 4, 5, 2, 1] := by decide

/-- Construction 3.11 for `n = 9`, `d = 2` (1-based): `π(5) = n = 9` (`i = 3d-1`),
`π(7) = n - d = 7` (`i = 4d-1`), `π(1) = n - 1` and `π(6) = n - 6` (`n - i`), `π(i) = n - i - 1`
for `2 ≤ i ≤ 4`, `π(i) = n - i + 1` for `i ≥ 8`. -/
example : List.ofFn (fun i : Fin 9 => val311 9 2 (i + 1)) = [8, 6, 5, 4, 9, 3, 7, 2, 1] := by
  decide

/-- `con_3_11` has the 1-based values `val311`. -/
example (n d : ℕ) (hd : 2 ≤ d) (hn : 4 * d ≤ n) (i : Fin n) :
    ((con_3_11 n d hd hn i : ℕ) + 1) = val311 n d (i + 1) := by
  have := val311_pos_lt n d hd hn i
  simp only [con_3_11, Equiv.ofBijective_apply]
  omega

end LinfPermRemoval
