/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.Section3
import LinfPermRemoval.Section4Main

/-!
# The main theorems (Theorems 1.1 and 1.2)
-/

open Equiv Finset

namespace LinfPermRemoval

namespace MT

variable {n k : ℕ}

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

theorem exists_matching (π π' : Perm (Fin n)) :
    ∃ θ : Perm (Fin n), univ.inf' univ_nonempty (maxDisp π π') = maxDisp π π' θ := by
  obtain ⟨θ, -, h⟩ := Finset.exists_mem_eq_inf' univ_nonempty (maxDisp π π')
  exact ⟨θ, h⟩

theorem disp_le (π π' θ : Perm (Fin n)) (i : Fin n) :
    max ((i : ℤ) - (θ i : ℤ)).natAbs ((π i : ℤ) - (π' (θ i) : ℤ)).natAbs ≤ maxDisp π π' θ :=
  Finset.le_sup (f := fun i : Fin n =>
    max ((i : ℤ) - (θ i : ℤ)).natAbs ((π i : ℤ) - (π' (θ i) : ℤ)).natAbs) (mem_univ i)

theorem mul_rhoInf_eq (h : n ≠ 1) (π π' : Perm (Fin n)) :
    ((n : ℝ) - 1) * rhoInf π π' = (univ.inf' univ_nonempty (maxDisp π π') : ℕ) := by
  have : (n : ℝ) - 1 ≠ 0 := by
    intro h'; apply h; exact_mod_cast (by linarith : (n : ℝ) = 1)
  unfold rhoInf
  field_simp

/-- `ρ_∞(π, π) = 0` (the identity matching). -/
theorem mul_rhoInf_self (h : n ≠ 1) (π : Perm (Fin n)) : ((n : ℝ) - 1) * rhoInf π π = 0 := by
  rw [mul_rhoInf_eq h]
  have h0 : maxDisp π π 1 = 0 := by
    unfold maxDisp
    exact le_antisymm (Finset.sup_le fun i _ => by simp) (Nat.zero_le _)
  have := Finset.inf'_le (maxDisp π π) (mem_univ (1 : Perm (Fin n)))
  rw [h0] at this
  simp [Nat.le_zero.1 this]

/-- Definiteness: `ρ_∞(π, π') > 0` for `π ≠ π'`. -/
theorem mul_rhoInf_pos (h : n ≠ 1) {π π' : Perm (Fin n)} (hne : π ≠ π') :
    0 < ((n : ℝ) - 1) * rhoInf π π' := by
  rw [mul_rhoInf_eq h]
  obtain ⟨θ, hθ⟩ := exists_matching π π'
  rw [hθ]
  have : maxDisp π π' θ ≠ 0 := by
    intro h0
    apply hne
    ext i
    have := disp_le π π' θ i
    rw [h0] at this
    have hθi : θ i = i := Fin.ext (by omega)
    rw [hθi] at this
    omega
  exact_mod_cast Nat.pos_of_ne_zero this

/-- The triangle inequality (the paper's Remark "Metric property"): compose optimal matchings. -/
theorem mul_rhoInf_triangle (h : n ≠ 1) (π₁ π₂ π₃ : Perm (Fin n)) :
    ((n : ℝ) - 1) * rhoInf π₁ π₃ ≤
      ((n : ℝ) - 1) * rhoInf π₁ π₂ + ((n : ℝ) - 1) * rhoInf π₂ π₃ := by
  rw [mul_rhoInf_eq h, mul_rhoInf_eq h, mul_rhoInf_eq h]
  obtain ⟨θ₁, h₁⟩ := exists_matching π₁ π₂
  obtain ⟨θ₂, h₂⟩ := exists_matching π₂ π₃
  rw [h₁, h₂]
  have hle : maxDisp π₁ π₃ (θ₂ * θ₁) ≤ maxDisp π₁ π₂ θ₁ + maxDisp π₂ π₃ θ₂ := by
    refine Finset.sup_le fun i _ => ?_
    have a := disp_le π₁ π₂ θ₁ i
    have b := disp_le π₂ π₃ θ₂ (θ₁ i)
    simp only [Perm.mul_apply, max_le_iff] at a b ⊢
    omega
  have := (Finset.inf'_le (maxDisp π₁ π₃) (mem_univ (θ₂ * θ₁))).trans hle
  exact_mod_cast this

/-- The iteration of the lower-bound proof of Theorem 1.1, as strong induction on `N_σ(π)`:
some `σ`-free `γ` has `(n-1) ρ_∞(π, γ) ≤ N_σ(π)`. -/
theorem exists_free_close (σ : Perm (Fin k)) (hσ : oneLine σ ∈ linearPatterns) (hn : 2 ≤ n) :
    ∀ (N : ℕ) (π : Perm (Fin n)), numCopies σ π = N →
      ∃ γ : Perm (Fin n), IsFree σ γ ∧ ((n : ℝ) - 1) * rhoInf π γ ≤ (numCopies σ π : ℝ) := by
  have h1 : n ≠ 1 := by omega
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro π hN
  rcases Nat.eq_zero_or_pos (numCopies σ π) with h0 | hpos
  · exact ⟨π, h0, by rw [mul_rhoInf_self h1]; positivity⟩
  obtain ⟨π', hne, hle⟩ := lemma_3_1 σ hσ π hpos
  have hp := mul_rhoInf_pos h1 (Ne.symm hne)
  have hlt : numCopies σ π' < N := by
    rw [← hN]; exact_mod_cast (by linarith : (numCopies σ π' : ℝ) < numCopies σ π)
  obtain ⟨γ, hγ, hb⟩ := ih _ hlt π' rfl
  refine ⟨γ, hγ, ?_⟩
  linarith [mul_rhoInf_triangle h1 π π' γ]

end MT

/-- **Theorem 1.1, lower bound.** Let `σ ∈ {(12), (21), (132), (231), (312), (213)}`. For every
`n ≥ 2`, every `π ∈ S_n` and every `ε > 0`: if `π` is `ε`-far from `σ`-free with respect to
`ρ_∞`, then `π` contains at least `ε(n-1)` `σ`-copies. The proof does not use `hε : 0 < ε` (for
`ε ≤ 0` the statement is trivially true); the paper states it (tex l.122), and it is kept to match
the paper. -/
theorem thm_1_1_lower {k : ℕ} (σ : Perm (Fin k)) (hσ : oneLine σ ∈ linearPatterns)
    (n : ℕ) (hn : 2 ≤ n) (π : Perm (Fin n)) (ε : ℝ) (hε : 0 < ε)
    (hfar : IsFarFromFree ε σ π) :
    ε * ((n : ℝ) - 1) ≤ (numCopies σ π : ℝ) := by
  obtain ⟨γ, hγ, hb⟩ := MT.exists_free_close σ hσ hn _ π rfl
  have h := hfar γ hγ
  have : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  nlinarith

namespace MT

variable {n k : ℕ}

/-! ### Copies of `(12)` and `(132)` -/

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

/-! ### Reverse and complement (the plot symmetries) -/

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
  have e1 : (((Fin.revPerm * π : Perm (Fin n)) i : ℕ) : ℤ) -
      ((Fin.revPerm * π' : Perm (Fin n)) (θ i) : ℕ) = -(((π i : ℕ) : ℤ) - (π' (θ i) : ℕ)) := by
    simp only [Perm.mul_apply, Fin.revPerm_apply, Fin.val_rev]
    have := (π i).isLt
    have := (π' (θ i)).isLt
    omega
  rw [e1, Int.natAbs_neg]
  exact h

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

theorem oneLine_injective {σ τ : Perm (Fin k)} (h : oneLine σ = oneLine τ) : σ = τ := by
  unfold oneLine at h
  have := List.ofFn_injective h
  ext i
  have := congrFun this i
  simp only [Nat.add_right_cancel_iff] at this
  exact this

/-- Complement transports being `ε`-far from free. -/
theorem far_compl {ε : ℝ} {σ : Perm (Fin k)} {π : Perm (Fin n)} (hn : 2 ≤ n)
    (h : IsFarFromFree ε σ π) : IsFarFromFree ε (Fin.revPerm * σ) (Fin.revPerm * π) := by
  intro γ hγ
  have hγ' : IsFree σ (Fin.revPerm * γ) := by
    have e : (Fin.revPerm : Perm (Fin n)) * (Fin.revPerm * γ) = γ := by
      rw [← mul_assoc, revPerm_mul_revPerm, one_mul]
    unfold IsFree
    rw [← numCopies_compl, e]
    exact hγ
  have h1 := h _ hγ'
  have h2 : ((n : ℝ) - 1) * rhoInf π (Fin.revPerm * γ) ≤
      ((n : ℝ) - 1) * rhoInf (Fin.revPerm * π) γ := by
    refine mul_rhoInf_le_of _ _ _ _ fun θ => ⟨θ, ?_⟩
    have := maxDisp_compl_le (Fin.revPerm * π) γ θ
    rwa [← mul_assoc, revPerm_mul_revPerm, one_mul] at this
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact h1.trans (le_of_mul_le_mul_left h2 hpos)

/-- Reverse transports being `ε`-far from free. -/
theorem far_rev {ε : ℝ} {σ : Perm (Fin k)} {π : Perm (Fin n)} (hn : 2 ≤ n)
    (h : IsFarFromFree ε σ π) : IsFarFromFree ε (σ * Fin.revPerm) (π * Fin.revPerm) := by
  intro γ hγ
  have e : ∀ τ : Perm (Fin n), τ * Fin.revPerm * Fin.revPerm = τ := fun τ => by
    rw [mul_assoc, revPerm_mul_revPerm, mul_one]
  have hγ' : IsFree σ (γ * Fin.revPerm) := by
    unfold IsFree
    rw [← numCopies_rev, e]
    exact hγ
  have h1 := h _ hγ'
  have h2 : ((n : ℝ) - 1) * rhoInf π (γ * Fin.revPerm) ≤
      ((n : ℝ) - 1) * rhoInf (π * Fin.revPerm) γ := by
    refine mul_rhoInf_le_of _ _ _ _ fun θ => ⟨Fin.revPerm * θ * Fin.revPerm, ?_⟩
    have := maxDisp_rev_le (π * Fin.revPerm) γ θ
    rwa [e] at this
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact h1.trans (le_of_mul_le_mul_left h2 hpos)

theorem ub_compl {ε : ℝ} {σ : Perm (Fin k)}
    (h : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ π : Perm (Fin n),
      IsFarFromFree ε σ π ∧ (numCopies σ π : ℝ) ≤ 6 * ε * n) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ π : Perm (Fin n),
      IsFarFromFree ε (Fin.revPerm * σ) π ∧
        (numCopies (Fin.revPerm * σ) π : ℝ) ≤ 6 * ε * n := by
  obtain ⟨n₀, h⟩ := h
  refine ⟨max n₀ 2, fun n hn => ?_⟩
  obtain ⟨π, hf, hc⟩ := h n (le_of_max_le_left hn)
  exact ⟨Fin.revPerm * π, far_compl (le_of_max_le_right hn) hf, by rwa [numCopies_compl]⟩

theorem ub_rev {ε : ℝ} {σ : Perm (Fin k)}
    (h : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ π : Perm (Fin n),
      IsFarFromFree ε σ π ∧ (numCopies σ π : ℝ) ≤ 6 * ε * n) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ π : Perm (Fin n),
      IsFarFromFree ε (σ * Fin.revPerm) π ∧
        (numCopies (σ * Fin.revPerm) π : ℝ) ≤ 6 * ε * n := by
  obtain ⟨n₀, h⟩ := h
  refine ⟨max n₀ 2, fun n hn => ?_⟩
  obtain ⟨π, hf, hc⟩ := h n (le_of_max_le_left hn)
  exact ⟨π * Fin.revPerm, far_rev (le_of_max_le_right hn) hf, by rwa [numCopies_rev]⟩

/-! ### The parameters `n₀ = ⌈1/ε⌉` and `d = ⌈2ε(n-1)⌉` -/

theorem params {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 16) {n : ℕ} (hn : ⌈1 / ε⌉₊ ≤ n) :
    2 ≤ n ∧ 2 ≤ ⌈2 * ε * ((n : ℝ) - 1)⌉₊ ∧ 4 * ⌈2 * ε * ((n : ℝ) - 1)⌉₊ ≤ n ∧
      2 * ε * ((n : ℝ) - 1) ≤ ⌈2 * ε * ((n : ℝ) - 1)⌉₊ ∧
      2 * (⌈2 * ε * ((n : ℝ) - 1)⌉₊ : ℝ) - 1 ≤ 6 * ε * n := by
  have h1 : 1 / ε ≤ n := Nat.ceil_le.1 hn
  have hεn : 1 ≤ ε * n := by
    rw [div_le_iff₀ hε] at h1; linarith
  have h16 : (16 : ℝ) ≤ n := by
    have : 16 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
    linarith
  set x := 2 * ε * ((n : ℝ) - 1) with hx
  set d := ⌈x⌉₊
  have hx0 : 0 ≤ x := by rw [hx]; have := hε.le; nlinarith
  have hdx : x ≤ d := Nat.le_ceil x
  have hdlt : (d : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hx1 : (1 : ℝ) < x := by rw [hx]; nlinarith
  have hd2 : 2 ≤ d := by
    have : 1 < d := Nat.lt_ceil.2 (by exact_mod_cast hx1)
    omega
  refine ⟨by exact_mod_cast (by linarith : (2 : ℝ) ≤ n), hd2, ?_, hdx, ?_⟩
  · have : (4 * d : ℝ) < n := by
      have : ε * n ≤ n / 16 := by nlinarith
      nlinarith
    exact_mod_cast this.le
  · nlinarith

theorem abs_ge (x y d : ℕ) (h : x + d ≤ y ∨ y + d ≤ x) : (d : ℝ) ≤ |(x : ℝ) - (y : ℝ)| := by
  rcases h with h | h
  · have : (x : ℝ) + d ≤ y := by exact_mod_cast h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · have : (y : ℝ) + d ≤ x := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith

/-! ### Construction 3.10: `(12)` -/

theorem con_3_10_val (n d : ℕ) (hd : d < n) (i : Fin n) :
    ((con_3_10 n d hd i : Fin n) : ℕ) =
      if (i : ℕ) = 0 then n - 1 - d else if (i : ℕ) = d then n - 1 else n - 1 - i := by
  simp only [con_3_10, Perm.mul_apply, Fin.revPerm_apply, Fin.val_rev, swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem card_fin_range (a b : ℕ) (hb : b < n) :
    (univ.filter (fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) ≤ b)).card = b + 1 - a := by
  rw [← card_map Fin.valEmbedding]
  have : (univ.filter (fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) ≤ b)).map Fin.valEmbedding =
      Finset.Icc a b := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · rintro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [this, Nat.card_Icc]

/-- The `(12)`-copies of Construction 3.10 (0-based): `{0, j}` for `1 ≤ j ≤ d` and `{i, d}` for
`1 ≤ i ≤ d - 1` (paper: `{1, j}`, `2 ≤ j ≤ d+1`, and `{i, d+1}`, `2 ≤ i ≤ d`). -/
theorem isCopy_con_3_10_iff (n d : ℕ) (hdn : d < n) (S : Finset (Fin n)) :
    IsCopy (1 : Perm (Fin 2)) (con_3_10 n d hdn) S ↔
      (∃ j : Fin n, (1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ d) ∧ S = {⟨0, by omega⟩, j}) ∨
      (∃ i : Fin n, (1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ d - 1) ∧ S = {i, ⟨d, hdn⟩}) := by
  rw [isCopy12_iff]
  constructor
  · rintro ⟨a, b, hab, rfl, hv⟩
    rw [Fin.lt_def, con_3_10_val, con_3_10_val] at hv
    rw [Fin.lt_def] at hab
    have key : ((a : ℕ) = 0 ∧ 1 ≤ (b : ℕ) ∧ (b : ℕ) ≤ d) ∨
        ((b : ℕ) = d ∧ 1 ≤ (a : ℕ) ∧ (a : ℕ) ≤ d - 1) := by
      have := b.isLt
      split_ifs at hv <;> omega
    rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inl ⟨b, h1, by rw [show a = ⟨0, by omega⟩ from Fin.ext h0]⟩
    · exact Or.inr ⟨a, h1, by rw [show b = ⟨d, hdn⟩ from Fin.ext h0]⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩)
    · refine ⟨_, _, by rw [Fin.lt_def]; simp only; omega, rfl, ?_⟩
      rw [Fin.lt_def, con_3_10_val, con_3_10_val]
      have := j.isLt
      split_ifs <;> simp_all <;> omega
    · refine ⟨_, _, by rw [Fin.lt_def]; simp only; omega, rfl, ?_⟩
      rw [Fin.lt_def, con_3_10_val, con_3_10_val]
      have := i.isLt
      split_ifs <;> simp_all <;> omega

/-- `N_{(12)}(π) = 2d - 1` for Construction 3.10. -/
theorem numCopies_con_3_10 (n d : ℕ) (hdn : d < n) :
    numCopies (1 : Perm (Fin 2)) (con_3_10 n d hdn) = 2 * d - 1 := by
  classical
  set z : Fin n := ⟨0, by omega⟩
  set D : Fin n := ⟨d, hdn⟩
  set A := (univ.filter (fun j : Fin n => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ d)).image
    (fun j => ({z, j} : Finset (Fin n)))
  set B := (univ.filter (fun i : Fin n => 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ d - 1)).image
    (fun i => ({i, D} : Finset (Fin n)))
  have hF : univ.filter (IsCopy (1 : Perm (Fin 2)) (con_3_10 n d hdn)) = A ∪ B := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_union, A, B, mem_image,
      isCopy_con_3_10_iff n d hdn]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact Or.inl ⟨j, hj, rfl⟩
      · exact Or.inr ⟨i, hi, rfl⟩
    · rintro (⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact Or.inl ⟨j, hj, rfl⟩
      · exact Or.inr ⟨i, hi, rfl⟩
  have hA : A.card = d := by
    rw [card_image_of_injOn, card_fin_range 1 d hdn]
    · omega
    intro j hj j' hj' he
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hj hj'
    have hm : j ∈ ({z, j'} : Finset (Fin n)) := by
      simp only at he; rw [← he]; simp
    simp only [mem_insert, mem_singleton, z, Fin.ext_iff] at hm
    rcases hm with h | h
    · omega
    · exact Fin.ext h
  have hB : B.card = d - 1 := by
    rw [card_image_of_injOn, card_fin_range 1 (d - 1) (by omega)]
    · omega
    intro i hi i' hi' he
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi hi'
    have hm : i ∈ ({i', D} : Finset (Fin n)) := by
      simp only at he; rw [← he]; simp
    simp only [mem_insert, mem_singleton, D, Fin.ext_iff] at hm
    rcases hm with h | h
    · exact Fin.ext h
    · omega
  have hdisj : Disjoint A B := by
    rw [disjoint_left]
    intro S hSA hSB
    simp only [A, B, mem_image, mem_filter, mem_univ, true_and] at hSA hSB
    obtain ⟨j, hj, rfl⟩ := hSA
    obtain ⟨i, hi, he⟩ := hSB
    have hm : z ∈ ({i, D} : Finset (Fin n)) := by rw [he]; simp
    simp only [mem_insert, mem_singleton, z, D, Fin.ext_iff] at hm
    omega
  unfold numCopies
  rw [hF, card_union_of_disjoint hdisj, hA, hB]
  omega

/-! ### Construction 3.11: `(132)` -/

theorem con_3_11_val (n d : ℕ) (hd : 2 ≤ d) (hn : 4 * d ≤ n) (i : Fin n) :
    ((con_3_11 n d hd hn i : ℕ) + 1) = val311 n d (i + 1) := by
  have := val311_pos_lt n d hd hn i
  simp only [con_3_11, Equiv.ofBijective_apply]
  omega

theorem val311_desc (n d i j : ℕ) (hn : 4 * d ≤ n) (hij : i < j) (hj : j < n)
    (h1 : j ≠ 3 * d - 2) (h2 : j ≠ 4 * d - 2) : val311 n d (j + 1) < val311 n d (i + 1) := by
  unfold val311
  split_ifs <;> omega

theorem val311_le (n d i : ℕ) (hi : i < n) : val311 n d (i + 1) ≤ n := by
  unfold val311
  split_ifs <;> omega

theorem val311_b (n d : ℕ) (hd : 2 ≤ d) : val311 n d (3 * d - 2 + 1) = n := by
  unfold val311
  split_ifs <;> omega

theorem val311_c (n d : ℕ) (hd : 2 ≤ d) : val311 n d (4 * d - 2 + 1) = n - d := by
  unfold val311
  split_ifs <;> omega

theorem val311_a (n d a : ℕ) (hn : 4 * d ≤ n) (ha : a + 3 ≤ 3 * d) :
    val311 n d (a + 1) < n - d ↔ d - 1 ≤ a := by
  unfold val311
  split_ifs <;> omega

/-- The `(132)`-copies of Construction 3.11 in values (the paper's case analysis, tex
l.590-600): `c = 4d-2` (0-based) since every other `c` is below everything to its left or is the
maximum; then `b = 3d-2`; then `d - 1 ≤ a ≤ 3d - 3`. -/
theorem val311_char (n d a b c : ℕ) (hd : 2 ≤ d) (hn : 4 * d ≤ n) (hab : a < b) (hbc : b < c)
    (hc : c < n) :
    (val311 n d (a + 1) < val311 n d (c + 1) ∧ val311 n d (c + 1) < val311 n d (b + 1)) ↔
      (b = 3 * d - 2 ∧ c = 4 * d - 2 ∧ d - 1 ≤ a ∧ a ≤ 3 * d - 3) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hc' : c = 4 * d - 2 := by
      by_contra hne
      by_cases h3 : c = 3 * d - 2
      · subst h3
        rw [val311_b n d hd] at h2
        exact absurd (val311_le n d b (by omega)) (by omega)
      · exact lt_asymm h1 (val311_desc n d a c hn (by omega) hc h3 hne)
    subst hc'
    have hb : b = 3 * d - 2 := by
      by_contra hne
      have := val311_desc n d a b hn hab (by omega) hne (by omega)
      omega
    subst hb
    rw [val311_c n d hd] at h1
    exact ⟨rfl, rfl, (val311_a n d a hn (by omega)).1 h1, by omega⟩
  · rintro ⟨rfl, rfl, ha1, ha2⟩
    rw [val311_c n d hd, val311_b n d hd]
    exact ⟨(val311_a n d a hn (by omega)).2 ha1, by omega⟩

/-- The `(132)`-copies of Construction 3.11 (0-based): `{a, 3d-2, 4d-2}` for
`d - 1 ≤ a ≤ 3d - 3` (paper: `{a, 3d-1, 4d-1}`, `d ≤ a ≤ 3d-2`). -/
theorem isCopy_con_3_11_iff (n d : ℕ) (hd : 2 ≤ d) (hn : 4 * d ≤ n) (S : Finset (Fin n)) :
    IsCopy p132 (con_3_11 n d hd hn) S ↔
      ∃ a : Fin n, (d - 1 ≤ (a : ℕ) ∧ (a : ℕ) ≤ 3 * d - 3) ∧
        S = {a, ⟨3 * d - 2, by omega⟩, ⟨4 * d - 2, by omega⟩} := by
  rw [isCopy132_iff]
  have hv : ∀ x y : Fin n, con_3_11 n d hd hn x < con_3_11 n d hd hn y ↔
      val311 n d (x + 1) < val311 n d (y + 1) := by
    intro x y
    rw [Fin.lt_def, ← con_3_11_val n d hd hn x, ← con_3_11_val n d hd hn y]
    omega
  constructor
  · rintro ⟨a, b, c, hab, hbc, rfl, h1, h2⟩
    rw [hv] at h1 h2
    rw [Fin.lt_def] at hab hbc
    have := (val311_char n d a b c hd hn hab hbc c.isLt).1 ⟨h1, h2⟩
    obtain ⟨hb, hc, ha⟩ := this
    refine ⟨a, ha, ?_⟩
    ext x
    simp only [mem_insert, mem_singleton, Fin.ext_iff, hb, hc]
  · rintro ⟨a, ha, rfl⟩
    have key := (val311_char n d a (3 * d - 2) (4 * d - 2) hd hn (by omega) (by omega)
      (by omega)).2 ⟨rfl, rfl, ha⟩
    refine ⟨a, _, _, by rw [Fin.lt_def]; simp only; omega, by rw [Fin.lt_def]; simp only; omega,
      rfl, (hv _ _).2 key.1, (hv _ _).2 key.2⟩

/-- `N_{(132)}(π) = 2d - 1` for Construction 3.11. -/
theorem numCopies_con_3_11 (n d : ℕ) (hd : 2 ≤ d) (hn : 4 * d ≤ n) :
    numCopies p132 (con_3_11 n d hd hn) = 2 * d - 1 := by
  classical
  set B : Fin n := ⟨3 * d - 2, by omega⟩
  set C : Fin n := ⟨4 * d - 2, by omega⟩
  have hF : univ.filter (IsCopy p132 (con_3_11 n d hd hn)) =
      (univ.filter (fun a : Fin n => d - 1 ≤ (a : ℕ) ∧ (a : ℕ) ≤ 3 * d - 3)).image
        (fun a => ({a, B, C} : Finset (Fin n))) := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_image, isCopy_con_3_11_iff n d hd hn]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  unfold numCopies
  rw [hF, card_image_of_injOn, card_fin_range _ _ (by omega)]
  · omega
  intro a ha a' ha' he
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ha'
  have hm : a ∈ ({a', B, C} : Finset (Fin n)) := by
    simp only at he; rw [← he]; simp
  simp only [mem_insert, mem_singleton, B, C, Fin.ext_iff] at hm
  rcases hm with h | h | h
  · exact Fin.ext h
  · omega
  · omega

/-! ### The base cases `(12)` and `(132)` of the upper bound -/

theorem ub_12 {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 16) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ π : Perm (Fin n),
      IsFarFromFree ε (1 : Perm (Fin 2)) π ∧
        (numCopies (1 : Perm (Fin 2)) π : ℝ) ≤ 6 * ε * n := by
  refine ⟨⌈1 / ε⌉₊, fun n hn => ?_⟩
  obtain ⟨hn2, hd2, h4d, hdx, h6⟩ := params hε hε' hn
  set d := ⌈2 * ε * ((n : ℝ) - 1)⌉₊
  have hdn : d < n := by omega
  refine ⟨con_3_10 n d hdn, ?_, ?_⟩
  · have hS : IsCopy (1 : Perm (Fin 2)) (con_3_10 n d hdn) {⟨0, by omega⟩, ⟨d, hdn⟩} :=
      (isCopy_con_3_10_iff n d hdn _).2 (Or.inl ⟨⟨d, hdn⟩, ⟨by simp; omega, le_refl _⟩, rfl⟩)
    refine fact_2_4 _ _ _ ε hε hn2 hS ?_
    intro i hi j hj hij
    have key : ((i : ℕ) + d ≤ j ∨ (j : ℕ) + d ≤ i) ∧
        (((con_3_10 n d hdn i : Fin n) : ℕ) + d ≤ (con_3_10 n d hdn j : Fin n) ∨
          ((con_3_10 n d hdn j : Fin n) : ℕ) + d ≤ (con_3_10 n d hdn i : Fin n)) := by
      simp only [mem_insert, mem_singleton] at hi hj
      rw [con_3_10_val, con_3_10_val]
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp_all [Fin.ext_iff] <;> omega
    exact ⟨hdx.trans (abs_ge _ _ _ key.1), hdx.trans (abs_ge _ _ _ key.2)⟩
  · rw [numCopies_con_3_10 n d hdn]
    have : ((2 * d - 1 : ℕ) : ℝ) = 2 * (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; exact h6

theorem ub_132 {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 16) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ π : Perm (Fin n),
      IsFarFromFree ε p132 π ∧ (numCopies p132 π : ℝ) ≤ 6 * ε * n := by
  refine ⟨⌈1 / ε⌉₊, fun n hn => ?_⟩
  obtain ⟨hn2, hd2, h4d, hdx, h6⟩ := params hε hε' hn
  set d := ⌈2 * ε * ((n : ℝ) - 1)⌉₊
  refine ⟨con_3_11 n d hd2 h4d, ?_, ?_⟩
  · have hS : IsCopy p132 (con_3_11 n d hd2 h4d)
        {⟨2 * d - 2, by omega⟩, ⟨3 * d - 2, by omega⟩, ⟨4 * d - 2, by omega⟩} :=
      (isCopy_con_3_11_iff n d hd2 h4d _).2 ⟨⟨2 * d - 2, by omega⟩, ⟨by simp; omega, by simp; omega⟩,
        rfl⟩
    refine fact_2_4 _ _ _ ε hε hn2 hS ?_
    intro i hi j hj hij
    have key : ((i : ℕ) + d ≤ j ∨ (j : ℕ) + d ≤ i) ∧
        (((con_3_11 n d hd2 h4d i : Fin n) : ℕ) + d ≤ (con_3_11 n d hd2 h4d j : Fin n) ∨
          ((con_3_11 n d hd2 h4d j : Fin n) : ℕ) + d ≤ (con_3_11 n d hd2 h4d i : Fin n)) := by
      have e1 := con_3_11_val n d hd2 h4d ⟨2 * d - 2, by omega⟩
      have e2 := con_3_11_val n d hd2 h4d ⟨3 * d - 2, by omega⟩
      have e3 := con_3_11_val n d hd2 h4d ⟨4 * d - 2, by omega⟩
      have v1 : val311 n d (2 * d - 2 + 1) = n - 2 * d := by
        unfold val311; split_ifs <;> omega
      simp only at e1 e2 e3
      rw [val311_b n d hd2] at e2
      rw [val311_c n d hd2] at e3
      rw [v1] at e1
      simp only [mem_insert, mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
        simp only [ne_eq, Fin.ext_iff, not_true_eq_false] at hij ⊢ <;> omega
    exact ⟨hdx.trans (abs_ge _ _ _ key.1), hdx.trans (abs_ge _ _ _ key.2)⟩
  · rw [numCopies_con_3_11 n d hd2 h4d]
    have : ((2 * d - 1 : ℕ) : ℝ) = 2 * (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; exact h6

end MT

/-- **Theorem 1.1, converse (upper-bound construction).** For each such `σ` and each
`0 < ε ≤ 1/16`, for all sufficiently large `n` (depending on `σ` and `ε`) there is a permutation
`π ∈ S_n` that is `ε`-far from `σ`-free with `N_σ(π) ≤ 6εn`. -/
theorem thm_1_1_upper {k : ℕ} (σ : Perm (Fin k)) (hσ : oneLine σ ∈ linearPatterns)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 16) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ π : Perm (Fin n),
      IsFarFromFree ε σ π ∧ (numCopies σ π : ℝ) ≤ 6 * ε * n := by
  simp only [linearPatterns, List.mem_cons, List.not_mem_nil, or_false] at hσ
  have hlen : ∀ l : List ℕ, oneLine σ = l → k = l.length := fun l h => by
    rw [← h]; simp [oneLine]
  rcases hσ with h | h | h | h | h | h <;> obtain rfl := hlen _ h <;> simp only [List.length] at h
  · obtain rfl : σ = 1 := MT.oneLine_injective (by rw [h]; decide)
    exact MT.ub_12 hε hε'
  · obtain rfl : σ = Fin.revPerm * 1 := MT.oneLine_injective (by rw [h]; decide)
    exact MT.ub_compl (MT.ub_12 hε hε')
  · obtain rfl : σ = p132 := MT.oneLine_injective (by rw [h]; decide)
    exact MT.ub_132 hε hε'
  · obtain rfl : σ = p132 * Fin.revPerm := MT.oneLine_injective (by rw [h]; decide)
    exact MT.ub_rev (MT.ub_132 hε hε')
  · obtain rfl : σ = Fin.revPerm * p132 := MT.oneLine_injective (by rw [h]; decide)
    exact MT.ub_compl (MT.ub_132 hε hε')
  · obtain rfl : σ = Fin.revPerm * p132 * Fin.revPerm := MT.oneLine_injective (by rw [h]; decide)
    exact MT.ub_rev (MT.ub_compl (MT.ub_132 hε hε'))

/-- **Theorem 1.2.** For any permutation `σ` of length `k` with `k ≥ 4` or `σ ∈ {(123), (321)}`,
there exist `ε_σ > 0` and `n₀(k)` such that for every `n ≥ n₀(k)` there is a permutation
`π ∈ S_n` that is `ε_σ`-far from `σ`-free with respect to `ρ_∞` yet contains only one copy of
`σ`. (`n₀` is chosen before `σ`, so it depends only on `k`.) -/
theorem thm_1_2 (k : ℕ) :
    ∃ n₀ : ℕ, ∀ σ : Perm (Fin k), ThmHyp σ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ n ≥ n₀, ∃ π : Perm (Fin n),
        IsFarFromFree ε σ π ∧ numCopies σ π = 1 :=
  DISC.thm_1_2_of_geom k (thm_4_1 k)

end LinfPermRemoval
