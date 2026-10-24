import QuarticSurvey.CosetSums

/-!
# The quarter-count dictionary (Proposition 3.5, Hudson [16, Thm. 3.1])

For `p ≡ 5 (mod 8)`, `p > 5`, and the pinned quartic character (`χ 2 = i`), let
`N_r = #{n ∈ H : r p/4 < n < (r+1) p/4}` where `H = {n : χ n = 1}` is the group of fourth
powers, and put `A = N₀ - N₃`, `B = N₁ - N₂`. Then

  `2A = -3k - t`,  `2B = 3t - k`                       (`two_A`, `two_B`, equation (6))
  `5k = -(3A + B)`, `5t = -A + 3B`                      (`five_k`, `five_t`, equation (5))
  `10 S₀ = 5m - 3A - B`, …                              (`hudson_S`, equation (4))

with `m = (p-1)/4`. The proof uses only the fixed-base collapse at `b = 2` and `b = 4`
(Proposition 4.1), the oddness of `χ`, and `n ↦ -n`; it is a reconstruction of Hudson's
classical statement, not a new result.
-/

namespace QuarticSurvey

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- The quarter index `⌊4n/p⌋ ∈ {0,1,2,3}` of a residue. -/
def quarter (n : ZMod p) : ℕ := 4 * n.val / p

/-- `Q_r = ∑_{n in quarter r} χ(n)`. -/
def Q (χ : MulChar (ZMod p) GaussianInt) (r : ℕ) : GaussianInt :=
  ∑ n ∈ univ.filter (fun n : ZMod p => quarter n = r), χ n

/-- `N_r = #{n ∈ H : n in quarter r}`. -/
def N (χ : MulChar (ZMod p) GaussianInt) (r : ℕ) : ℕ :=
  (univ.filter (fun n : ZMod p => χ n = 1 ∧ quarter n = r)).card

/-- `A = N₀ - N₃`. -/
def A (χ : MulChar (ZMod p) GaussianInt) : ℤ := N χ 0 - N χ 3

/-- `B = N₁ - N₂`. -/
def B (χ : MulChar (ZMod p) GaussianInt) : ℤ := N χ 1 - N χ 2

omit hp in
lemma quarter_le (n : ZMod p) [NeZero p] : quarter n ≤ 3 := by
  have := ZMod.val_lt n
  unfold quarter
  have : 4 * n.val / p < 4 := (Nat.div_lt_iff_lt_mul (NeZero.pos p)).2 (by omega)
  omega

lemma quarter_neg (hp5 : 5 < p) {n : ZMod p} (hn : n ≠ 0) : quarter (-n) = 3 - quarter n := by
  unfold quarter
  rw [val_neg_of_ne_zero hn]
  have hv := ZMod.val_lt n
  have hv0 : n.val ≠ 0 := (ZMod.val_ne_zero n).2 hn
  set v := n.val
  have hdm := Nat.div_add_mod (4 * v) p
  have hs : 4 * v % p ≠ 0 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).1 (Nat.dvd_of_mod_eq_zero h) with h4 | hv'
    · have := Nat.le_of_dvd (by norm_num) h4; omega
    · have := Nat.le_of_dvd (by omega) hv'; omega
  have hsl := Nat.mod_lt (4 * v) (by omega : p > 0)
  have hr : 4 * v / p ≤ 3 := by
    have : 4 * v / p < 4 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega
  set r := 4 * v / p
  set s := 4 * v % p
  apply Nat.div_eq_of_lt_le
  · interval_cases r <;> omega
  · interval_cases r <;> omega

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

/-- `Q_{3-r} = -Q_r`: the reflection `n ↦ -n` and oddness of `χ`. -/
lemma Q_reflect (hp8 : p % 8 = 5) (hp5 : 5 < p) {r : ℕ} (hr : r ≤ 3) : Q χ (3 - r) = -Q χ r := by
  have hodd := quartic_apply_neg_one χ hχ hp8
  unfold Q
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine (Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun n => ?_).symm
  simp only [Equiv.neg_apply]
  by_cases hn : n = 0
  · subst hn; simp [MulChar.map_zero]
  · have hχn : χ (-n) = -χ n := by rw [show -n = -1 * n by ring, map_mul, hodd, neg_one_mul]
    have hq := quarter_le (p := p) n
    rw [quarter_neg hp5 hn, hχn]
    by_cases h : quarter n = r
    · simp [h]
    · have : ¬ 3 - quarter n = 3 - r := by omega
      simp [h, this]

/-- `#{n : χ n = -1, quarter r} = N_{3-r}`. -/
lemma card_neg_one_quarter (hp8 : p % 8 = 5) (hp5 : 5 < p) {r : ℕ} (hr : r ≤ 3) :
    (univ.filter (fun n : ZMod p => χ n = -1 ∧ quarter n = r)).card = N χ (3 - r) := by
  have hodd := quartic_apply_neg_one χ hχ hp8
  unfold N
  refine Finset.card_equiv (Equiv.neg (ZMod p)) fun n => ?_
  simp only [mem_filter, mem_univ, true_and, Equiv.neg_apply]
  have hχn : χ (-n) = -χ n := by rw [show -n = -1 * n by ring, map_mul, hodd, neg_one_mul]
  rw [hχn, neg_eq_iff_eq_neg]
  constructor
  · rintro ⟨h1, h2⟩
    have hn : n ≠ 0 := by rintro rfl; rw [MulChar.map_zero] at h1; revert h1; decide
    exact ⟨h1, by rw [quarter_neg hp5 hn, h2]⟩
  · rintro ⟨h1, h2⟩
    have hn : n ≠ 0 := by rintro rfl; rw [MulChar.map_zero] at h1; revert h1; decide
    rw [quarter_neg hp5 hn] at h2
    have := quarter_le (p := p) n
    exact ⟨h1, by omega⟩

/-- The real part of `Q_r` counts `N_r - N_{3-r}`. -/
lemma re_Q (hp8 : p % 8 = 5) (hp5 : 5 < p) {r : ℕ} (hr : r ≤ 3) :
    (Q χ r).re = (N χ r : ℤ) - N χ (3 - r) := by
  let reHom : GaussianInt →+ ℤ := AddMonoidHom.mk' Zsqrtd.re Zsqrtd.re_add
  have hsum : (Q χ r).re = ∑ n ∈ univ.filter (fun n : ZMod p => quarter n = r), (χ n).re :=
    map_sum reHom _ _
  rw [hsum, ← card_neg_one_quarter hχ hp8 hp5 hr, N]
  have hpt : ∀ n : ZMod p, (χ n).re = (if χ n = 1 then 1 else 0) - (if χ n = -1 then 1 else 0) := by
    intro n
    by_cases hn : n = 0
    · subst hn; rw [MulChar.map_zero]; decide
    · rcases quartic_values χ hχ hn with h | h | h | h <;> rw [h] <;> decide
  simp only [hpt, Finset.sum_sub_distrib, Finset.sum_boole, Finset.filter_filter]
  congr 3 <;> ext n <;> simp only [mem_filter, mem_univ, true_and] <;> tauto

omit hχ in
/-- Grouping a sum by quarters. -/
lemma sum_by_quarter (f : ℕ → GaussianInt) :
    ∑ n : ZMod p, χ n * f (quarter n) = ∑ r ∈ range 4, f r * Q χ r := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := quarter) (t := range 4)
    (fun n _ => Finset.mem_range.2 (Nat.lt_succ_of_le (quarter_le n)))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [(Finset.mem_filter.1 hn).2]; ring

omit hχ in
lemma val_small {b : ℕ} (hb : b < p) : ((b : ℕ) : ZMod p).val = b := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hb]

omit hp hχ in
lemma floor_two (n : ZMod p) : 2 * n.val / p = quarter n / 2 := by
  unfold quarter
  rw [Nat.div_div_eq_div_mul, show 4 * n.val = 2 * (2 * n.val) by ring,
    show p * 2 = 2 * p by ring, Nat.mul_div_mul_left _ _ (by norm_num)]

omit hχ in
lemma two_ne_zero' (hp5 : 5 < p) : (2 : ZMod p) ≠ 0 := by
  have := val_small (p := p) (b := 2) (by omega)
  intro h; rw [Nat.cast_ofNat, h, ZMod.val_zero] at this; omega

omit hχ in
lemma four_ne_zero' (hp5 : 5 < p) : (4 : ZMod p) ≠ 0 := by
  have := val_small (p := p) (b := 4) (by omega)
  intro h; rw [Nat.cast_ofNat, h, ZMod.val_zero] at this; omega

/-- The two linear relations behind Hudson's dictionary:
`2 Q₀ = (-3 + i) β` and `2 Q₁ = (-1 - 3i) β`, where `β = k + i t`. -/
theorem two_Q (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    2 * Q χ 0 = (-3 + gi) * ((k χ : GaussianInt) + gi * t χ) ∧
      2 * Q χ 1 = (-1 - 3 * gi) * ((k χ : GaussianInt) + gi * t χ) := by
  set β : GaussianInt := (k χ : GaussianInt) + gi * t χ with hβ
  have hT : T χ = (p : GaussianInt) * β := T_eq hχ hp5
  have hv2 : (2 : ZMod p).val = 2 := by
    have := val_small (p := p) (b := 2) (by omega); rwa [Nat.cast_ofNat] at this
  have hv4 : (4 : ZMod p).val = 4 := by
    have := val_small (p := p) (b := 4) (by omega); rwa [Nat.cast_ofNat] at this
  have e2 := fixed_base_collapse χ (two_ne_zero' hp5)
  have e4 := fixed_base_collapse χ (four_ne_zero' hp5)
  have f2 : floorSum χ 2 = Q χ 2 + Q χ 3 := by
    unfold floorSum
    rw [hv2]
    simp_rw [floor_two]
    rw [sum_by_quarter (χ := χ) (fun r => ((r / 2 : ℕ) : GaussianInt))]
    simp [Finset.sum_range_succ]
  have f4 : floorSum χ 4 = Q χ 1 + 2 * Q χ 2 + 3 * Q χ 3 := by
    unfold floorSum
    rw [hv4]
    change ∑ n, χ n * ((quarter n : ℕ) : GaussianInt) = _
    rw [sum_by_quarter (χ := χ) (fun r => ((r : ℕ) : GaussianInt))]
    simp [Finset.sum_range_succ]
  have hχ4 : χ 4 = -1 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num, map_mul, hpin, ← sq, gi_sq]
  have r3 : Q χ 3 = -Q χ 0 := Q_reflect hχ hp8 hp5 (r := 0) (by norm_num)
  have r2 : Q χ 2 = -Q χ 1 := Q_reflect hχ hp8 hp5 (r := 1) (by norm_num)
  rw [f2, hv2, hpin, hT, r2, r3] at e2
  rw [f4, hv4, hχ4, hT, r2, r3] at e4
  have hp0 : (p : GaussianInt) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have E2 : gi * (-Q χ 1 + -Q χ 0) = (2 * gi - 1) * β := by
    apply mul_left_cancel₀ hp0; push_cast at e2 ⊢; linear_combination e2
  have E4 : Q χ 1 + 3 * Q χ 0 = -5 * β := by
    apply mul_left_cancel₀ hp0; push_cast at e4 ⊢; linear_combination e4
  constructor
  · linear_combination E4 - gi * E2 - (Q χ 0 + Q χ 1 + 2 * β) * gi_sq
  · linear_combination 3 * gi * E2 + 3 * (Q χ 0 + Q χ 1 + 2 * β) * gi_sq - E4

/-- **Proposition 3.5, equation (6).** `A = -(3k + t)/2`. -/
theorem two_A (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    2 * A χ = -3 * k χ - t χ := by
  have h := congrArg Zsqrtd.re (two_Q hχ hp8 hp5 hpin).1
  have hre := re_Q hχ hp8 hp5 (r := 0) (by norm_num)
  simp [gi] at h hre
  rw [A]; linarith

/-- **Proposition 3.5, equation (6).** `B = (3t - k)/2`. -/
theorem two_B (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    2 * B χ = 3 * t χ - k χ := by
  have h := congrArg Zsqrtd.re (two_Q hχ hp8 hp5 hpin).2
  have hre := re_Q hχ hp8 hp5 (r := 1) (by norm_num)
  simp [gi] at h hre
  rw [B]; linarith

/-- **Proposition 3.5, equation (5).** `k = -(3A + B)/5`. -/
theorem five_k (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    5 * k χ = -(3 * A χ + B χ) := by
  have := two_A hχ hp8 hp5 hpin; have := two_B hχ hp8 hp5 hpin; linarith

/-- **Proposition 3.5, equation (5).** `t = (-A + 3B)/5`. -/
theorem five_t (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    5 * t χ = -A χ + 3 * B χ := by
  have := two_A hχ hp8 hp5 hpin; have := two_B hχ hp8 hp5 hpin; linarith

/-- **Proposition 3.5, equation (4)** (Hudson's formulas, cleared of denominators):
with `m = (p-1)/4`,
`10 S₀ = 5m - 3A - B`, `10 S₁ = 5m - A + 3B`, `10 S₂ = 5m + 3A + B`, `10 S₃ = 5m + A - 3B`. -/
theorem hudson_S (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    let m : ℤ := ((p - 1) / 4 : ℕ)
    10 * S χ 1 = 5 * m - 3 * A χ - B χ ∧ 10 * S χ gi = 5 * m - A χ + 3 * B χ ∧
      10 * S χ (-1) = 5 * m + 3 * A χ + B χ ∧ 10 * S χ (-gi) = 5 * m + A χ - 3 * B χ := by
  intro m
  have h0 := S_add_S_neg hχ hp8 hp5 1 (by simp)
  have h1 := S_add_S_neg hχ hp8 hp5 gi (by simp)
  have hk := five_k hχ hp8 hp5 hpin
  have ht := five_t hχ hp8 hp5 hpin
  simp only [k, t] at hk ht
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end Quartic

end QuarticSurvey
