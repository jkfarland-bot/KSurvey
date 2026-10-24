import QuarticSurvey.CosetSums
import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# The quartic Jacobi sum (Proposition 3.4)

For a quartic character `χ` modulo `p ≡ 5 (mod 8)` with values in `ℤ[i]`, write
`J(χ, χ) = a + b i`. Then

* `J(χ̄, χ̄) = conj J(χ, χ)` (`jacobiSum_pow_three`), so the choice of `χ` among the two
  quartic characters is the choice of the sign of `b`;
* `a² + b² = p` (`jacobiSum_norm`);
* `a ≡ -1 (mod 4)` and `b ≡ 2 (mod 4)` (`jacobiSum_mod_four`).

These are the classical evaluation [Berndt–Evans–Williams 1979, Cor. 3.10]; the proof of the
congruences pairs `x` with `1 - x`. The sharper statement `b ≡ -2 (mod 8)` under the pin
`χ(2) = i` rests on the supplementary law for the quartic character of `2` and is not
formalized here.
-/

namespace QuarticSurvey

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

omit hp in
lemma ne_one_of_orderOf_four : χ ≠ 1 := by
  intro h; rw [h, orderOf_one] at hχ; norm_num at hχ

omit hp in
lemma mul_self_ne_one_of_orderOf_four : χ * χ ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one (show χ ^ 2 = 1 by rw [sq]; exact h)
  rw [hχ] at this; norm_num at this

/-- **Proposition 3.4 (conjugation).** `J(χ̄, χ̄) = conj J(χ, χ)`. -/
theorem jacobiSum_pow_three : jacobiSum (χ ^ 3) (χ ^ 3) = star (jacobiSum χ χ) := by
  have : χ ^ 3 = χ.ringHomComp (starRingEnd GaussianInt) := by
    refine MulChar.ext fun u => ?_
    rw [MulChar.ringHomComp_apply, pow_three_apply hχ]; rfl
  rw [this, jacobiSum_ringHomComp]; rfl

/-- `J(χ, χ) · conj J(χ, χ) = p`. -/
theorem jacobiSum_mul_star : jacobiSum χ χ * star (jacobiSum χ χ) = p := by
  have hf : Function.Injective GaussianInt.toComplex := GaussianInt.toComplex_injective
  have hc : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]; exact hp.out.ne_zero.symm
  have h1 : χ.ringHomComp GaussianInt.toComplex ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff hf).2 (ne_one_of_orderOf_four hχ)
  have h2 : χ.ringHomComp GaussianInt.toComplex * χ.ringHomComp GaussianInt.toComplex ≠ 1 := by
    rw [← MulChar.ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff hf).2 (mul_self_ne_one_of_orderOf_four hχ)
  have key := jacobiSum_mul_jacobiSum_inv hc h1 h1 h2
  have h4 : χ ^ 4 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hinv : χ⁻¹ = χ ^ 3 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h4)
  rw [MulChar.ringHomComp_inv, hinv, jacobiSum_ringHomComp, jacobiSum_ringHomComp, ← map_mul,
    jacobiSum_pow_three hχ, ZMod.card] at key
  apply hf; rw [key, map_natCast]

/-- **Proposition 3.4 (norm).** `a² + b² = p`. -/
theorem jacobiSum_norm :
    (jacobiSum χ χ).re ^ 2 + (jacobiSum χ χ).im ^ 2 = p := by
  have h := jacobiSum_mul_star hχ
  rw [← Zsqrtd.norm_eq_mul_conj] at h
  have h' : (jacobiSum χ χ).norm = p := by exact_mod_cast h
  rw [Zsqrtd.norm_def] at h'
  linear_combination h'

omit hp hχ in
/-- The decision behind the congruences, checked over `ZMod 8`. -/
lemma zmod8_fact : ∀ X Y C : ZMod 8, X + Y = 2 * C + 1 → (2 * X - 1) ^ 2 + (2 * Y) ^ 2 = 5 →
    (2 * X - 1 = 3 ∨ 2 * X - 1 = 7) ∧ (2 * Y = 2 ∨ 2 * Y = 6) := by decide

/-- **Proposition 3.4 (congruences).** `a ≡ -1 (mod 4)` and `b ≡ 2 (mod 4)`. -/
theorem jacobiSum_mod_four (hp8 : p % 8 = 5) :
    (jacobiSum χ χ).re % 4 = 3 ∧ (jacobiSum χ χ).im % 4 = 2 := by
  have hp5 : 5 ≤ p := by omega
  set f : ZMod p → GaussianInt := fun x => χ x * χ (1 - x) with hf
  have hJ : jacobiSum χ χ = ∑ x, f x := rfl
  have hsym : ∀ x, f (1 - x) = f x := fun x => by simp only [hf, sub_sub_cancel, mul_comm]
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this; omega
  set x0 : ZMod p := (2 : ZMod p)⁻¹ with hx0
  have hfix : ∀ x : ZMod p, x.val = (1 - x).val ↔ x = x0 := by
    intro x
    rw [ZMod.val_injective p |>.eq_iff, hx0]
    have : x = 2⁻¹ ↔ x * 2 = 1 :=
      ⟨fun h => h ▸ inv_mul_cancel₀ h20, fun h => eq_inv_of_mul_eq_one_left h⟩
    rw [this]
    constructor <;> intro h <;> linear_combination h
  have hx0fix : 1 - x0 = x0 := by linear_combination -(inv_mul_cancel₀ h20)
  -- the terms
  have hf0 : ∀ x, f x = 0 ↔ x = 0 ∨ x = 1 := by
    intro x
    simp only [hf, mul_eq_zero, apply_eq_zero_iff hχ, sub_eq_zero]
    constructor <;> rintro (h | h) <;> simp_all [eq_comm]
  have hf4 : ∀ x, f x ≠ 0 → f x ^ 4 = 1 := by
    intro x hx
    have hx0' : x ≠ 0 := fun h => hx ((hf0 x).2 (Or.inl h))
    have hx1 : 1 - x ≠ 0 := fun h => hx ((hf0 x).2 (Or.inr (sub_eq_zero.1 h).symm))
    simp only [hf, mul_pow]
    rw [show χ x ^ 4 = 1 by simpa using unit_apply_pow_four χ hχ (Units.mk0 x hx0'),
      show χ (1 - x) ^ 4 = 1 by simpa using unit_apply_pow_four χ hχ (Units.mk0 _ hx1), one_mul]
  have hfx0 : f x0 = -1 := by
    have hc2 : χ 2 ^ 2 = -1 := by
      rcases quartic_apply_two χ hχ hp8 with h | h <;> rw [h] <;> simp [gi_sq]
    have hprod : χ x0 * χ 2 = 1 := by rw [← map_mul, hx0, inv_mul_cancel₀ h20, map_one]
    simp only [hf]; rw [hx0fix]
    linear_combination (-(χ x0 * χ 2 + 1)) * hprod + χ x0 ^ 2 * hc2
  -- the pairing `x ↔ 1 - x`
  set lt : ZMod p → Prop := fun x => x.val < (1 - x).val with hlt
  set gt : ZMod p → Prop := fun x => (1 - x).val < x.val with hgt
  have htri : ∀ x, (lt x ∧ ¬ gt x ∧ x ≠ x0) ∨ (¬ lt x ∧ gt x ∧ x ≠ x0) ∨
      (¬ lt x ∧ ¬ gt x ∧ x = x0) := by
    intro x
    have h := hfix x
    simp only [hlt, hgt]
    rcases lt_trichotomy x.val (1 - x).val with h1 | h1 | h1
    · exact Or.inl ⟨h1, by omega, fun e => by have := h.2 e; omega⟩
    · exact Or.inr (Or.inr ⟨by omega, by omega, h.1 h1⟩)
    · exact Or.inr (Or.inl ⟨by omega, h1, fun e => by have := h.2 e; omega⟩)
  have hsplit : ∀ x, f x = (if lt x then f x else 0) + (if gt x then f x else 0) +
      (if x = x0 then f x else 0) := by
    intro x
    rcases htri x with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · simp [a, b, c]
    · simp [a, b, c]
    · rw [c] at a b ⊢; simp [a, b]
  have hmirror : ∑ x, (if gt x then f x else 0) = ∑ x, (if lt x then f x else 0) :=
    Fintype.sum_equiv (Equiv.subLeft (1 : ZMod p)) _ _ fun x => by
      simp only [Equiv.subLeft_apply, hlt, hgt, sub_sub_cancel, hsym]
  set W := ∑ x, (if lt x then f x else 0) with hW
  have hJW : jacobiSum χ χ = 2 * W - 1 := by
    rw [hJ, Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib,
      Finset.sum_add_distrib, hmirror, Finset.sum_ite_eq']
    simp only [mem_univ, ↓reduceIte, hfx0]; ring
  -- counting the nonzero terms with `lt`
  have hcard : 2 * (univ.filter (fun x => lt x ∧ f x ≠ 0)).card + 1 = p - 2 := by
    have hnz : (univ.filter (fun x : ZMod p => f x ≠ 0)).card = p - 2 := by
      have : univ.filter (fun x : ZMod p => f x ≠ 0) = (univ.erase 0).erase 1 := by
        ext x; simp only [mem_filter, mem_univ, true_and, ne_eq, hf0 x, mem_erase]; tauto
      rw [this, card_erase_of_mem (by simp), card_erase_of_mem (mem_univ _), card_univ,
        ZMod.card]
      omega
    have hx0nz : f x0 ≠ 0 := by rw [hfx0]; decide
    have hpart : ∀ x : ZMod p, (if f x ≠ 0 then 1 else 0 : ℕ) =
        (if lt x ∧ f x ≠ 0 then 1 else 0) + (if gt x ∧ f x ≠ 0 then 1 else 0) +
        (if x = x0 then 1 else 0) := by
      intro x
      rcases htri x with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
      · simp [a, b, c]
      · simp [a, b, c]
      · subst c; simp [a, b, hx0nz]
    have hsum := Finset.sum_congr rfl (fun x (_ : x ∈ (univ : Finset (ZMod p))) => hpart x)
    simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at hsum
    have hgl : (univ.filter (fun x => gt x ∧ f x ≠ 0)).card =
        (univ.filter (fun x => lt x ∧ f x ≠ 0)).card := by
      refine Finset.card_equiv (Equiv.subLeft (1 : ZMod p)) fun x => ?_
      simp only [mem_filter, mem_univ, true_and, Equiv.subLeft_apply, hlt, hgt, sub_sub_cancel,
        hsym]
    rw [hnz, hgl, show (univ.filter fun x : ZMod p => x = x0).card = 1 from
      Finset.card_eq_one.2 ⟨x0, by ext y; simp⟩] at hsum
    omega
  -- parity of `W.re + W.im`
  have hpar : (W.re + W.im) % 2 = 1 := by
    let g : GaussianInt →+ ℤ := AddMonoidHom.mk' (fun z => z.re + z.im) (by intros; simp; ring)
    have hg : W.re + W.im = ∑ x, (if lt x then (f x).re + (f x).im else 0) := by
      have := map_sum g (fun x => if lt x then f x else 0) univ
      rw [← hW] at this
      change W.re + W.im = _ at this
      rw [this]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp [g]
    have hpt : ∀ x, (if lt x then (f x).re + (f x).im else 0) % 2 =
        if lt x ∧ f x ≠ 0 then 1 else 0 := by
      intro x
      by_cases hl : lt x
      · by_cases hz : f x = 0
        · simp [hl, hz]
        · rcases eq_of_pow_four_eq_one (hf4 x hz) with h | h | h | h <;> simp [hl, h, gi, Zsqrtd.ext_iff]
      · simp [hl]
    rw [hg, Finset.sum_int_mod]
    simp_rw [hpt]
    rw [Finset.sum_boole]
    have : (univ.filter (fun x => lt x ∧ f x ≠ 0)).card % 2 = 1 := by omega
    exact_mod_cast this
  -- conclude over `ZMod 8`
  have hre : (jacobiSum χ χ).re = 2 * W.re - 1 := by rw [hJW]; simp
  have him : (jacobiSum χ χ).im = 2 * W.im := by rw [hJW]; simp
  have hn := jacobiSum_norm hχ
  rw [hre, him] at hn ⊢
  obtain ⟨c, hc⟩ : ∃ c : ℤ, W.re + W.im = 2 * c + 1 := ⟨(W.re + W.im) / 2, by omega⟩
  have hp8' : ((p : ℕ) : ZMod 8) = 5 := by
    rw [← ZMod.natCast_mod, hp8]; rfl
  have hc8 := congrArg (Int.cast : ℤ → ZMod 8) hc
  have hn8 := congrArg (Int.cast : ℤ → ZMod 8) hn
  push_cast at hc8 hn8
  rw [hp8'] at hn8
  obtain ⟨h1, h2⟩ := zmod8_fact _ _ _ hc8 hn8
  have conv : ∀ (z : ℤ) (r : ℤ), ((z : ZMod 8) = (r : ZMod 8)) → z % 8 = r % 8 :=
    fun z r h => (ZMod.intCast_eq_intCast_iff' z r 8).1 h
  have k1 : (2 * W.re - 1) % 8 = 3 ∨ (2 * W.re - 1) % 8 = 7 := by
    rcases h1 with h | h
    · left; have := conv (2 * W.re - 1) 3 (by push_cast; exact h); simpa using this
    · right; have := conv (2 * W.re - 1) 7 (by push_cast; exact h); simpa using this
  have k2 : (2 * W.im) % 8 = 2 ∨ (2 * W.im) % 8 = 6 := by
    rcases h2 with h | h
    · left; have := conv (2 * W.im) 2 (by push_cast; exact h); simpa using this
    · right; have := conv (2 * W.im) 6 (by push_cast; exact h); simpa using this
  omega

end Quartic

end QuarticSurvey
