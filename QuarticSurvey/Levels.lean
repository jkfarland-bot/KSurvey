import QuarticSurvey.Basic
import QuarticSurvey.FixedBase

/-!
# The 2-power levels (Section 5 of the survey)

Let `χ` be a character modulo a prime `p` with complex values. For a value `z` put
`C_z = {n : χ n = z}` and `levelSum χ z = ∑_{n ∈ C_z} n` (least nonnegative residues).

* **Even characters** (`even_T_eq_zero`, `levelSum_even`). If `ψ(-1) = 1` and `ψ ≠ 1`, then
  `∑ ψ(n) n = 0`, i.e. `B_{1,ψ} = 0`; in coset form, every class `C_z` of an even character is
  closed under `n ↦ -n`, so `2 ∑_{C_z} n = |C_z| p`.
* **Integrality** (`p_dvd_levelSum`). If `χ^m = 1` for some `0 < m < p - 1`, then `χ` has a
  kernel element `a ≠ 1`, which permutes every class, so `p ∣ ∑_{C_z} n`.
* **Pairing** (`levelSum_add_neg`). If `χ(-1) = -1`, then `n ↦ -n` carries `C_z` onto `C_{-z}`, so
  `∑_{C_z} n + ∑_{C_{-z}} n = |C_z| p`.
* **Parity at every level** (`level_parity`). If moreover `χ^m = 1` with `0 < m < p - 1`, the
  coordinate `d_z = (∑_{C_z} n - ∑_{C_{-z}} n)/p` is an odd integer for every value `z = χ(x)`,
  `x ≠ 0`: the kernel has odd order because it does not contain `-1`.
* **The power-basis expansion** (`level_expansion`). If `χ^{2M} = 1` and `ζ` is a primitive
  `2M`-th root of unity, then `∑ χ(n) n = ∑_{r<M} (∑_{C_{ζ^r}} n - ∑_{C_{-ζ^r}} n) ζ^r`.
* **The level invariant** (`level_trace`). If `χ^{2M} = 1` (no parity hypothesis is needed), then
  `∑_{w < M} ∑_n χ^{2w+1}(n) n = M (∑_{C_1} n - ∑_{C_{-1}} n)`. For `χ` of exact order `2^a` and
  `M = 2^{a-1}` the left side is `p` times the trace of `B_{1,χ}` from `ℚ(ζ_{2^a})` to `ℚ`, so
  `2^{1-a} Tr B_{1,χ} = d_0` (Murty and Thangadurai).
-/

namespace QuarticSurvey

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `∑_{n : χ n = z} n` over least nonnegative residues. -/
noncomputable def levelSum (χ : MulChar (ZMod p) ℂ) (z : ℂ) : ℤ :=
  ∑ n ∈ univ.filter (fun n : ZMod p => χ n = z), (n.val : ℤ)

lemma levelSum_eq_sum_ite (χ : MulChar (ZMod p) ℂ) (z : ℂ) :
    levelSum χ z = ∑ n : ZMod p, if χ n = z then (n.val : ℤ) else 0 := by
  rw [levelSum, Finset.sum_filter]

lemma mulChar_zero (χ : MulChar (ZMod p) ℂ) : χ 0 = 0 :=
  MulChar.map_nonunit χ not_isUnit_zero

/-- `val (-n) + val n = p` for `n ≠ 0`, as integers. -/
lemma val_neg_add (n : ZMod p) (hn : n ≠ 0) : ((-n).val : ℤ) + n.val = p := by
  rw [val_neg_of_ne_zero hn]
  have := ZMod.val_lt n
  push_cast [show n.val ≤ p from this.le]
  ring

/-- Substituting `n ↦ -n` in a class: `∑_{C_{w}} f(-n) = ∑_{C_{χ(-1) w}} f(n)`, in the form used
below. -/
lemma sum_class_neg (χ : MulChar (ZMod p) ℂ) (z : ℂ) (f : ZMod p → ℤ) :
    ∑ n ∈ univ.filter (fun n : ZMod p => χ n = z), f (-n) =
      ∑ n ∈ univ.filter (fun n : ZMod p => χ (-n) = z), f n := by
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun n => by simp)

lemma apply_ne_zero (χ : MulChar (ZMod p) ℂ) {x : ZMod p} (hx : x ≠ 0) : χ x ≠ 0 := by
  have := Units.ne_zero (χ.toUnitHom (Ne.isUnit hx).unit)
  rwa [MulChar.coe_toUnitHom, IsUnit.unit_spec] at this

/-! ### Even characters -/

/-- **`B_{1,ψ} = 0` for even `ψ ≠ 1`.** -/
theorem even_T_eq_zero (ψ : MulChar (ZMod p) ℂ) (heven : ψ (-1) = 1) (hne : ψ ≠ 1) :
    T ψ = 0 := by
  have hrefl : T ψ = ∑ n : ZMod p, ψ n * ((p : ℂ) - n.val) := by
    have e : ∑ n : ZMod p, ψ (-n) * ((-n).val : ℂ) = T ψ :=
      Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun n => rfl)
    rw [← e]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n = 0
    · subst hn; simp [mulChar_zero]
    · have h1 : ψ (-n) = ψ n := by
        rw [show -n = (-1) * n by ring, map_mul, heven, one_mul]
      rw [h1, val_neg_of_ne_zero hn]
      push_cast [(ZMod.val_lt n).le]
      ring
  have hsum : ∑ n : ZMod p, ψ n = 0 := MulChar.sum_eq_zero_of_ne_one hne
  have h2 : 2 * T ψ = (p : ℂ) * ∑ n : ZMod p, ψ n := by
    calc 2 * T ψ = T ψ + T ψ := two_mul _
      _ = ∑ n : ZMod p, ψ n * (n.val : ℂ) + ∑ n : ZMod p, ψ n * ((p : ℂ) - n.val) := by
          nth_rewrite 2 [hrefl]; rfl
      _ = (p : ℂ) * ∑ n : ZMod p, ψ n := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
  rw [hsum, mul_zero] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · norm_num at h
  · exact h

/-- **Coset form.** For an even character every class `C_z`, `z ≠ 0`, has `2 ∑_{C_z} n = |C_z| p`. -/
theorem levelSum_even (ψ : MulChar (ZMod p) ℂ) (heven : ψ (-1) = 1) {z : ℂ} (hz : z ≠ 0) :
    2 * levelSum ψ z = (univ.filter fun n : ZMod p => ψ n = z).card * p := by
  have hneg : ∀ n : ZMod p, ψ (-n) = ψ n := fun n => by
    rw [show -n = (-1) * n by ring, map_mul, heven, one_mul]
  have h1 : levelSum ψ z = ∑ n ∈ univ.filter (fun n : ZMod p => ψ n = z), ((-n).val : ℤ) := by
    have := sum_class_neg ψ z (fun m => (m.val : ℤ))
    simp only [hneg] at this
    rw [this]; rfl
  have h2 : ∀ n ∈ univ.filter (fun n : ZMod p => ψ n = z), ((-n).val : ℤ) + n.val = p := by
    intro n hn
    rw [mem_filter] at hn
    refine val_neg_add n fun h0 => hz ?_
    rw [← hn.2, h0, mulChar_zero]
  calc 2 * levelSum ψ z = levelSum ψ z + levelSum ψ z := two_mul _
    _ = ∑ n ∈ univ.filter (fun n : ZMod p => ψ n = z), (((-n).val : ℤ) + n.val) := by
        rw [Finset.sum_add_distrib]; nth_rewrite 1 [h1]; rfl
    _ = _ := by rw [Finset.sum_congr rfl h2, sum_const, nsmul_eq_mul]

/-! ### Integrality and pairing -/

/-- A kernel element `a ≠ 0, 1` when `χ^m = 1` for some `0 < m < p - 1`. -/
lemma exists_kernel_elt (χ : MulChar (ZMod p) ℂ) {m : ℕ} (hm0 : 0 < m) (hmp : m < p - 1)
    (hχm : χ ^ m = 1) : ∃ a : ZMod p, a ≠ 0 ∧ a ≠ 1 ∧ χ a = 1 := by
  obtain ⟨g, hgo, -⟩ := exists_generator (p := p)
  refine ⟨((g ^ m : (ZMod p)ˣ) : ZMod p), Units.ne_zero _, fun h => ?_, ?_⟩
  · have h1 : g ^ m = 1 := Units.ext h
    have := pow_ne_one_of_lt_orderOf hm0.ne' (by rw [hgo]; exact hmp)
    exact this h1
  · rw [Units.val_pow_eq_pow_val, map_pow, ← MulChar.pow_apply' χ hm0.ne', hχm,
      MulChar.one_apply (Units.isUnit g)]

/-- **Integrality.** `p ∣ ∑_{C_z} n` when `χ^m = 1` for some `0 < m < p - 1`. -/
theorem p_dvd_levelSum (χ : MulChar (ZMod p) ℂ) {m : ℕ} (hm0 : 0 < m) (hmp : m < p - 1)
    (hχm : χ ^ m = 1) (z : ℂ) : (p : ℤ) ∣ levelSum χ z := by
  obtain ⟨a, ha0, ha1, hχa⟩ := exists_kernel_elt χ hm0 hmp hχm
  set s0 := ∑ n : ZMod p, (if χ n = z then n else 0)
  have h : s0 = a * s0 := by
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft₀ a ha0) _ _ fun n => ?_).symm
    simp only [Equiv.mulLeft₀_apply, map_mul, hχa, one_mul, mul_ite, mul_zero]
  have h0 : s0 = 0 := by
    have : (a - 1) * s0 = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha1)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, levelSum_eq_sum_ite, Int.cast_sum, ← h0]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

/-- **Pairing.** For odd `χ`, `∑_{C_z} n + ∑_{C_{-z}} n = |C_z| p`. -/
theorem levelSum_add_neg (χ : MulChar (ZMod p) ℂ) (hodd : χ (-1) = -1) {z : ℂ} (hz : z ≠ 0) :
    levelSum χ z + levelSum χ (-z) = (univ.filter fun n : ZMod p => χ n = z).card * p := by
  have hneg : ∀ n : ZMod p, χ (-n) = -χ n := fun n => by
    rw [show -n = (-1) * n by ring, map_mul, hodd, neg_one_mul]
  have h1 : levelSum χ (-z) = ∑ n ∈ univ.filter (fun n : ZMod p => χ n = z), ((-n).val : ℤ) := by
    have := sum_class_neg χ z (fun m => (m.val : ℤ))
    simp only [hneg] at this
    rw [this]
    unfold levelSum
    congr 1
    ext n
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> intro h <;> linear_combination -h
  have h2 : ∀ n ∈ univ.filter (fun n : ZMod p => χ n = z), (n.val : ℤ) + ((-n).val : ℤ) = p := by
    intro n hn
    rw [mem_filter] at hn
    rw [add_comm]
    refine val_neg_add n fun h0 => hz ?_
    rw [← hn.2, h0, mulChar_zero]
  rw [h1, levelSum, ← Finset.sum_add_distrib, Finset.sum_congr rfl h2, sum_const, nsmul_eq_mul]

/-! ### Parity at every level -/

/-- For odd `χ`, the kernel `C_1` has odd size: it is a subgroup of `(ℤ/p)ˣ` not containing `-1`,
the only element of order `2`. -/
lemma card_kernel_odd (χ : MulChar (ZMod p) ℂ) (hodd : χ (-1) = -1) :
    Odd (univ.filter fun n : ZMod p => χ n = 1).card := by
  set K : Subgroup (ZMod p)ˣ := (MulChar.toUnitHom χ).ker
  have hmemK : ∀ u : (ZMod p)ˣ, u ∈ K ↔ χ u = 1 := by
    intro u
    simp only [K, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  -- the filter is the image of `K` in `ZMod p`
  have hcard : (univ.filter fun n : ZMod p => χ n = 1).card = Nat.card K := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    symm
    refine Finset.card_bij (fun u _ => ((u : (ZMod p)ˣ) : ZMod p)) ?_ ?_ ?_
    · intro u _
      simp only [mem_filter, mem_univ, true_and]
      exact (hmemK _).1 u.2
    · intro u _ v _ huv
      exact Subtype.ext (Units.ext huv)
    · intro n hn
      simp only [mem_filter, mem_univ, true_and] at hn
      have hu : IsUnit n := by
        by_contra hnu
        rw [MulChar.map_nonunit χ hnu] at hn
        exact zero_ne_one hn
      refine ⟨⟨hu.unit, (hmemK _).2 (by simpa using hn)⟩, mem_univ _, ?_⟩
      simp
  rw [hcard, Nat.odd_iff]
  by_contra hev
  have h2 : 2 ∣ Nat.card K := Nat.dvd_of_mod_eq_zero (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hu2 : ((u : (ZMod p)ˣ) : ZMod p) * ((u : (ZMod p)ˣ) : ZMod p) = 1 := by
    have : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have := congrArg (fun v : K => (((v : (ZMod p)ˣ)) : ZMod p)) this
    simpa [pow_two] using this
  rcases mul_self_eq_one_iff.1 hu2 with h | h
  · have : u = 1 := Subtype.ext (Units.ext h)
    rw [this, orderOf_one] at hu
    norm_num at hu
  · have hmem := (hmemK (u : (ZMod p)ˣ)).1 u.2
    rw [h, hodd] at hmem
    norm_num at hmem

/-- All classes of values of `χ` have the size of the kernel. -/
lemma card_level_eq (χ : MulChar (ZMod p) ℂ) {x : ZMod p} (hx : x ≠ 0) :
    (univ.filter fun n : ZMod p => χ n = χ x).card = (univ.filter fun n : ZMod p => χ n = 1).card := by
  have hχx : χ x ≠ 0 := apply_ne_zero χ hx
  have hinv : χ x⁻¹ * χ x = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  refine Finset.card_nbij' (fun n => x⁻¹ * n) (fun n => x * n) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hn ⊢
    rw [map_mul, hn, hinv]
  · intro n hn
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hn ⊢
    rw [map_mul, hn, mul_one]
  · intro n _; simp [← mul_assoc, mul_inv_cancel₀ hx]
  · intro n _; simp [← mul_assoc, inv_mul_cancel₀ hx]

/-- **Parity at every level.** If `χ` is odd and `χ^m = 1` with `0 < m < p - 1`, then for every value
`z = χ(x)`, `x ≠ 0`, the coordinate `d_z = (∑_{C_z} n - ∑_{C_{-z}} n)/p` is an odd integer. -/
theorem level_parity (χ : MulChar (ZMod p) ℂ) (hodd : χ (-1) = -1) {m : ℕ} (hm0 : 0 < m)
    (hmp : m < p - 1) (hχm : χ ^ m = 1) {x : ZMod p} (hx : x ≠ 0) :
    ∃ d : ℤ, Odd d ∧ levelSum χ (χ x) - levelSum χ (-χ x) = p * d := by
  have hz : χ x ≠ 0 := apply_ne_zero χ hx
  obtain ⟨s, hs⟩ := p_dvd_levelSum χ hm0 hmp hχm (χ x)
  have hpair := levelSum_add_neg χ hodd hz
  have hc := card_kernel_odd χ hodd
  rw [← card_level_eq χ hx] at hc
  set c := (univ.filter fun n : ZMod p => χ n = χ x).card
  refine ⟨2 * s - c, ?_, ?_⟩
  · have : Odd (c : ℤ) := by exact_mod_cast hc
    rcases this with ⟨r, hr⟩
    exact ⟨s - r - 1, by rw [hr]; ring⟩
  · linear_combination 2 * hs - hpair

/-! ### The level invariant -/

/-- If `z^{2M} = 1` then `∑_{w<M} z^{2w+1} = M` for `z = 1`, `-M` for `z = -1`, and `0` otherwise. -/
lemma geom_odd (M : ℕ) {z : ℂ} (hz : z ^ (2 * M) = 1) :
    ∑ w ∈ range M, z ^ (2 * w + 1) =
      (M : ℂ) * ((if z = 1 then 1 else 0) - (if z = -1 then 1 else 0)) := by
  have e : ∑ w ∈ range M, z ^ (2 * w + 1) = z * ∑ w ∈ range M, (z ^ 2) ^ w := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => ?_; ring
  rw [e]
  by_cases h2 : z ^ 2 = 1
  · rw [h2]; simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    have : z * z = 1 := by rw [← pow_two]; exact h2
    rcases mul_self_eq_one_iff.1 this with h | h
    · subst h; norm_num
    · subst h; norm_num
  · have hne : z ^ 2 - 1 ≠ 0 := sub_ne_zero.2 h2
    rw [geom_sum_eq h2, ← pow_mul, hz, sub_self, zero_div, mul_zero]
    have h1 : z ≠ 1 := fun h => h2 (by rw [h]; norm_num)
    have h3 : z ≠ -1 := fun h => h2 (by rw [h]; norm_num)
    simp [h1, h3]

/-- **The level invariant** (Murty and Thangadurai). If `χ^{2M} = 1`, then
`∑_{w<M} ∑_n χ^{2w+1}(n) n = M (∑_{C_1} n - ∑_{C_{-1}} n)`. -/
theorem level_trace (χ : MulChar (ZMod p) ℂ) {M : ℕ} (hM : χ ^ (2 * M) = 1) :
    ∑ w ∈ range M, T (χ ^ (2 * w + 1)) = (M : ℂ) * ((levelSum χ 1 - levelSum χ (-1) : ℤ) : ℂ) := by
  have hpow : ∀ w : ℕ, ∀ n : ZMod p, (χ ^ (2 * w + 1)) n = χ n ^ (2 * w + 1) :=
    fun w n => MulChar.pow_apply' χ (by omega) n
  have hroot : ∀ n : ZMod p, n ≠ 0 → χ n ^ (2 * M) = 1 := by
    intro n hn
    by_cases hM0 : 2 * M = 0
    · rw [hM0, pow_zero]
    · rw [← MulChar.pow_apply' χ hM0, hM, MulChar.one_apply (Ne.isUnit hn)]
  unfold T
  simp_rw [hpow]
  rw [Finset.sum_comm]
  have hterm : ∀ n : ZMod p, ∑ w ∈ range M, χ n ^ (2 * w + 1) * (n.val : ℂ) =
      (M : ℂ) * ((if χ n = 1 then (n.val : ℂ) else 0) - (if χ n = -1 then (n.val : ℂ) else 0)) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    · rw [← Finset.sum_mul, geom_odd M (hroot n hn)]
      split_ifs <;> ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, levelSum_eq_sum_ite, levelSum_eq_sum_ite]
  push_cast
  congr 2

/-! ### The power-basis expansion -/

/-- **The power-basis expansion.** If `χ^{2M} = 1` and `ζ` is a primitive `2M`-th root of unity,
then `∑_n χ(n) n = ∑_{r<M} (∑_{C_{ζ^r}} n - ∑_{C_{-ζ^r}} n) ζ^r`. For `χ` of exact order `2^a`,
`M = 2^{a-1}` and `ζ = χ(g)`, the coefficients are `p d_r`. -/
theorem level_expansion (χ : MulChar (ZMod p) ℂ) {M : ℕ} (hM0 : 0 < M) (hM : χ ^ (2 * M) = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * M)) :
    T χ = ∑ r ∈ range M, ((levelSum χ (ζ ^ r) - levelSum χ (-ζ ^ r) : ℤ) : ℂ) * ζ ^ r := by
  haveI : NeZero (2 * M) := ⟨by omega⟩
  have hroot : ∀ n : ZMod p, n ≠ 0 → χ n ^ (2 * M) = 1 := by
    intro n hn
    rw [← MulChar.pow_apply' χ (by omega), hM, MulChar.one_apply (Ne.isUnit hn)]
  have hhalf : ζ ^ M = -1 := by
    have hsq : ζ ^ M * ζ ^ M = 1 := by rw [← pow_add, ← two_mul, hζ.pow_eq_one]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exfalso
      have := (hζ.pow_eq_one_iff_dvd M).1 h
      have := Nat.le_of_dvd hM0 this
      omega
    · exact h
  -- Step 1: expansion over all `2M` powers.
  have step1 : T χ = ∑ r ∈ range (2 * M), ((levelSum χ (ζ ^ r) : ℤ) : ℂ) * ζ ^ r := by
    unfold T levelSum
    simp_rw [Finset.sum_filter]
    push_cast
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · obtain ⟨r, hr, hrn⟩ := hζ.eq_pow_of_pow_eq_one (hroot n hn)
      rw [Finset.sum_eq_single r]
      · rw [← hrn]; simp [mul_comm]
      · intro r' hr' hne
        have hc : χ n ≠ ζ ^ r' :=
          fun h => hne (hζ.pow_inj (Finset.mem_range.1 hr') hr (by rw [← h, hrn]))
        simp [hc]
      · intro h; exact absurd (Finset.mem_range.2 hr) h
  rw [step1, two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pow_add, hhalf]
  push_cast
  ring

end QuarticSurvey
