import QuarticSurvey.Quarters

/-!
# Reconstruction (Theorem 3.6, the formalized part)

The two quartic characters `χ`, `χ̄ = χ ^ 3` share `k` and have opposite `t`; the pin
`χ(2) = i` selects one of them; and under the pin the pair `(k, t)` and Hudson's pair `(A, B)`
determine each other.

The identification of `k² + t²` with `2 h*(p)` (Proposition 2.1, Hudson–Williams) uses the
relative class number of the imaginary cyclic quartic field and is **not** formalized; it is
recorded in the survey as a cited input.
-/

namespace QuarticSurvey

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Theorem 3.6 (formalized part).** Let `p ≡ 5 (mod 8)`, `p > 5`, and let `χ` be the pinned
quartic character. Then every quartic character `ψ` has `k ψ = k χ` and `t ψ = ± t χ`; the sign
is `+` exactly when `ψ` is pinned; and `(k, t)` and `(A, B)` determine each other. -/
theorem reconstruction (hp8 : p % 8 = 5) (hp5 : 5 < p)
    {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4) (hpin : χ 2 = gi)
    {ψ : MulChar (ZMod p) GaussianInt} (hψ : orderOf ψ = 4) :
    k ψ = k χ ∧ (t ψ = t χ ∨ t ψ = -t χ) ∧ (ψ 2 = gi ↔ ψ = χ) ∧
      2 * A χ = -3 * k χ - t χ ∧ 2 * B χ = 3 * t χ - k χ ∧
      5 * k χ = -(3 * A χ + B χ) ∧ 5 * t χ = -A χ + 3 * B χ := by
  refine ⟨?_, ?_, ?_, two_A hχ hp8 hp5 hpin, two_B hχ hp8 hp5 hpin,
    five_k hχ hp8 hp5 hpin, five_t hχ hp8 hp5 hpin⟩
  · rcases quartic_eq_or_eq_pow_three hχ hψ with rfl | rfl
    · rfl
    · exact k_pow_three hχ
  · rcases quartic_eq_or_eq_pow_three hχ hψ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (t_pow_three hχ)
  · constructor
    · intro h2
      obtain ⟨c, -, hc⟩ := existsUnique_pinned (p := p) hp8
      exact (hc ψ ⟨hψ, h2⟩).trans (hc χ ⟨hχ, hpin⟩).symm
    · rintro rfl; exact hpin

/-- **Proposition 2.1 (trace, formal part).** `T(χ) + T(χ̄) = 2 p k`, i.e. `Tr β = 2k`. -/
theorem trace_eq (hp5 : 5 < p) {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4) :
    T χ + T (χ ^ 3) = 2 * (p : GaussianInt) * (k χ) := by
  rw [T_eq hχ hp5, T_eq (orderOf_pow_three hχ) hp5, k_pow_three hχ, t_pow_three hχ]
  push_cast; ring

end QuarticSurvey
