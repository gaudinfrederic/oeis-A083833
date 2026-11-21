import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# OEIS A069881 - classification of palindromes `p` with `2p+1` palindrome

Statement (OEIS): numbers `n` such that `n` and `2n+1` are both
palindromes. Scope: `IsPal p m` classifies palindromes of exact
length `m >= 1` (no leading zero), i.e. non-trivial members `p >= 1`;
the degenerate member `p = 0` (single digit, `2*0+1 = 1` palindrome)
is outside this classification and is a separate triviality. The only
comment on the fiche (McCann 2002) notes that the
repdigits `R_d(5) = 5*(10^d-1)/9` (d digits all equal to 5:
55, 5555, ...) are terms. The even-length classification
is stated as a conjecture in Tangente (problem 8154): "on peut
conjecturer que les seuls palindromes alpha+ ayant un nombre pair de
chiffres sont 55, 5555, 555555, ..." - never proved anywhere before
this file. STATUS: the classification is now machine-proved below
(`A069881_even`: even m => all digits of p equal 5, i.e. p is a
repdigit of 5s; `A069881_overflow`: the full member dichotomy).

Mechanism (carry chain, multiplier `2`). `a j = (p / 10^j) % 10`,
`c j = (2 * (p % 10^j) + 1) / 10^j` (`c 0 = 1`, `c j ≤ 1`), output digit
`b j = (2 a j + c j) % 10`, `c (j+1) = (2 a j + c j) / 10`.

* `m' = m`  ⟹ carry chain symmetric (`c j = c (m-1-j)`), 2-periodic;
  `m` odd, `a 0 ∈ {1,2,3,4}`, and `a j ≤ 4` (`j` even) /
  `a j ≥ 5` (`j` odd).
* `m' = m+1` ⟹ boundary `(2a_0+1)%10 = c_m = 1` forces `a_0 = 5`,
  `c_1 = 1`. The joint constraints give `(2a_{j+1}+1)%10 = (10 + r)%10`
  with `r = c_{m-j-1} ∈ {0,1}`: the left side is odd, so `r = 1`; then
  `eB: 1 = (2a_{j+1} + r')/10` forces `a_{j+1} ≥ 5` while `eA` gives
  `a_{j+1} ∈ {0,5}` - hence `a_{j+1} = 5` in ONE step (fully rigid,
  no dead-end lookahead needed). Every position is `5`, `p = 55...5`.
-/

namespace A069881

/-- The `j`-th decimal digit of `n` (units = `j = 0`). -/
def dgt (n j : ℕ) : ℕ := n / 10 ^ j % 10

/-- `p` has `m`-digit palindromic decimal expansion: symmetric digits,
`10^(m-1) ≤ p < 10^m`. -/
structure IsPal (p m : ℕ) : Prop where
  sym : ∀ j < m, dgt p j = dgt p (m - 1 - j)
  lo : 10 ^ (m - 1) ≤ p
  hi : p < 10 ^ m

/-- Closed-form carry into position `j` when computing `2p+1`. -/
def crry (p j : ℕ) : ℕ := (2 * (p % 10 ^ j) + 1) / 10 ^ j

theorem crry_zero (p : ℕ) : crry p 0 = 1 := by
  unfold crry
  rw [pow_zero, Nat.mod_one]
  norm_num

theorem crry_le (p j : ℕ) : crry p j ≤ 1 := by
  have h : p % 10 ^ j < 10 ^ j := Nat.mod_lt _ (by positivity)
  have h10 : 0 < 10 ^ j := by positivity
  unfold crry
  have := (Nat.div_lt_iff_lt_mul h10).mpr (show 2 * (p % 10 ^ j) + 1 < 2 * 10 ^ j by omega)
  omega

/-- Core identity: `2p+1 = 10^j * (2 Q + c_j) + r` with `r < 10^j`. -/
theorem decomp (p j : ℕ) :
    2 * p + 1 = 10 ^ j * (2 * (p / 10 ^ j) + crry p j) +
      (2 * (p % 10 ^ j) + 1) % 10 ^ j := by
  have h1 : p = 10 ^ j * (p / 10 ^ j) + p % 10 ^ j := (Nat.div_add_mod p _).symm
  have h2 : 2 * (p % 10 ^ j) + 1 =
      10 ^ j * ((2 * (p % 10 ^ j) + 1) / 10 ^ j) + (2 * (p % 10 ^ j) + 1) % 10 ^ j :=
    (Nat.div_add_mod _ _).symm
  unfold crry
  have e3 : 10 ^ j * (2 * (p / 10 ^ j) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) =
      2 * (10 ^ j * (p / 10 ^ j)) + 10 ^ j * ((2 * (p % 10 ^ j) + 1) / 10 ^ j) := by
    ring
  rw [e3]
  omega

/-- The quotient of `2p+1` by `10^j`. -/
theorem div_ten_pow (p j : ℕ) :
    (2 * p + 1) / 10 ^ j = 2 * (p / 10 ^ j) + crry p j := by
  have h := decomp p j
  have hr : (2 * (p % 10 ^ j) + 1) % 10 ^ j < 10 ^ j :=
    Nat.mod_lt _ (by positivity)
  rw [h]
  refine Nat.div_eq_of_lt_le ?_ ?_
  · have mc : (2 * (p / 10 ^ j) + crry p j) * 10 ^ j =
        10 ^ j * (2 * (p / 10 ^ j) + crry p j) := mul_comm _ _
    omega
  · have e : (2 * (p / 10 ^ j) + crry p j + 1) * 10 ^ j =
        10 ^ j * (2 * (p / 10 ^ j) + crry p j) + 10 ^ j := by ring
    rw [e]; omega

/-- Digits of `2p+1` in terms of digits of `p` and carries. -/
theorem qdgt (p j : ℕ) :
    dgt (2 * p + 1) j = (2 * dgt p j + crry p j) % 10 := by
  unfold dgt
  rw [div_ten_pow]
  have : p / 10 ^ j = 10 * (p / 10 ^ j / 10) + p / 10 ^ j % 10 :=
    (Nat.div_add_mod _ _).symm
  omega

/-- Carry recurrence. -/
theorem crry_succ (p j : ℕ) :
    crry p (j + 1) = (2 * dgt p j + crry p j) / 10 := by
  have hmod : p % 10 ^ (j + 1) = p % 10 ^ j + 10 ^ j * (p / 10 ^ j % 10) := by
    have e1 : p / (10 ^ j * 10) = p / 10 ^ j / 10 := (Nat.div_div_eq_div_mul _ _ _).symm
    have e4 : p = 10 ^ j * 10 * (p / (10 ^ j * 10)) + p % (10 ^ j * 10) :=
      (Nat.div_add_mod p _).symm
    have e3 : p = 10 ^ j * (p / 10 ^ j) + p % 10 ^ j := (Nat.div_add_mod p _).symm
    have e2 : p / 10 ^ j = 10 * (p / (10 ^ j * 10)) + p / 10 ^ j % 10 := by
      rw [e1]; omega
    have e5 : 10 ^ j * (p / 10 ^ j) =
        10 * (10 ^ j * (p / (10 ^ j * 10))) + 10 ^ j * (p / 10 ^ j % 10) := by
      conv_lhs => rw [e2]
      ring
    have e7 : 10 ^ j * 10 * (p / (10 ^ j * 10)) =
        10 * (10 ^ j * (p / (10 ^ j * 10))) := by ring
    have hX : (10 : ℕ) ^ (j + 1) = 10 ^ j * 10 := by rw [pow_succ]
    rw [hX]
    omega
  unfold crry dgt
  rw [hmod]
  have hX : (0 : ℕ) < 10 ^ j := by positivity
  have hr : (2 * (p % 10 ^ j) + 1) % 10 ^ j < 10 ^ j := Nat.mod_lt _ hX
  have hdec : 2 * (p % 10 ^ j) + 1 =
      10 ^ j * ((2 * (p % 10 ^ j) + 1) / 10 ^ j) + (2 * (p % 10 ^ j) + 1) % 10 ^ j :=
    (Nat.div_add_mod _ _).symm
  have e5 : 2 * (p % 10 ^ j + 10 ^ j * (p / 10 ^ j % 10)) + 1 =
      10 ^ j * (2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) +
      (2 * (p % 10 ^ j) + 1) % 10 ^ j := by
    have e6 : 10 ^ j * (2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) =
        10 ^ j * (2 * (p / 10 ^ j % 10)) + 10 ^ j * ((2 * (p % 10 ^ j) + 1) / 10 ^ j) := by
      ring
    have e7 : 10 ^ j * (2 * (p / 10 ^ j % 10)) = 2 * (10 ^ j * (p / 10 ^ j % 10)) := by
      ring
    rw [e6]; omega
  rw [e5]
  have hX : (10 : ℕ) ^ (j + 1) = 10 ^ j * 10 := by rw [pow_succ]
  rw [hX]
  refine Nat.div_eq_of_lt_le ?_ ?_
  · have hY : 10 * ((2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) / 10) ≤
        2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j := by omega
    have e1 : (2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) / 10 *
        (10 ^ j * 10) = 10 * (10 ^ j *
        ((2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) := by ring
    have e2 : 10 ^ j * (10 * ((2 * (p / 10 ^ j % 10) +
        (2 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) =
        10 * (10 ^ j * ((2 * (p / 10 ^ j % 10) +
        (2 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) := by ring
    have e3 : 10 ^ j * (10 * ((2 * (p / 10 ^ j % 10) +
        (2 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) ≤
        10 ^ j * (2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) := by
      gcongr
    omega
  · have hYd : 2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j =
        10 * ((2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) / 10) +
        (2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) % 10 :=
      (Nat.div_add_mod _ _).symm
    have hY : (2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) % 10 ≤ 9 := by
      omega
    have e1 : ((2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) / 10 + 1) *
        (10 ^ j * 10) = 10 * (10 ^ j *
        ((2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) + 10 * 10 ^ j := by
      ring
    have e2 : 10 ^ j * (2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) =
        10 * (10 ^ j * ((2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) +
        10 ^ j * ((2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) % 10) := by
      conv_lhs => rw [hYd]
      ring
    have e3 : 10 ^ j * ((2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) % 10) ≤
        9 * 10 ^ j := by
      rw [mul_comm (10 ^ j) ((2 * (p / 10 ^ j % 10) + (2 * (p % 10 ^ j) + 1) / 10 ^ j) % 10)]
      gcongr
    omega

/-- `dgt` vanishes above the length. -/
theorem dgt_eq_zero_of_ge {p m j : ℕ} (h : p < 10 ^ m) (hj : m ≤ j) : dgt p j = 0 := by
  unfold dgt
  have : p < 10 ^ j := lt_of_lt_of_le h (pow_le_pow_right₀ (by norm_num) hj)
  rw [Nat.div_eq_of_lt this, Nat.zero_mod]

/-- Length of `2p+1` is `m` or `m+1`. -/
theorem mp_cases {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) m')
    (hm : 1 ≤ m) : m' = m ∨ m' = m + 1 := by
  have hphi := hp.hi
  have hplo := hp.lo
  have hqhi := hq.hi
  have hqlo := hq.lo
  have hup : 2 * p + 1 < 10 ^ (m + 1) := by
    calc 2 * p + 1 < 2 * 10 ^ m := by omega
      _ < 10 ^ (m + 1) := by rw [pow_succ']; omega
  have hlo : 10 ^ (m - 1) < 2 * p + 1 := by omega
  have h1 : m' - 1 < m + 1 := by
    by_contra h
    replace h := not_lt.mp h
    have : 10 ^ (m + 1) ≤ 10 ^ (m' - 1) := pow_le_pow_right₀ (by norm_num) h
    omega
  have h2 : m ≤ m' := by
    by_contra h
    replace h := not_le.mp h
    have : m' ≤ m - 1 := by omega
    have : 10 ^ m' ≤ 10 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) this
    omega
  omega

/-- `m' = m` iff the top carry vanishes. -/
theorem crry_m_eq_zero_iff {p m : ℕ} (hp : p < 10 ^ m) :
    crry p m = 0 ↔ 2 * p + 1 < 10 ^ m := by
  unfold crry
  rw [Nat.mod_eq_of_lt hp, Nat.div_eq_zero_iff,
      or_iff_right (pow_ne_zero _ (by norm_num) : (10 : ℕ) ^ m ≠ 0)]

/-- Carry symmetry, same-length case: `c_j = c_{m-1-j}` (the same digit
`a_j` on both sides, and carries are `< 10`). -/
theorem crry_sym_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) m)
    {j : ℕ} (hj : j < m) : crry p j = crry p (m - 1 - j) := by
  have e := hq.sym j (by omega)
  rw [qdgt, qdgt] at e
  have ha : dgt p (m - 1 - j) = dgt p j := (hp.sym j hj).symm
  rw [ha] at e
  have c1 := crry_le p j
  have c2 := crry_le p (m - 1 - j)
  omega

/-- Length+1 case: the mirrored carry `c_{m-j}` is the forward recurrence
of the same digit `a_j` (palindrome: `a_{m-j-1} = a_j`) - the second
determination of `a_j`. -/
theorem crry_mirror {p m : ℕ} (hp : IsPal p m)
    (hm : 1 ≤ m) (j : ℕ) (hj : j ≤ m - 1) :
    crry p (m - j) = (2 * dgt p j + crry p (m - j - 1)) / 10 := by
  have e := crry_succ p (m - j - 1)
  rw [show m - j - 1 + 1 = m - j by omega] at e
  have hpd : dgt p (m - j - 1) = dgt p j := by
    have h := hp.sym j (by omega : j < m)
    rw [show m - 1 - j = m - j - 1 by omega] at h
    exact h.symm
  rw [hpd] at e
  exact e

/-- Output symmetry, length+1 case, raw form:
`(2a_j + c_j) % 10 = (2a_{j-1} + c_{m-j}) % 10` for `1 ≤ j ≤ m-1`. -/
theorem qdgt_sym_succ {p m : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) (m + 1))
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ m - 1) :
    (2 * dgt p j + crry p j) % 10 = (2 * dgt p (j - 1) + crry p (m - j)) % 10 := by
  have e := hq.sym j (by omega)
  have hm_j : m + 1 - 1 - j = m - j := by omega
  rw [hm_j, qdgt, qdgt] at e
  have ha : dgt p (m - j) = dgt p (j - 1) := by
    have h := hp.sym (j - 1) (by omega)
    rw [show m - 1 - (j - 1) = m - j by omega] at h
    exact h.symm
  rw [ha] at e
  exact e

/-- Same-length case: 2-periodicity `c_{j+1} = c_{j-1}` for `1 ≤ j ≤ m-2`. -/
theorem carry_period_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) m)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ m - 2) :
    crry p (j + 1) = crry p (j - 1) := by
  have e1 := crry_succ p j
  have e2 := crry_succ p (m - 1 - j)
  have hidx : m - 1 - j + 1 = m - j := by omega
  rw [hidx] at e2
  have ha : dgt p (m - 1 - j) = dgt p j := (hp.sym j (by omega)).symm
  have hc : crry p (m - 1 - j) = crry p j :=
    (crry_sym_same hp hq (show j < m by omega)).symm
  rw [ha, hc] at e2
  have hsym : crry p (m - j) = crry p (j - 1) := by
    rw [show m - j = m - 1 - (j - 1) by omega]
    exact (crry_sym_same hp hq (j := j - 1) (by omega)).symm
  rw [hsym, ← e1] at e2
  exact e2.symm

/-- Same-length case: even-indexed carries equal `1`. -/
theorem carry_even_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) m) :
    ∀ k, 2 * k ≤ m - 1 → crry p (2 * k) = 1 := by
  intro k
  induction k with
  | zero => intro _; exact crry_zero p
  | succ k ih =>
    intro hk
    have hstep := carry_period_same hp hq (j := 2 * k + 1) (by omega) (by omega)
    have e1 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
    have e2 : 2 * k + 1 - 1 = 2 * k := by omega
    rw [e1, e2] at hstep
    rw [hstep, ih (by omega)]

/-- Same-length case: odd-indexed carries all equal `c_1`. -/
theorem carry_odd_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) m) :
    ∀ k, 2 * k + 1 ≤ m - 1 → crry p (2 * k + 1) = crry p 1 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hstep := carry_period_same hp hq (j := 2 * k + 2) (by omega) (by omega)
    have e1 : 2 * k + 2 + 1 = 2 * (k + 1) + 1 := by ring
    have e2 : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    rw [e1, e2] at hstep
    rw [hstep, ih (by omega)]

/-- Same-length case: `m` must be odd and `a_0 ∈ {1,2,3,4}`. -/
theorem same_case_odd_a0 {p m : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) m)
    (hm : 1 ≤ m) : Odd m ∧ 1 ≤ dgt p 0 ∧ dgt p 0 ≤ 4 := by
  have hcm0 : crry p m = 0 := by
    rw [crry_m_eq_zero_iff hp.hi]; exact hq.hi
  have htop : 1 ≤ dgt p (m - 1) := by
    have h1 : 1 ≤ p / 10 ^ (m - 1) := Nat.div_pos hp.lo (by positivity)
    have h2 : p / 10 ^ (m - 1) < 10 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity : (0:ℕ) < 10 ^ (m - 1))]
      have e : (10 : ℕ) ^ m = 10 * 10 ^ (m - 1) := by
        cases m with
        | zero => omega
        | succ k => rw [pow_succ, show k + 1 - 1 = k by omega]; ring
      have hphi := hp.hi
      omega
    unfold dgt
    omega
  have htop0 : dgt p 0 = dgt p (m - 1) := by
    have h := hp.sym 0 (by omega)
    rw [show m - 1 - 0 = m - 1 by omega] at h
    exact h
  by_cases hpar : m % 2 = 0
  · -- m even: derive contradiction
    obtain ⟨k, hk⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have csym := crry_sym_same hp hq (j := 0) (by omega)
    rw [show m - 1 - 0 = m - 1 by omega, crry_zero] at csym
    have codd := carry_odd_same hp hq (k - 1) (by omega)
    rw [show 2 * (k - 1) + 1 = m - 1 by omega] at codd
    have hc1 : crry p 1 = 1 := by rw [← csym] at codd; exact codd.symm
    have e1 : crry p 1 = (2 * dgt p 0 + 1) / 10 := by
      have e := crry_succ p 0
      rw [crry_zero] at e
      exact e
    have em := crry_succ p (m - 1)
    have hsym2 : crry p (m - 1) = 1 := csym.symm
    rw [show m - 1 + 1 = m by omega, ← htop0, hsym2] at em
    exfalso
    omega
  · -- m odd: a_0 ≤ 4
    refine ⟨Nat.odd_iff.mpr (by omega), ?_, ?_⟩
    · rw [htop0]; exact htop
    · have hmk : m - 1 = 2 * ((m - 1) / 2) := by omega
      have ceven := carry_even_same hp hq ((m - 1) / 2) (by omega)
      rw [← hmk] at ceven
      have em := crry_succ p (m - 1)
      rw [show m - 1 + 1 = m by omega, ← htop0, ceven, hcm0] at em
      omega

/-- Same-length case: digit classes `≤ 4` (even positions) / `≥ 5` (odd). -/
theorem same_case_digits {p m : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) m)
    (hm : 1 ≤ m) :
    (∀ j, j < m → j % 2 = 0 → dgt p j ≤ 4) ∧
    (∀ j, j < m → j % 2 = 1 → 5 ≤ dgt p j) := by
  obtain ⟨hmo, ha0lo, ha0hi⟩ := same_case_odd_a0 hp hq hm
  have hcm0 : crry p m = 0 := by
    rw [crry_m_eq_zero_iff hp.hi]; exact hq.hi
  have hc1 : crry p 1 = 0 := by
    have e : crry p 1 = (2 * dgt p 0 + 1) / 10 := by
      have e := crry_succ p 0
      rw [crry_zero] at e
      exact e
    omega
  refine ⟨?_, ?_⟩
  · intro j hj hev
    have cj : crry p j = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
      rw [hk]
      exact carry_even_same hp hq k (by omega)
    have e := crry_succ p j
    rw [cj] at e
    by_cases hjm : j + 1 ≤ m - 1
    · have cj1 : crry p (j + 1) = 0 := by
        have hje : j + 1 = 2 * (j / 2) + 1 := by omega
        rw [hje]
        rw [carry_odd_same hp hq (j / 2) (by omega)]
        exact hc1
      omega
    · have hjm2 : j + 1 = m := by omega
      rw [hjm2, hcm0] at e
      omega
  · intro j hj hod
    have cj : crry p j = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, j = 2 * k + 1 := ⟨(j - 1) / 2, by omega⟩
      rw [hk]
      rw [carry_odd_same hp hq k (by omega)]
      exact hc1
    have e := crry_succ p j
    rw [cj] at e
    have hjm : j + 1 ≤ m - 1 := by
      obtain ⟨t, ht⟩ := hmo
      omega
    have cj1 : crry p (j + 1) = 1 := by
      have hje : j + 1 = 2 * ((j + 1) / 2) := by omega
      rw [hje]
      exact carry_even_same hp hq ((j + 1) / 2) (by omega)
    rw [cj1] at e
    unfold dgt at e ⊢
    omega

/-- Length+1 case: the boundary forces `a_0 = 5` (and `c_m = 1`). -/
theorem succ_case_a0 {p m : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) (m + 1))
    (hm : 1 ≤ m) : dgt p 0 = 5 := by
  have hb := hq.sym 0 (by omega : 0 < m + 1)
  rw [show m + 1 - 1 - 0 = m by omega, qdgt, qdgt, crry_zero] at hb
  have hdm0 : dgt p m = 0 := dgt_eq_zero_of_ge hp.hi le_rfl
  rw [hdm0] at hb
  have hcm2 : crry p m ≤ 1 := crry_le p m
  have hb2 : (2 * dgt p 0 + 1) % 10 = crry p m := by omega
  have hdm : dgt (2 * p + 1) m = crry p m := by
    rw [qdgt, hdm0]
    omega
  have htcm : 1 ≤ crry p m := by
    have hlo : 10 ^ m ≤ 2 * p + 1 := by
      have := hq.lo
      rwa [show m + 1 - 1 = m by omega] at this
    have h1 : 1 ≤ (2 * p + 1) / 10 ^ m := Nat.div_pos hlo (by positivity)
    have h2 : (2 * p + 1) / 10 ^ m < 10 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      have e : (10 : ℕ) ^ (m + 1) = 10 ^ m * 10 := by rw [pow_succ]
      have hqhi := hq.hi
      omega
    rw [← hdm]
    unfold dgt
    omega
  have htop : 1 ≤ dgt p 0 := by
    have h1 : 1 ≤ p / 10 ^ (m - 1) := Nat.div_pos hp.lo (by positivity)
    have h2 : p / 10 ^ (m - 1) < 10 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity : (0:ℕ) < 10 ^ (m - 1))]
      have e : (10 : ℕ) ^ m = 10 * 10 ^ (m - 1) := by
        rw [← pow_succ', show m - 1 + 1 = m by omega]
      have hphi := hp.hi
      omega
    have hd : dgt p (m - 1) = p / 10 ^ (m - 1) := by unfold dgt; omega
    have h := hp.sym 0 (by omega : 0 < m)
    rw [show m - 1 - 0 = m - 1 by omega] at h
    omega
  have hcm1 : crry p (m - 1) ≤ 1 := crry_le p _
  have ec := crry_succ p (m - 1)
  rw [show m - 1 + 1 = m by omega] at ec
  have ham1 : dgt p (m - 1) = dgt p 0 := by
    have h := hp.sym 0 (by omega : 0 < m)
    rw [show m - 1 - 0 = m - 1 by omega] at h
    exact h.symm
  rw [ham1] at ec
  have h91 : dgt p 0 ≤ 9 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  interval_cases dgt p 0 <;> omega

/-- Length+1 case: fully rigid chain `(a_j, c_{j+1}) = (5, 1)` for ALL
`j ≤ m-1`. The mirror carry is forced to `1` by parity (`2a'+1` is odd),
then `eB` forces `a' ≥ 5` while `eA` gives `a' ∈ {0,5}` - one-step
forcing, no dead-end lookahead needed. -/
theorem succ_case_chain {p m : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) (m + 1))
    (hm : 1 ≤ m) : ∀ j, j ≤ m - 1 → dgt p j = 5 ∧ crry p (j + 1) = 1 := by
  have ha0 := succ_case_a0 hp hq hm
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨ha0, ?_⟩
    have e : crry p 1 = (2 * dgt p 0 + 1) / 10 := by
      have e := crry_succ p 0
      rw [crry_zero] at e
      exact e
    rw [ha0] at e
    omega
  | succ j ih =>
    intro hj
    obtain ⟨haj, hcj⟩ := ih (by omega)
    -- (A): `(2·a_{j+1} + 1) % 10 = (10 + c_{m-j-1}) % 10`
    have eA := qdgt_sym_succ hp hq (j := j + 1) (by omega) (by omega)
    rw [show j + 1 - 1 = j by omega, haj, hcj] at eA
    -- (B): `c_{m-j-1} = (2·a_{j+1} + c_{m-j-2}) / 10`
    have eB := crry_mirror hp hm (j + 1) (by omega)
    have e2 := crry_succ p (j + 1)
    rw [hcj] at e2
    have hr : crry p (m - (j + 1)) ≤ 1 := crry_le p _
    have hr2 : crry p (m - (j + 1) - 1) ≤ 1 := crry_le p _
    have ha9 : dgt p (j + 1) ≤ 9 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    -- step 1: parity - `2a'+1` odd forces `r = 1`
    have hr1 : crry p (m - (j + 1)) = 1 := by
      clear eB e2 hr2 ha9
      omega
    -- step 2: `a' = 5` (from `a' ∈ {0,5}` and `a' ≥ 5`)
    have ha' : dgt p (j + 1) = 5 := by
      clear e2
      omega
    -- step 3: `c_{j+2} = (2·5+1)/10 = 1`
    have hc' : crry p (j + 1 + 1) = 1 := by
      clear eA eB hr hr2 ha9
      omega
    exact ⟨ha', hc'⟩

/-- Length+1 case: every digit is `5`. -/
theorem succ_case_all5 {p m : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) (m + 1))
    (hm : 1 ≤ m) : ∀ j < m, dgt p j = 5 := by
  intro j hj
  exact (succ_case_chain hp hq hm j (by omega)).1

/-- **A069881 classification, part 1 (Tangente's conjecture)**: for `m`
even, every digit of `p` is `5` (`p = 55...5`). -/
theorem A069881_even {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) m')
    (hm : 1 ≤ m) (hme : m % 2 = 0) : ∀ j < m, dgt p j = 5 := by
  rcases mp_cases hp hq hm with h | h
  · subst h
    obtain ⟨hodd, _, _⟩ := same_case_odd_a0 hp hq hm
    rw [Nat.odd_iff] at hodd
    omega
  · subst h
    exact succ_case_all5 hp hq hm

/-- **A069881 classification, part 2**: the overflow terms are exactly
the repdigits - `2p+1` has `m+1` digits iff every digit of `p` is `5`. -/
theorem A069881_overflow {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) m')
    (hm : 1 ≤ m) :
    (∀ j < m, dgt p j = 5) ∨
      (Odd m ∧ 1 ≤ dgt p 0 ∧ dgt p 0 ≤ 4 ∧
        (∀ j, j < m → j % 2 = 0 → dgt p j ≤ 4) ∧
        (∀ j, j < m → j % 2 = 1 → 5 ≤ dgt p j)) := by
  rcases mp_cases hp hq hm with h | h
  · subst h
    obtain ⟨hmo, ha0lo, ha0hi⟩ := same_case_odd_a0 hp hq hm
    obtain ⟨d1, d2⟩ := same_case_digits hp hq hm
    exact Or.inr ⟨hmo, ha0lo, ha0hi, d1, d2⟩
  · subst h
    exact Or.inl (succ_case_all5 hp hq hm)

/-- Bonus (image parity): the digits of `q = 2p+1` at even positions are
all odd (`b_j = (2a_j + 1) % 10` for the same-length case, all `1`s for
the repdigit case). -/
theorem A069881_image_odd {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (2 * p + 1) m')
    (hm : 1 ≤ m) : ∀ j < m', j % 2 = 0 → dgt (2 * p + 1) j % 2 = 1 := by
  intro j hj hev
  rcases mp_cases hp hq hm with h | h
  · subst h
    obtain ⟨d1, d2⟩ := same_case_digits hp hq hm
    obtain ⟨k, hk⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
    have cj : crry p j = 1 := by
      rw [hk]; exact carry_even_same hp hq k (by omega)
    have haj : dgt p j ≤ 4 := d1 j hj hev
    rw [qdgt, cj]
    omega
  · subst h
    have ha0 := succ_case_a0 hp hq hm
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [qdgt, hj0, crry_zero, ha0]
    · by_cases hjm : j = m
      · rw [qdgt, hjm, show dgt p m = 0 from dgt_eq_zero_of_ge hp.hi le_rfl]
        have hcm : crry p m = 1 := by
          have hb := hq.sym 0 (by omega : 0 < m + 1)
          rw [show m + 1 - 1 - 0 = m by omega, qdgt, qdgt, crry_zero,
              show dgt p m = 0 from dgt_eq_zero_of_ge hp.hi le_rfl] at hb
          have hcm2 : crry p m ≤ 1 := crry_le p m
          omega
        rw [hcm]
      · have hcj : crry p j = 1 := by
          have e := (succ_case_chain hp hq hm (j - 1) (by omega)).2
          rwa [show j - 1 + 1 = j by omega] at e
        have haj : dgt p j = 5 := succ_case_all5 hp hq hm j (by omega)
        rw [qdgt, haj, hcj]

/-- Backward direction, same-length branch: an odd-length palindrome
with alternating digit classes `a_j ≤ 4` (even positions) / `a_j ≥ 5`
(odd positions) gives a palindrome `2p+1` of length `m`. -/
theorem alt_gives_pal {p m : ℕ} (hp : IsPal p m) (_hm : 1 ≤ m)
    (hodd : m % 2 = 1)
    (hev : ∀ j, j < m → j % 2 = 0 → dgt p j ≤ 4)
    (hod : ∀ j, j < m → j % 2 = 1 → 5 ≤ dgt p j) :
    IsPal (2 * p + 1) m := by
  -- alternating carry chain: c_j = 1 (j even), c_j = 0 (j odd), j ≤ m
  have hcar : ∀ j, j ≤ m →
      (j % 2 = 0 → crry p j = 1) ∧ (j % 2 = 1 → crry p j = 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨fun _ => crry_zero p, fun h => by omega⟩
    | succ j ih =>
      intro hjm
      obtain ⟨ih0, ih1⟩ := ih (by omega)
      have e := crry_succ p j
      by_cases hjp : j % 2 = 0
      · rw [ih0 hjp] at e
        have haj := hev j (by omega) hjp
        exact ⟨fun h => by omega, fun _ => by omega⟩
      · have hjp' : j % 2 = 1 := by omega
        rw [ih1 hjp'] at e
        have haj := hod j (by omega) hjp'
        have h9 : dgt p j < 10 := by
          unfold dgt
          exact Nat.mod_lt _ (by positivity)
        exact ⟨fun _ => by omega, fun h => by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · -- sym: ∀ j < m, q_j = q_{m-1-j} (same-parity carries)
    intro j hj
    rw [qdgt, qdgt]
    have ha : dgt p (m - 1 - j) = dgt p j := (hp.sym j hj).symm
    rw [ha]
    have hceq : crry p (m - 1 - j) = crry p j := by
      have hpar : (m - 1 - j) % 2 = j % 2 := by omega
      by_cases hjp : j % 2 = 0
      · have h1 := (hcar j (by omega)).1 hjp
        have h2 := (hcar (m - 1 - j) (by omega)).1 (by omega)
        omega
      · have hjp' : j % 2 = 1 := by omega
        have h1 := (hcar j (by omega)).2 hjp'
        have h2 := (hcar (m - 1 - j) (by omega)).2 (by omega)
        omega
    rw [hceq]
  · -- lo: 10^{m-1} ≤ 2p+1
    have hplo := hp.lo
    omega
  · -- hi: 2p+1 < 10^m via c_m = 0
    have hcm : crry p m = 0 := (hcar m le_rfl).2 hodd
    exact (crry_m_eq_zero_iff hp.hi).mp hcm

end A069881
