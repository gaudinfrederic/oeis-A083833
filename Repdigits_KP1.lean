/-
COMPILE-CHECKED -- Repdigits_KP1.lean (canonical iff module)

STATUS: kernel-verified remotely, three times on the
self-hosted VPS (workflow lean-run-vps.yml, cache tag
repdig-iff):
* run 44730959646: identical file compiled as
  `Check_repdigits_iff.lean` via `lake env lean`, LEAN_EXIT=0;
* run 44731366320: this file built in place as a lean_lib via
  `lake build Repdigits_KP1`, LEAN_EXIT=0 (9052 jobs);
* run 44731969710: same build, current content including the
  `repdigitN_iff_member_even_AXXXXX` headline iffs,
  LEAN_EXIT=0.
Axiom audit, printed inside the file:
  repdigit_mem, repdigit5_iff_overflow_A069881,
  repdigit7_iff_overflow_A083829,
  repdigit8_iff_overflow_A083831,
  repdigit2_iff_overflow_A083833,
  repdigit5_iff_member_even_A069881,
  repdigit7_iff_member_even_A083829,
  repdigit8_iff_member_even_A083831,
  repdigit2_iff_member_even_A083833
all depend only on [propext, Classical.choice, Quot.sound] -
the standard Mathlib trio, no sorryAx, no native_decide.
(Failed probe: run 44730514142, a `generalizing`/`intro`
mismatch in `eq_sum_dgt`, fixed in v2.)

This module does TWO things:

1. The repdigit converse, detached: for every `m >= 1` the
   repdigit `d_k * R_m` (digits 5,7,8,2 for multipliers
   k = 2,3,4,5) is a member of `S_k` with overflow image
   (`k*p+1` on `m+1` digits). Proved once in this file's own
   `IsPal`/`IsMember` vocabulary - the same theorems as the
   verified `repdigits-sketch.lean` draft.

2. CANONICAL UNIFICATION (the point of this module): the four
   artifacts `A069881/A083829/A083831/A083833` are imported, and
   each repdigit theorem is restated against the ARTIFACT's OWN
   `IsPal`/`dgt` - which elaborate as definitionally equal to the
   local ones (probed by `rfl` examples below). For each k the
   module proves a LITERAL `Iff` on the overflow branch
   `m' = m + 1` - the exact hypothesis pair every artifact
   classification theorem quantifies over - plus the membership
   direction inside artifact vocabulary:

     (AXXXXX.IsPal p m /\ AXXXXX.IsPal (k*p+1) (m+1)) <->
       p = repdigit d m

   and the headline iff for even-length members (no constraint
   on `m'`, forward via the artifact's `_even`/`_C2`
   classification):

     (exists m', AXXXXX.IsPal p m /\ AXXXXX.IsPal (k*p+1) m') <->
       p = repdigit d m        [for m even, 1 <= m]

   Forward direction: the artifact's own `succ_case_allN`
   (all digits equal d) or `_even`/`_C2` composed with
   `eq_sum_dgt` (digit reconstruction
   p = sum dgt p j * 10^j). Backward: the detached
   repdigit-palindrome proofs transported through
   `isPal_to_AXXXXX` bridges.

Prior runs (detached body): baseline 44709195515, candidates
44715758098/44717823639 (failed), 44718583159 + 44719094015
(pass). Unification verdict: UNIFIED by definitional equality,
not merely fieldwise-identical text.

Scope (only the direction still missing). The artifacts prove
"member => structure": in the overflow branch m' = m+1 every
digit of p equals d_k, and even m forces that branch:
  k = 2 (lean/A069881.lean): all digits 5
        (A069881_even, succ_case_all5)
  k = 3 (lean/A083829.lean): all digits 7
        (A083829_even, succ_case_all7)
  k = 4 (lean/A083831.lean): all digits 8
        (A083831_even, succ_case_all8)
  k = 5 (12-PUBLIES-SCELLES/A083833/lean-artifact/A083833.lean):
        all digits 2 (A083833_C2, succ_case_all2)
This file proves the converse "repdigit => member": for
every length m >= 1 the repdigit p = d_k * R_m is a member,
with k*p+1 of length m+1. Repdigit/multiplier mapping (verified
against the artifacts, not taken from the referee's word):
  k = 2 -> d = 5: 2*(55..5)+1 = 11..1     (repunit R_{m+1})
  k = 3 -> d = 7: 3*(77..7)+1 = 2 33..3 2 (2*R_{m+1}+10*R_{m-1})
  k = 4 -> d = 8: 4*(88..8)+1 = 3 55..5 3 (3*R_{m+1}+20*R_{m-1})
  k = 5 -> d = 2: 5*(22..2)+1 = 11..1     (repunit R_{m+1})
Head-equation check: k*d_k + 1 = 11*v_k gives
  2*5+1 = 11, 3*7+1 = 22, 4*8+1 = 33, 5*2+1 = 11.

NOTE on namespaces: each artifact ships its own textually
identical `dgt`/`IsPal`; they are cloned here once, so each
membership theorem drops into its artifact's namespace verbatim
(up to the namespace prefix).
-/

import Mathlib
import A069881
import A083829
import A083831
import A083833

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Repdigit converses for the kp+1 palindrome sequences

Only the missing direction is stated here (see file header).
The module imports the four canonical artifacts and proves the
converse against THEIR OWN `IsPal` predicates: literal `Iff`
statements for the overflow branch `m' = m + 1`, plus the
membership direction `repdigit d m -> exists m', IsPal p m and
IsPal (k*p+1) m'` inside each artifact namespace's vocabulary.
-/

namespace Kp1Repdigits

/-- The `j`-th decimal digit of `n` (units = `j = 0`).
Identical to `dgt` in all four artifacts. -/
def dgt (n j : Nat) : Nat := n / 10 ^ j % 10

/-- `p` has `m`-digit palindromic decimal expansion: symmetric
digits, `10^(m-1) <= p < 10^m`. Identical to `IsPal` in all four
artifacts. -/
structure IsPal (p m : Nat) : Prop where
  sym : forall j, j < m -> dgt p j = dgt p (m - 1 - j)
  lo : 10 ^ (m - 1) <= p
  hi : p < 10 ^ m

/-- Membership predicate, the convention of the `Check_*` audit
modules: `p` and `k*p+1` are both palindromes (`m >= 1`). -/
def IsMember (k p : Nat) : Prop :=
  exists m m', 1 <= m /\ IsPal p m /\ IsPal (k * p + 1) m'

/-- The `m`-digit repunit `11..1 = (10^m - 1)/9`
(`repunit 0 = 0`). -/
def repunit (m : Nat) : Nat := (10 ^ m - 1) / 9

/-- The `m`-digit repdigit `dd..d = d * repunit m`. -/
def repdigit (d m : Nat) : Nat := d * repunit m

/-! ## Repunit / repdigit arithmetic -/

/-- `9` divides `10^m - 1` (the repunit numerator). -/
theorem nine_dvd_pow10 (m : Nat) : 9 ∣ 10 ^ m - 1 := by
  induction m with
  | zero => exact ⟨0, by norm_num⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    have h1 : 1 ≤ 10 ^ m := Nat.one_le_pow m 10 (by norm_num)
    refine ⟨10 ^ m + c, ?_⟩
    rw [pow_succ]
    omega

/-- Integral repunit identity: `9 * repunit m = 10^m - 1`. -/
theorem repunit_eq (m : Nat) : 10 ^ m - 1 = 9 * repunit m := by
  have h := Nat.div_mul_cancel (nine_dvd_pow10 m)
  unfold repunit
  omega

theorem repunit_succ (m : Nat) :
    repunit (m + 1) = 10 * repunit m + 1 := by
  unfold repunit
  rw [pow_succ]
  have h := Nat.div_mul_cancel (nine_dvd_pow10 (m + 1))
  have h0 := Nat.div_mul_cancel (nine_dvd_pow10 m)
  have hT : 1 ≤ 10 ^ m := Nat.one_le_pow m 10 (by norm_num)
  rw [pow_succ] at h
  omega

theorem repdigit_succ (d m : Nat) :
    repdigit d (m + 1) = 10 * repdigit d m + d := by
  unfold repdigit
  rw [repunit_succ]
  ring

/-- Geometric sum: `9 * (1 + 10 + ... + 10^(m-1)) = 10^m - 1`. -/
theorem geom10 (m : Nat) :
    9 * Finset.sum (Finset.range m) (fun i => 10 ^ i) =
      10 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Finset.sum_range_succ, pow_succ]
    have h1 : 1 ≤ 10 ^ m := Nat.one_le_pow m 10 (by norm_num)
    omega

/-- A repunit is the digit expansion `sum_{i<m} 10^i`. -/
theorem repunit_eq_sum (m : Nat) :
    repunit m = Finset.sum (Finset.range m) (fun i => 10 ^ i) := by
  have e1 := repunit_eq m
  have e2 := geom10 m
  omega

/-- A repdigit is the explicit digit expansion
`sum_{j<m} d * 10^j`. -/
theorem repdigit_eq_sum (d m : Nat) :
    repdigit d m =
      Finset.sum (Finset.range m) (fun i => d * 10 ^ i) := by
  unfold repdigit
  rw [repunit_eq_sum, Finset.mul_sum]

/-- A digit expansion on `m` positions stays below `10^m`
(each coefficient `<= 9`, no carry). -/
theorem digit_sum_lt {a : Nat → Nat} {m : Nat}
    (ha : forall i, i < m -> a i <= 9) :
    Finset.sum (Finset.range m) (fun i => a i * 10 ^ i) <
      10 ^ m := by
  revert ha
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro ha
    simp only [Finset.sum_range_succ]
    have hih := ih (fun i hi => ha i (by omega))
    have h1 : 1 ≤ 10 ^ m := Nat.one_le_pow m 10 (by norm_num)
    have ham : a m * 10 ^ m ≤ 9 * 10 ^ m :=
      Nat.mul_le_mul (ha m (by omega)) (le_refl _)
    rw [pow_succ]
    omega

/-- Digits of an explicit digit expansion: coefficients `<= 9`
are read off position by position (no carries). -/
theorem dgt_digit_sum {a : Nat → Nat} {m : Nat}
    (ha : forall i, i < m -> a i <= 9) :
    forall j, j < m ->
      dgt (Finset.sum (Finset.range m) (fun i => a i * 10 ^ i)) j =
        a j := by
  revert ha
  induction m with
  | zero => intro _ j hj; omega
  | succ m ih =>
    intro ha j hj
    simp only [Finset.sum_range_succ]
    by_cases hjm : j = m
    · subst j
      unfold dgt
      rw [Nat.add_mul_div_right _ _ (by positivity : (0:Nat) < 10 ^ m)]
      rw [Nat.div_eq_of_lt
        (digit_sum_lt (fun i hi => ha i (by omega)))]
      rw [zero_add]
      exact Nat.mod_eq_of_lt (by have h9 := ha m (by omega); omega)
    · have hjm' : j < m := by omega
      have hexp : a m * 10 ^ m = (a m * 10 ^ (m - j)) * 10 ^ j := by
        have e : m - j + j = m := Nat.sub_add_cancel (by omega)
        calc a m * 10 ^ m = a m * 10 ^ (m - j + j) := by rw [e]
          _ = a m * (10 ^ (m - j) * 10 ^ j) := by rw [pow_add]
          _ = (a m * 10 ^ (m - j)) * 10 ^ j := by ring
      unfold dgt
      rw [hexp,
        Nat.add_mul_div_right _ _ (by positivity : (0:Nat) < 10 ^ j)]
      have hmj : m - j - 1 + 1 = m - j :=
        Nat.sub_add_cancel (by omega)
      have e2 : a m * 10 ^ (m - j) =
          (a m * 10 ^ (m - j - 1)) * 10 := by
        calc a m * 10 ^ (m - j) = a m * 10 ^ (m - j - 1 + 1) := by
              rw [hmj]
          _ = a m * (10 ^ (m - j - 1) * 10) := by rw [pow_succ]
          _ = (a m * 10 ^ (m - j - 1)) * 10 := by ring
      rw [e2, Nat.add_mul_mod_self_right]
      exact ih (fun i hi => ha i (by omega)) j hjm'

theorem dgt_repdigit {d m : Nat} (hd : d <= 9) :
    forall j, j < m -> dgt (repdigit d m) j = d := by
  intro j hj
  rw [repdigit_eq_sum]
  exact dgt_digit_sum (a := fun _ => d) (fun i _ => hd) j hj

theorem repunit_lo {m : Nat} (hm : 1 <= m) :
    10 ^ (m - 1) <= repunit m := by
  rw [repunit_eq_sum]
  exact Finset.single_le_sum (f := fun i => 10 ^ i)
    (fun i _ => Nat.zero_le _)
    (Finset.mem_range.mpr (show m - 1 < m by omega))

theorem repunit_hi (m : Nat) : repunit m < 10 ^ m := by
  have h1 : 1 ≤ 10 ^ m := Nat.one_le_pow m 10 (by norm_num)
  calc repunit m = (10 ^ m - 1) / 9 := rfl
    _ ≤ 10 ^ m - 1 := Nat.div_le_self _ _
    _ < 10 ^ m := by omega

theorem repdigit_lo {d m : Nat} (hd0 : 1 <= d) (hd9 : d <= 9)
    (hm : 1 <= m) : 10 ^ (m - 1) <= repdigit d m := by
  calc 10 ^ (m - 1) ≤ repunit m := repunit_lo hm
    _ = 1 * repunit m := (one_mul _).symm
    _ ≤ d * repunit m := Nat.mul_le_mul hd0 (le_refl _)
    _ = repdigit d m := rfl

/-- Leading term bound: a repdigit dominates its leading
contribution `d * 10^(m-1)`. -/
theorem repdigit_ge_lead {d m : Nat} (hm : 1 <= m) :
    d * 10 ^ (m - 1) <= repdigit d m := by
  rw [repdigit_eq_sum]
  exact Finset.single_le_sum (f := fun i => d * 10 ^ i)
    (fun i _ => Nat.zero_le _)
    (Finset.mem_range.mpr (show m - 1 < m by omega))

theorem repdigit_hi {d m : Nat} (hd9 : d <= 9) :
    repdigit d m < 10 ^ m := by
  have e := repunit_eq m
  have h1 : 1 ≤ 10 ^ m := Nat.one_le_pow m 10 (by norm_num)
  have hle : repdigit d m ≤ 9 * repunit m :=
    Nat.mul_le_mul hd9 (le_refl _)
  omega

/-- A repdigit `d*R_m` with `1 <= d <= 9` is an `m`-digit
palindrome. -/
theorem isPal_repdigit {d m : Nat} (hd0 : 1 <= d) (hd9 : d <= 9)
    (hm : 1 <= m) : IsPal (repdigit d m) m := by
  exact ⟨fun j hj => by
      rw [dgt_repdigit hd9 j hj,
        dgt_repdigit hd9 (m - 1 - j) (by omega)],
    repdigit_lo hd0 hd9 hm, repdigit_hi hd9⟩

theorem isPal_repunit {m : Nat} (hm : 1 <= m) :
    IsPal (repunit m) m := by
  simpa [repdigit] using
    (isPal_repdigit (d := 1) (m := m) (by norm_num) (by norm_num) hm)

/-! ## Closed forms of the images `k * (d_k * R_m) + 1` -/

/-- `k = 2`: `2*(55..5)+1 = 10*R_m + 1 = R_{m+1}` (repunit). -/
theorem two_mul_repdigit5 (m : Nat) :
    2 * repdigit 5 m + 1 = repunit (m + 1) := by
  rw [repunit_succ]
  unfold repdigit
  ring

/-- `k = 5`: `5*(22..2)+1 = 10*R_m + 1 = R_{m+1}` (repunit). -/
theorem five_mul_repdigit2 (m : Nat) :
    5 * repdigit 2 m + 1 = repunit (m + 1) := by
  rw [repunit_succ]
  unfold repdigit
  ring

/-- `k = 3`: `3*(77..7)+1 = 2*R_{m+1} + 10*R_{m-1}`, i.e. the
digits `2`, then `m-1` times `3`, then `2` (verified `m <= 7`). -/
theorem three_mul_repdigit7 {m : Nat} (hm : 1 <= m) :
    3 * repdigit 7 m + 1 =
      2 * repunit (m + 1) + 10 * repunit (m - 1) := by
  have h1 : repunit (m + 1) = 10 * repunit m + 1 := repunit_succ m
  have h2 : repunit m = 10 * repunit (m - 1) + 1 := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    exact repunit_succ (m - 1)
  unfold repdigit
  omega

/-- `k = 4`: `4*(88..8)+1 = 3*R_{m+1} + 20*R_{m-1}`, i.e. the
digits `3`, then `m-1` times `5`, then `3` (verified `m <= 7`). -/
theorem four_mul_repdigit8 {m : Nat} (hm : 1 <= m) :
    4 * repdigit 8 m + 1 =
      3 * repunit (m + 1) + 20 * repunit (m - 1) := by
  have h1 : repunit (m + 1) = 10 * repunit m + 1 := repunit_succ m
  have h2 : repunit m = 10 * repunit (m - 1) + 1 := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    exact repunit_succ (m - 1)
  unfold repdigit
  omega

/-- Sum of `v` at the interior positions `1..m-1`:
`sum_{1<=j<=m-1} v * 10^j = v * 10 * R_{m-1}` (packaged as a
boundary-zero digit expansion on `range (m+1)`). -/
theorem boundary_sum {v : Nat} {m : Nat} (hm : 1 <= m) :
    Finset.sum (Finset.range (m + 1))
      (fun j => (if j = 0 then 0 else if j = m then 0 else v)
        * 10 ^ j) =
      v * (10 * repunit (m - 1)) := by
  have hIco : Finset.Ico 1 m ⊆ Finset.range (m + 1) := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    rw [Finset.mem_range]
    omega
  have h1 : Finset.sum (Finset.range (m + 1))
      (fun j => (if j = 0 then 0 else if j = m then 0 else v)
        * 10 ^ j) =
      Finset.sum (Finset.Ico 1 m)
        (fun j => (if j = 0 then 0 else if j = m then 0 else v)
          * 10 ^ j) := by
    symm
    apply Finset.sum_subset hIco
    intro j hj1 hj2
    rw [Finset.mem_range] at hj1
    rw [Finset.mem_Ico] at hj2
    have hjm : j = 0 ∨ j = m := by omega
    rcases hjm with rfl | rfl <;> simp
  rw [h1]
  have h2 : forall j, j ∈ Finset.Ico 1 m ->
      (if j = 0 then 0 else if j = m then 0 else v) * 10 ^ j =
        v * 10 ^ j := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    split_ifs <;> omega
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range, repunit_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_comm 1 i, pow_succ]
  ring

/-- The `k = 3` image as a digit expansion: `2` at both ends,
`3` inside (positions `0 <= j <= m`). -/
theorem three_mul_repdigit7_sum {m : Nat} (hm : 1 <= m) :
    3 * repdigit 7 m + 1 =
      Finset.sum (Finset.range (m + 1))
        (fun j => (if j = 0 then 2 else if j = m then 2 else 3)
          * 10 ^ j) := by
  rw [three_mul_repdigit7 hm]
  have hA : 2 * repunit (m + 1) =
      Finset.sum (Finset.range (m + 1)) (fun j => 2 * 10 ^ j) := by
    have h := repdigit_eq_sum 2 (m + 1)
    unfold repdigit at h
    exact h
  have hB : 10 * repunit (m - 1) =
      Finset.sum (Finset.range (m + 1))
        (fun j => (if j = 0 then 0 else if j = m then 0 else 1)
          * 10 ^ j) := by
    have h := boundary_sum (v := 1) hm
    simpa using h.symm
  rw [hA, hB, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

/-- The `k = 4` image as a digit expansion: `3` at both ends,
`5` inside (positions `0 <= j <= m`). -/
theorem four_mul_repdigit8_sum {m : Nat} (hm : 1 <= m) :
    4 * repdigit 8 m + 1 =
      Finset.sum (Finset.range (m + 1))
        (fun j => (if j = 0 then 3 else if j = m then 3 else 5)
          * 10 ^ j) := by
  rw [four_mul_repdigit8 hm]
  have hA : 3 * repunit (m + 1) =
      Finset.sum (Finset.range (m + 1)) (fun j => 3 * 10 ^ j) := by
    have h := repdigit_eq_sum 3 (m + 1)
    unfold repdigit at h
    exact h
  have hB : 20 * repunit (m - 1) =
      Finset.sum (Finset.range (m + 1))
        (fun j => (if j = 0 then 0 else if j = m then 0 else 2)
          * 10 ^ j) := by
    have h := boundary_sum (v := 2) hm
    have e : 20 * repunit (m - 1) = 2 * (10 * repunit (m - 1)) :=
      by ring
    rw [e]
    exact h.symm
  rw [hA, hB, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

/-- Digit profile of `3*(77..7)+1`: `2` at both ends, `3`
inside (positions `0 <= j <= m`). -/
theorem dgt_three_mul_repdigit7 {m : Nat} (hm : 1 <= m) :
    forall j, j <= m ->
      dgt (3 * repdigit 7 m + 1) j =
        (if j = 0 then 2 else if j = m then 2 else 3) := by
  intro j hj
  rw [three_mul_repdigit7_sum hm]
  exact dgt_digit_sum
    (a := fun j => if j = 0 then 2 else if j = m then 2 else 3)
    (m := m + 1) (fun i _ => by split_ifs <;> norm_num) j (by omega)

/-- Digit profile of `4*(88..8)+1`: `3` at both ends, `5`
inside (positions `0 <= j <= m`). -/
theorem dgt_four_mul_repdigit8 {m : Nat} (hm : 1 <= m) :
    forall j, j <= m ->
      dgt (4 * repdigit 8 m + 1) j =
        (if j = 0 then 3 else if j = m then 3 else 5) := by
  intro j hj
  rw [four_mul_repdigit8_sum hm]
  exact dgt_digit_sum
    (a := fun j => if j = 0 then 3 else if j = m then 3 else 5)
    (m := m + 1) (fun i _ => by split_ifs <;> norm_num) j (by omega)

/-- `k = 3` image is an `(m+1)`-digit palindrome. -/
theorem isPal_three_mul_repdigit7 {m : Nat} (hm : 1 <= m) :
    IsPal (3 * repdigit 7 m + 1) (m + 1) := by
  have hlead : 7 * 10 ^ (m - 1) ≤ repdigit 7 m :=
    repdigit_ge_lead hm
  have hhi : repdigit 7 m < 10 ^ m := repdigit_hi (by norm_num)
  have hpm : 10 ^ m = 10 * 10 ^ (m - 1) := by
    have e : m - 1 + 1 = m := Nat.sub_add_cancel hm
    calc 10 ^ m = 10 ^ (m - 1 + 1) := by rw [e]
      _ = 10 ^ (m - 1) * 10 := pow_succ _ _
      _ = 10 * 10 ^ (m - 1) := mul_comm _ _
  have hp : 10 ^ (m + 1) = 10 * 10 ^ m := by rw [pow_succ, mul_comm]
  have hX : 1 ≤ 10 ^ (m - 1) := Nat.one_le_pow _ 10 (by norm_num)
  have hT : 1 ≤ 10 ^ m := Nat.one_le_pow m 10 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have e : m + 1 - 1 - j = m - j := by omega
    rw [e, dgt_three_mul_repdigit7 hm j (by omega),
      dgt_three_mul_repdigit7 hm (m - j) (by omega)]
    show (if j = 0 then 2 else if j = m then 2 else 3) =
      (if m - j = 0 then 2 else if m - j = m then 2 else 3)
    split_ifs <;> omega
  · rw [Nat.add_sub_cancel, hpm]
    omega
  · rw [hp]
    omega

/-- `k = 4` image is an `(m+1)`-digit palindrome. -/
theorem isPal_four_mul_repdigit8 {m : Nat} (hm : 1 <= m) :
    IsPal (4 * repdigit 8 m + 1) (m + 1) := by
  have hlead : 8 * 10 ^ (m - 1) ≤ repdigit 8 m :=
    repdigit_ge_lead hm
  have hhi : repdigit 8 m < 10 ^ m := repdigit_hi (by norm_num)
  have hpm : 10 ^ m = 10 * 10 ^ (m - 1) := by
    have e : m - 1 + 1 = m := Nat.sub_add_cancel hm
    calc 10 ^ m = 10 ^ (m - 1 + 1) := by rw [e]
      _ = 10 ^ (m - 1) * 10 := pow_succ _ _
      _ = 10 * 10 ^ (m - 1) := mul_comm _ _
  have hp : 10 ^ (m + 1) = 10 * 10 ^ m := by rw [pow_succ, mul_comm]
  have hX : 1 ≤ 10 ^ (m - 1) := Nat.one_le_pow _ 10 (by norm_num)
  have hT : 1 ≤ 10 ^ m := Nat.one_le_pow m 10 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have e : m + 1 - 1 - j = m - j := by omega
    rw [e, dgt_four_mul_repdigit8 hm j (by omega),
      dgt_four_mul_repdigit8 hm (m - j) (by omega)]
    show (if j = 0 then 3 else if j = m then 3 else 5) =
      (if m - j = 0 then 3 else if m - j = m then 3 else 5)
    split_ifs <;> omega
  · rw [Nat.add_sub_cancel, hpm]
    omega
  · rw [hp]
    omega

/-! ## The four converse theorems (the missing direction) -/

/-- `k = 2`, OEIS A069881: every repdigit `55..5` is a member;
its image `2*p+1` is the repunit `R_{m+1}`. -/
theorem mem_A069881_repdigit5 {m : Nat} (hm : 1 <= m) :
    IsMember 2 (repdigit 5 m) :=
  Exists.intro m (Exists.intro (m + 1)
    (And.intro hm
      (And.intro
        (isPal_repdigit (by norm_num) (by norm_num) hm)
        (by rw [two_mul_repdigit5]; exact isPal_repunit (by omega)))))

/-- `k = 3`, OEIS A083829: every repdigit `77..7` is a member;
its image `3*p+1` is `2 33..3 2` on `m+1` digits. -/
theorem mem_A083829_repdigit7 {m : Nat} (hm : 1 <= m) :
    IsMember 3 (repdigit 7 m) :=
  Exists.intro m (Exists.intro (m + 1)
    (And.intro hm
      (And.intro
        (isPal_repdigit (by norm_num) (by norm_num) hm)
        (isPal_three_mul_repdigit7 hm))))

/-- `k = 4`, OEIS A083831: every repdigit `88..8` is a member;
its image `4*p+1` is `3 55..5 3` on `m+1` digits. -/
theorem mem_A083831_repdigit8 {m : Nat} (hm : 1 <= m) :
    IsMember 4 (repdigit 8 m) :=
  Exists.intro m (Exists.intro (m + 1)
    (And.intro hm
      (And.intro
        (isPal_repdigit (by norm_num) (by norm_num) hm)
        (isPal_four_mul_repdigit8 hm))))

/-- `k = 5`, OEIS A083833: every repdigit `22..2` is a member;
its image `5*p+1` is the repunit `R_{m+1}`. -/
theorem mem_A083833_repdigit2 {m : Nat} (hm : 1 <= m) :
    IsMember 5 (repdigit 2 m) :=
  Exists.intro m (Exists.intro (m + 1)
    (And.intro hm
      (And.intro
        (isPal_repdigit (by norm_num) (by norm_num) hm)
        (by rw [five_mul_repdigit2]
            exact isPal_repunit (by omega)))))

/-! ## Unified packaging -/

/-- The repdigit digit attached to multiplier `k`: the unique
`d` making `k*d + 1` a two-digit repdigit `11*v` (solutions
`(k,d,v)`: `(2,5,1)`, `(3,7,2)`, `(4,8,3)`, `(5,2,1)`).
Default value `2` is only reached through `k = 5` below. -/
def repdDigit (k : Nat) : Nat :=
  if k = 2 then 5 else if k = 3 then 7 else if k = 4 then 8 else 2

/-- All four converses in one statement: the `k`-repdigit of
any length `m >= 1` is a member of `S_k` with overflow image. -/
theorem repdigit_mem {k m : Nat}
    (hk : k = 2 \/ k = 3 \/ k = 4 \/ k = 5) (hm : 1 <= m) :
    IsMember k (repdigit (repdDigit k) m) := by
  rcases hk with rfl | rfl | rfl | rfl
  case inl => simpa [repdDigit] using mem_A069881_repdigit5 hm
  case inr.inl => simpa [repdDigit] using mem_A083829_repdigit7 hm
  case inr.inr.inl =>
    simpa [repdDigit] using mem_A083831_repdigit8 hm
  case inr.inr.inr =>
    simpa [repdDigit] using mem_A083833_repdigit2 hm

/-!
## Connection with the artifacts (comment only, NOT formalized)

Combined with the certified theorems, the converses above give
the full iff for the repdigit branch (to be stated inside each
artifact's namespace, e.g. `open A069881`):

* `A069881`: `IsPal p m /\ IsPal (2*p+1) m' /\ m even` iff
  `p = repdigit 5 m` (forward: `A069881_even` gives the digits,
  closed form `p = 5*R_m`; backward: `mem_A069881_repdigit5`).
* `A083829`: same iff with `d = 7` (`A083829_even`,
  `succ_case_all7`); image `2 3^{m-1} 2`.
* `A083831`: same iff with `d = 8` (`A083831_even`,
  `succ_case_all8`); image `3 5^{m-1} 3`.
* `A083833`: same iff with `d = 2` (`A083833_C2`,
  `succ_case_all2`); image repunit `R_{m+1}`.

Also NOT formalized anywhere (beyond this draft's scope): the
converse for the same-length branch. The alternating digit
classes of the shared lemma are necessary conditions on members,
not known to be sufficient; no claim is made there.
-/

/-! ## Canonical unification: artifact-native Iff

The four artifacts ship separately namespaced but fieldwise
identical `dgt`/`IsPal`. The bridges below transport our verified
`Kp1Repdigits.IsPal` facts to each artifact's `IsPal` by
definitional equality (`rfl`-level: same term
`n / 10^j % 10` on both sides). Combined with each artifact's own
`succ_case_allN` (forward direction) this yields a LITERAL
`Iff` on the overflow branch `m' = m + 1`, stated and checked
entirely in the artifact vocabulary. -/

-- Definitional-identity probes (compile iff the two `dgt`s and
-- `IsPal` field types are defeq).
example (n j : ℕ) : A069881.dgt n j = dgt n j := rfl
example (n j : ℕ) : A083829.dgt n j = dgt n j := rfl
example (n j : ℕ) : A083831.dgt n j = dgt n j := rfl
example (n j : ℕ) : A083833.dgt n j = dgt n j := rfl

/-- Bridge to `A069881.IsPal` (the artifact structure is fieldwise
defeq to ours). -/
theorem isPal_to_A069881 {p m : ℕ} (h : IsPal p m) :
    A069881.IsPal p m := by
  refine ⟨fun j hj => ?_, h.lo, h.hi⟩
  exact h.sym j hj

/-- Bridge to `A083829.IsPal`. -/
theorem isPal_to_A083829 {p m : ℕ} (h : IsPal p m) :
    A083829.IsPal p m := by
  refine ⟨fun j hj => ?_, h.lo, h.hi⟩
  exact h.sym j hj

/-- Bridge to `A083831.IsPal`. -/
theorem isPal_to_A083831 {p m : ℕ} (h : IsPal p m) :
    A083831.IsPal p m := by
  refine ⟨fun j hj => ?_, h.lo, h.hi⟩
  exact h.sym j hj

/-- Bridge to `A083833.IsPal`. -/
theorem isPal_to_A083833 {p m : ℕ} (h : IsPal p m) :
    A083833.IsPal p m := by
  refine ⟨fun j hj => ?_, h.lo, h.hi⟩
  exact h.sym j hj

/-- Digit shift under division by 10: the `j`-th digit of
`p / 10` is the `(j+1)`-th digit of `p`. -/
theorem dgt_div10 (p j : ℕ) : dgt (p / 10) j = dgt p (j + 1) := by
  unfold dgt
  rw [Nat.div_div_eq_div_mul, mul_comm (10 : ℕ) (10 ^ j),
    ← pow_succ]

/-- A number below `10^m` equals the sum of its `m` low digits:
`p = sum_{j<m} dgt p j * 10^j`. This is the reconstruction lemma
turning "all digits equal `d`" into "p is the `d`-repdigit". -/
theorem eq_sum_dgt {p m : ℕ} (h : p < 10 ^ m) :
    p = Finset.sum (Finset.range m) (fun j => dgt p j * 10 ^ j) := by
  induction m generalizing p with
  | zero =>
    rw [Nat.lt_one_iff.mp h]
    simp
  | succ m ih =>
    have h' : p < 10 ^ m * 10 := by rwa [pow_succ] at h
    have hdiv : p / 10 < 10 ^ m :=
      (Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 10)).mpr h'
    have ih' := ih hdiv
    have hterm : ∀ j ∈ Finset.range m,
        dgt p (j + 1) * 10 ^ (j + 1) =
          10 * (dgt (p / 10) j * 10 ^ j) := by
      intro j _
      rw [pow_succ, ← dgt_div10]
      ring
    have hsum : Finset.sum (Finset.range m)
        (fun j => dgt p (j + 1) * 10 ^ (j + 1)) = 10 * (p / 10) := by
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← ih']
    have hd0 : dgt p 0 * 10 ^ 0 = p % 10 := by
      unfold dgt
      rw [pow_zero, Nat.div_one, mul_one]
    simp only [Finset.sum_range_succ']
    rw [hd0, hsum]
    omega

/-! ### The iff per artifact (overflow branch `m' = m + 1`) -/

/-- `k = 2` (OEIS A069881): a palindrome `p` whose double-plus-one
has one more digit is EXACTLY the `5`-repdigit. Literal `Iff`
against `A069881.IsPal`. -/
theorem repdigit5_iff_overflow_A069881 {p m : ℕ} (hm : 1 ≤ m) :
    (A069881.IsPal p m ∧ A069881.IsPal (2 * p + 1) (m + 1)) ↔
      p = repdigit 5 m := by
  constructor
  · rintro ⟨hp, hq⟩
    have hd : ∀ j < m, dgt p j = 5 := fun j hj =>
      A069881.succ_case_all5 hp hq hm j hj
    have hsum : p = Finset.sum (Finset.range m)
        (fun j => (5 : ℕ) * 10 ^ j) := by
      rw [eq_sum_dgt hp.hi]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      show dgt p j * 10 ^ j = 5 * 10 ^ j
      rw [hd j hj]
    exact hsum.trans (repdigit_eq_sum 5 m).symm
  · intro h
    subst h
    exact ⟨isPal_to_A069881
        (isPal_repdigit (by norm_num) (by norm_num) hm),
      by rw [two_mul_repdigit5]
         exact isPal_to_A069881 (isPal_repunit (by omega))⟩

/-- `k = 3` (OEIS A083829): the `7`-repdigit iff. -/
theorem repdigit7_iff_overflow_A083829 {p m : ℕ} (hm : 1 ≤ m) :
    (A083829.IsPal p m ∧ A083829.IsPal (3 * p + 1) (m + 1)) ↔
      p = repdigit 7 m := by
  constructor
  · rintro ⟨hp, hq⟩
    have hd : ∀ j < m, dgt p j = 7 := fun j hj =>
      A083829.succ_case_all7 hp hq hm j hj
    have hsum : p = Finset.sum (Finset.range m)
        (fun j => (7 : ℕ) * 10 ^ j) := by
      rw [eq_sum_dgt hp.hi]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      show dgt p j * 10 ^ j = 7 * 10 ^ j
      rw [hd j hj]
    exact hsum.trans (repdigit_eq_sum 7 m).symm
  · intro h
    subst h
    exact ⟨isPal_to_A083829
        (isPal_repdigit (by norm_num) (by norm_num) hm),
      isPal_to_A083829 (isPal_three_mul_repdigit7 hm)⟩

/-- `k = 4` (OEIS A083831): the `8`-repdigit iff. -/
theorem repdigit8_iff_overflow_A083831 {p m : ℕ} (hm : 1 ≤ m) :
    (A083831.IsPal p m ∧ A083831.IsPal (4 * p + 1) (m + 1)) ↔
      p = repdigit 8 m := by
  constructor
  · rintro ⟨hp, hq⟩
    have hd : ∀ j < m, dgt p j = 8 := fun j hj =>
      A083831.succ_case_all8 hp hq hm j hj
    have hsum : p = Finset.sum (Finset.range m)
        (fun j => (8 : ℕ) * 10 ^ j) := by
      rw [eq_sum_dgt hp.hi]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      show dgt p j * 10 ^ j = 8 * 10 ^ j
      rw [hd j hj]
    exact hsum.trans (repdigit_eq_sum 8 m).symm
  · intro h
    subst h
    exact ⟨isPal_to_A083831
        (isPal_repdigit (by norm_num) (by norm_num) hm),
      isPal_to_A083831 (isPal_four_mul_repdigit8 hm)⟩

/-- `k = 5` (OEIS A083833): the `2`-repdigit iff. -/
theorem repdigit2_iff_overflow_A083833 {p m : ℕ} (hm : 1 ≤ m) :
    (A083833.IsPal p m ∧ A083833.IsPal (5 * p + 1) (m + 1)) ↔
      p = repdigit 2 m := by
  constructor
  · rintro ⟨hp, hq⟩
    have hd : ∀ j < m, dgt p j = 2 := fun j hj =>
      A083833.succ_case_all2 hp hq hm j hj
    have hsum : p = Finset.sum (Finset.range m)
        (fun j => (2 : ℕ) * 10 ^ j) := by
      rw [eq_sum_dgt hp.hi]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      show dgt p j * 10 ^ j = 2 * 10 ^ j
      rw [hd j hj]
    exact hsum.trans (repdigit_eq_sum 2 m).symm
  · intro h
    subst h
    exact ⟨isPal_to_A083833
        (isPal_repdigit (by norm_num) (by norm_num) hm),
      by rw [five_mul_repdigit2]
         exact isPal_to_A083833 (isPal_repunit (by omega))⟩

/-! ### The headline iff: even-length members are the repdigits

For `m` even every member is forced into the overflow branch by
each artifact's `_even`/`_C2` classification, so membership alone
(no `m' = m + 1` constraint) is already equivalent to being the
repdigit. This is the claim the paper calls
"member of even length <-> repdigit". -/

/-- `k = 2` (A069881): an even-length member is exactly the
`5`-repdigit (forward: `A069881_even`). -/
theorem repdigit5_iff_member_even_A069881 {p m : ℕ}
    (hm : 1 ≤ m) (hme : m % 2 = 0) :
    (∃ m', A069881.IsPal p m ∧ A069881.IsPal (2 * p + 1) m') ↔
      p = repdigit 5 m := by
  constructor
  · rintro ⟨m', hp, hq⟩
    have hd : ∀ j < m, dgt p j = 5 := fun j hj =>
      A069881.A069881_even hp hq hm hme j hj
    have hsum : p = Finset.sum (Finset.range m)
        (fun j => (5 : ℕ) * 10 ^ j) := by
      rw [eq_sum_dgt hp.hi]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      show dgt p j * 10 ^ j = 5 * 10 ^ j
      rw [hd j hj]
    exact hsum.trans (repdigit_eq_sum 5 m).symm
  · intro h
    subst h
    exact ⟨m + 1, (repdigit5_iff_overflow_A069881 (p := repdigit 5 m) hm).mpr rfl⟩

/-- `k = 3` (A083829, conjecture P1): an even-length member is
exactly the `7`-repdigit (forward: `A083829_even`). -/
theorem repdigit7_iff_member_even_A083829 {p m : ℕ}
    (hm : 1 ≤ m) (hme : m % 2 = 0) :
    (∃ m', A083829.IsPal p m ∧ A083829.IsPal (3 * p + 1) m') ↔
      p = repdigit 7 m := by
  constructor
  · rintro ⟨m', hp, hq⟩
    have hd : ∀ j < m, dgt p j = 7 := fun j hj =>
      A083829.A083829_even hp hq hm hme j hj
    have hsum : p = Finset.sum (Finset.range m)
        (fun j => (7 : ℕ) * 10 ^ j) := by
      rw [eq_sum_dgt hp.hi]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      show dgt p j * 10 ^ j = 7 * 10 ^ j
      rw [hd j hj]
    exact hsum.trans (repdigit_eq_sum 7 m).symm
  · intro h
    subst h
    exact ⟨m + 1, (repdigit7_iff_overflow_A083829 (p := repdigit 7 m) hm).mpr rfl⟩

/-- `k = 4` (A083831): an even-length member is exactly the
`8`-repdigit (forward: `A083831_even`). -/
theorem repdigit8_iff_member_even_A083831 {p m : ℕ}
    (hm : 1 ≤ m) (hme : m % 2 = 0) :
    (∃ m', A083831.IsPal p m ∧ A083831.IsPal (4 * p + 1) m') ↔
      p = repdigit 8 m := by
  constructor
  · rintro ⟨m', hp, hq⟩
    have hd : ∀ j < m, dgt p j = 8 := fun j hj =>
      A083831.A083831_even hp hq hm hme j hj
    have hsum : p = Finset.sum (Finset.range m)
        (fun j => (8 : ℕ) * 10 ^ j) := by
      rw [eq_sum_dgt hp.hi]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      show dgt p j * 10 ^ j = 8 * 10 ^ j
      rw [hd j hj]
    exact hsum.trans (repdigit_eq_sum 8 m).symm
  · intro h
    subst h
    exact ⟨m + 1, (repdigit8_iff_overflow_A083831 (p := repdigit 8 m) hm).mpr rfl⟩

/-- `k = 5` (A083833, conjecture C2): an even-length member is
exactly the `2`-repdigit (forward: `A083833_C2`). -/
theorem repdigit2_iff_member_even_A083833 {p m : ℕ}
    (hm : 1 ≤ m) (hme : m % 2 = 0) :
    (∃ m', A083833.IsPal p m ∧ A083833.IsPal (5 * p + 1) m') ↔
      p = repdigit 2 m := by
  constructor
  · rintro ⟨m', hp, hq⟩
    have hd : ∀ j < m, dgt p j = 2 := fun j hj =>
      A083833.A083833_C2 hp hq hm hme j hj
    have hsum : p = Finset.sum (Finset.range m)
        (fun j => (2 : ℕ) * 10 ^ j) := by
      rw [eq_sum_dgt hp.hi]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      show dgt p j * 10 ^ j = 2 * 10 ^ j
      rw [hd j hj]
    exact hsum.trans (repdigit_eq_sum 2 m).symm
  · intro h
    subst h
    exact ⟨m + 1, (repdigit2_iff_overflow_A083833 (p := repdigit 2 m) hm).mpr rfl⟩

/-! ### Canonical membership (sufficient direction) -/

/-- `repdigit 5 m` is an A069881 member, in the artifact's own
vocabulary (`A069881.IsPal` on both slots). -/
theorem repdigit5_mem_A069881 {m : ℕ} (hm : 1 ≤ m) :
    ∃ m', A069881.IsPal (repdigit 5 m) m ∧
      A069881.IsPal (2 * repdigit 5 m + 1) m' :=
  ⟨m + 1,
    (repdigit5_iff_overflow_A069881 (p := repdigit 5 m) hm).mpr rfl⟩

/-- `repdigit 7 m` is an A083829 member. -/
theorem repdigit7_mem_A083829 {m : ℕ} (hm : 1 ≤ m) :
    ∃ m', A083829.IsPal (repdigit 7 m) m ∧
      A083829.IsPal (3 * repdigit 7 m + 1) m' :=
  ⟨m + 1,
    (repdigit7_iff_overflow_A083829 (p := repdigit 7 m) hm).mpr rfl⟩

/-- `repdigit 8 m` is an A083831 member. -/
theorem repdigit8_mem_A083831 {m : ℕ} (hm : 1 ≤ m) :
    ∃ m', A083831.IsPal (repdigit 8 m) m ∧
      A083831.IsPal (4 * repdigit 8 m + 1) m' :=
  ⟨m + 1,
    (repdigit8_iff_overflow_A083831 (p := repdigit 8 m) hm).mpr rfl⟩

/-- `repdigit 2 m` is an A083833 member. -/
theorem repdigit2_mem_A083833 {m : ℕ} (hm : 1 ≤ m) :
    ∃ m', A083833.IsPal (repdigit 2 m) m ∧
      A083833.IsPal (5 * repdigit 2 m + 1) m' :=
  ⟨m + 1,
    (repdigit2_iff_overflow_A083833 (p := repdigit 2 m) hm).mpr rfl⟩

#print axioms repdigit_mem
#print axioms repdigit5_iff_overflow_A069881
#print axioms repdigit7_iff_overflow_A083829
#print axioms repdigit8_iff_overflow_A083831
#print axioms repdigit2_iff_overflow_A083833
#print axioms repdigit5_iff_member_even_A069881
#print axioms repdigit7_iff_member_even_A083829
#print axioms repdigit8_iff_member_even_A083831
#print axioms repdigit2_iff_member_even_A083833

end Kp1Repdigits
