import A083832
import Spec_A083832
import Check_Spec_A083832
import Check_AntiVacuite_A083832
import A083831

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AxiomsReport_A083832 : couverture exhaustive des axiomes

Perimetre cible A083832 (5 modules) : `A083832` +
`Spec_A083832` + `Check_Spec_A083832` +
`Check_AntiVacuite_A083832` + cloture transitive
projet (`A083832 -> A083831` ; `Spec_A083832`
importe `A083831` directement).
40 declarations auditees ci-dessous.
Attendu partout : [propext, Classical.choice, Quot.sound].
-/

-- A083832 (1 decl)
#print axioms A083832_alphabet

-- Spec_A083832 (1 decl)
#print axioms SpecA083832

-- Check_Spec_A083832 (1 decl)
#print axioms proven_A083832

-- Check_AntiVacuite_A083832 (9 decls, namespace CheckAntiVacA083832)
#print axioms CheckAntiVacA083832.sat_conjunction
#print axioms CheckAntiVacA083832.sat_succ_branch
#print axioms CheckAntiVacA083832.sat_same_branch
#print axioms CheckAntiVacA083832.sat_m_one
#print axioms CheckAntiVacA083832.sat_via_theorem
#print axioms CheckAntiVacA083832.ablation_needs_ppal
#print axioms CheckAntiVacA083832.ablation_needs_qpal
#print axioms CheckAntiVacA083832.ablation_m_guard
#print axioms CheckAntiVacA083832.ablation_alpha_tight

-- A083831 (28 decls, namespace A083831)
#print axioms A083831.dgt
#print axioms A083831.IsPal
#print axioms A083831.crry
#print axioms A083831.crry_zero
#print axioms A083831.crry_le
#print axioms A083831.decomp
#print axioms A083831.div_ten_pow
#print axioms A083831.qdgt
#print axioms A083831.crry_succ
#print axioms A083831.dgt_eq_zero_of_ge
#print axioms A083831.mp_cases
#print axioms A083831.crry_m_eq_zero_iff
#print axioms A083831.crry_sym_same
#print axioms A083831.crry_mirror
#print axioms A083831.qdgt_sym_succ
#print axioms A083831.top_two_eq
#print axioms A083831.carry_period_same
#print axioms A083831.carry_even_same
#print axioms A083831.carry_odd_same
#print axioms A083831.same_case_odd_a0
#print axioms A083831.same_case_digits
#print axioms A083831.succ_case_chain
#print axioms A083831.succ_case_all8
#print axioms A083831.A083831_even
#print axioms A083831.A083831_digits
#print axioms A083831.same_case_c1
#print axioms A083831.succ_case_carry
#print axioms A083831.A083832_digits
