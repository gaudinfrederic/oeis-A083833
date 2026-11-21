import A083831
import Spec_A083831
import Check_Spec_A083831
import Check_AntiVacuite_A083831

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AxiomsReport_A083831 : couverture exhaustive des axiomes

Perimetre cible A083831 (4 modules) : le module
principal `A083831` (auto-contenu, `import Mathlib`) +
`Spec_A083831` + `Check_Spec_A083831` +
`Check_AntiVacuite_A083831`. Le module `A083831`
declare aussi le theoreme compagnon `A083832_digits`
(cible A083832).
35 declarations auditees ci-dessous.
Attendu partout : [propext, Classical.choice, Quot.sound].
-/

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

-- Spec_A083831 (1 decl)
#print axioms SpecA083831

-- Check_Spec_A083831 (1 decl)
#print axioms proven_A083831

-- Check_AntiVacuite_A083831 (5 decls, namespace CheckAntiVacA083831)
#print axioms CheckAntiVacA083831.sat_even_branch
#print axioms CheckAntiVacA083831.sat_odd_branch
#print axioms CheckAntiVacA083831.ablation_even_needs_parity
#print axioms CheckAntiVacA083831.ablation_digits_needs8
#print axioms CheckAntiVacA083831.ablation_digits_tight
