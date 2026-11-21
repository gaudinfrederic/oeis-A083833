import A083833
import A083837
import A083838
import Spec_A083837
import Check_Spec_A083837
import Check_AntiVacuite_A083837
import Spec_A083838
import Check_Spec_A083838

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AxiomsReport_A083837 - audit des axiomes du paquet A083837/A083838

`#print axioms` sur les déclarations clés : whitelist attendue
`[propext, Classical.choice, Quot.sound]` (ou moins), aucun `sorryAx`,
aucun axiome `native_decide`.
-/

open A083833

-- machine générique
#print axioms A083837.revW
#print axioms A083837.okP
#print axioms A083837.escapesIn
#print axioms A083837.lowW
#print axioms A083837.low_rev
#print axioms A083837.dgt_sum_low
#print axioms A083837.revW_invol
#print axioms A083837.revW_mod
#print axioms A083837.prefix_range
#print axioms A083837.prefix_ext
#print axioms A083837.prefix_escapes
#print axioms A083837.zero_of_escapes

-- théorèmes par k (profondeurs 1, 2, 3)
#print axioms A083837.no_wit_12
#print axioms A083837.no_wit_17
#print axioms A083837.no_wit_23
#print axioms A083837.no_wit_31
#print axioms A083837.no_wit_37
#print axioms A083837.no_wit_41
#print axioms A083837.no_wit_42
#print axioms A083837.no_wit_48
#print axioms A083837.no_wit_51
#print axioms A083837.no_wit_53
#print axioms A083837.no_wit_61
#print axioms A083837.no_wit_64
#print axioms A083837.no_wit_71
#print axioms A083837.no_wit_74
#print axioms A083837.no_wit_79
#print axioms A083837.no_wit_81
#print axioms A083837.no_wit_86
#print axioms A083837.no_wit_91
#print axioms A083837.no_wit_96
#print axioms A083837.no_wit_101
#print axioms A083837.no_wit_103

-- capstones A083837
#print axioms A083837.A083837_12_zero
#print axioms A083837.A083837_17_zero
#print axioms A083837.A083837_23_zero
#print axioms A083837.A083837_48_zero
#print axioms A083837.A083837_74_zero
#print axioms A083837.A083837_79_zero
#print axioms A083837.A083837_101_zero
#print axioms A083837.A083837_103_zero

-- capstones A083838 (échantillon)
#print axioms A083838.A083838_12_zero
#print axioms A083838.A083838_48_zero
#print axioms A083838.A083838_79_zero
#print axioms A083838.A083838_101_zero

-- fermetures Spec
#print axioms proven_A083837
#print axioms proven_A083838
