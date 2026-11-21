import Spec_A083833
import A083833

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A083833 : fermeture Spec↔preuve (Option B)

Le Spec (`Spec_A083833.lean`) ne contient aucune preuve ; ce
fichier vérifie que les théorèmes compilés satisfont EXACTEMENT
les deux énoncés de la spec, dans l'ordre de la conjonction
(C1, C2). Les théorèmes vivent dans le namespace `A083833` du
module homonyme.
-/

/-- Les preuves compilées satisfont les énoncés record C1-C2. -/
theorem proven_A083833 : SpecA083833 :=
  ⟨A083833.A083833_C1, A083833.A083833_C2⟩

#print axioms proven_A083833
