import .pair
import .precofibration_category

noncomputable theory

namespace homotopy_theory.topological_spaces
open homotopy_theory.cylinder

-- (Provisional?) inductive definition of the disk/sphere pair using cubes.
def unit_pair : pair := pair.mk (*) ∅
def disk_sphere_pair (n : ℕ) : pair := nat.rec unit_pair (λ _ P, pair.prod P I_01) n

def disk (n : ℕ) : Top := (disk_sphere_pair n).space
def sphere_minus_one (n : ℕ) : Top := (disk_sphere_pair n).subspace
notation `D[` n `]` := disk n
notation `S[` n `-1]` := sphere_minus_one n
def sphere_disk_incl (n : ℕ) : S[n-1] ⟶ D[n] := pair.incl _

-- It's a cofibration.
lemma sphere_disk_closed : ∀ n, is_closed (disk_sphere_pair n).subset
| 0 := is_closed_empty
| (n+1) := pair.prod.is_closed (sphere_disk_closed n) I_01.is_closed

lemma sphere_disk_cofibered : ∀ n, (disk_sphere_pair n).cofibered
| 0 := pair.empty_cofibered _
| (n+1) := prod_I_01_cofibered _ (sphere_disk_closed n) (sphere_disk_cofibered n)

lemma sphere_disk_cofibration (n : ℕ) : closed_cofibration (sphere_disk_incl n) :=
closed_cofibration_incl_iff.mpr ⟨sphere_disk_cofibered n, sphere_disk_closed n⟩

end homotopy_theory.topological_spaces
