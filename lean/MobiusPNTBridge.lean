import MobiusPNT
import MobiusHarmonic

/-! Discharge the qualitative PNT premise of the harmonic smoothing lemmas.
The general shifted profile, coprimality average and Feng asymptotics remain
separate obligations; these theorems do not count zeros. -/
noncomputable section
open Filter Topology
namespace XiPrime8845.MobiusPNTBridge
open MobiusHarmonic

theorem mobiusMass_tendsto : Tendsto mobiusMass atTop (nhds 0) :=
  mass_tendsto_of_mu_pnt_alt MobiusPNT.mu_pnt_alt

theorem logMean_tendsto : Tendsto logMean atTop (nhds 1) :=
  logMean_tendsto_of_mass mobiusMass_tendsto

/-- Uniform away from u=0, with no external PNT hypothesis. -/
theorem linearProfile_uniform (u0 : ℝ) (hu0 : 0 < u0) :
    TendstoUniformlyOn (fun L u => L * linearProfile L u) (fun _ => 1)
      atTop (Set.Ici u0) :=
  linearProfile_uniform_of_mass u0 hu0 mobiusMass_tendsto

#print axioms mobiusMass_tendsto
#print axioms logMean_tendsto
#print axioms linearProfile_uniform
end XiPrime8845.MobiusPNTBridge
