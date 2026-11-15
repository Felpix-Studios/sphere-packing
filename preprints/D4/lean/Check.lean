import D4Bound

/-! Run with `lake env lean Check.lean` after `lake build`. Every theorem below must depend only
on `propext`, `Classical.choice`, `Quot.sound` and, where a finite check uses
`native_decide`, the compiler-trust axioms that tactic adds. -/

-- Print the complete type as well: an allowed axiom list does not discharge
-- explicit theorem premises. This makes the formalization boundary visible.
#print D4Bound.d4_density_bound_concrete

#print axioms D4Bound.d4_density_bound
#print axioms D4Bound.d4_density_bound_concrete
#print axioms D4Bound.d4_patch_bound
#print axioms D4Bound.energy_floor
#print axioms D4Bound.tripleSum_Kalloc
#print axioms D4Bound.far_pair_nbhd
#print axioms D4Bound.far_pair_sum_max
#print axioms D4Bound.quartic_offdiag_ge
#print axioms D4Bound.finite_local_energy
#print axioms D4Bound.groups_ge
#print axioms D4Bound.final_arith
#print axioms D4Bound.transfer
#print axioms D4Bound.transfer_quarter
#print axioms D4Bound.coeff_identity
#print axioms D4Bound.G_zero
#print axioms D4Bound.G_pos
#print axioms D4Bound.F_neg
#print axioms D4Bound.f_nonpos
#print axioms D4Bound.f_integrable
#print axioms D4Bound.fourier_integrable
#print axioms D4Bound.integral_f
#print axioms D4Bound.fourierIdentity
#print axioms D4Bound.fourier_polyGauss
#print axioms D4Bound.shell_inner_le
#print axioms D4Bound.two_shell_inner_le
#print axioms D4Bound.annulus_inner_le
#print axioms D4Bound.card_le_of_cos_le
#print axioms D4Bound.broad_degree_le
#print axioms D4Bound.broad_vertices_le
#print axioms D4Bound.broadEdges_le
#print axioms D4Bound.graphSlack_of
#print axioms D4Bound.lat_key
#print axioms D4Bound.latitude_count
#print axioms D4Bound.countWithin_le_of_code
#print axioms D4Bound.countDomain_of_admissible
#print axioms D4Bound.groupKeys_nodup
#print axioms D4Bound.groupKeys_complete
#print axioms D4Bound.group_mem

#print axioms D4Bound.schoenberg_S3
#print axioms D4Bound.Components.gram_energy_nonneg
#print axioms D4Bound.Components.origin_credit_identity
#print axioms D4Bound.Components.gram_origin_credit
#print axioms D4Bound.Components.gram_energy_ge_credit
#print axioms D4Bound.Components.usage_energy_eq
#print axioms D4Bound.Components.usage_energy_nonneg
#print axioms D4Bound.Components.gauge_energy_eq
#print axioms D4Bound.Components.gauge_pair_term
#print axioms D4Bound.Components.pair_count_gauge_nonneg
#print axioms D4Bound.Components.card_le_of_ball
#print axioms D4Bound.Components.blichfeldt_translate
#print axioms D4Bound.Components.pstar_capacity
#print axioms D4Bound.Components.step_capacity
#print axioms D4Bound.Components.pstar_allocation_nonneg
#print axioms D4Bound.Components.step_allocation_nonneg

#print axioms D4Bound.annular_151_proved

#print axioms D4Bound.LatitudeCheck.latitude15
#print axioms D4Bound.LatitudeCheck.latitude24

#print axioms D4Bound.schoenberg_S2
#print axioms D4Bound.projected_eight_proved
#print axioms D4Bound.proj_scalar_exact
#print axioms D4Bound.broadEdges_le_projected
#print axioms D4Bound.graphSlack_proved

/-! All-theorems audit. Every theorem named `D4Bound.*` in the environment may depend
only on `propext`, `Classical.choice`, `Quot.sound` and the per-use axioms that
`native_decide` adds. The command fails on anything else (for example `sorryAx` or a
declared axiom) and prints the number of theorems and the native axioms it found. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut theorems : Nat := 0
  let mut native : NameSet := {}
  let mut bad : NameSet := {}
  for (name, info) in env.constants.toList do
    if (`D4Bound).isPrefixOf name then
      if let .thmInfo _ := info then
        theorems := theorems + 1
        for ax in (← Lean.collectAxioms name) do
          if standard.contains ax then continue
          if (ax.toString.splitOn "._native.native_decide.ax_").length == 2 then
            native := native.insert ax
          else bad := bad.insert ax
  if bad.isEmpty then
    logInfo m!"D4_ALL_THEOREMS_AXIOM_AUDIT_PASS {theorems} NATIVE_AXIOMS {native.size} {native.toList}"
  else
    throwError "unapproved axioms: {bad.toList}"
